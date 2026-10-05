import Lean4Lean.Theory.Typing.AnchoredAdmission

/-! Literal dependent function displays. Their context, renaming and actual
domain and body are retained definitionally, so original lambda-child proofs
can supply their rows without choosing a new private display. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  {Γ : List VExpr} {A B : VExpr} {key : Key n} {domain result : Profile n}

def Exposure.literal (hΓ : OnCtx Γ (env.IsType U))
    (formed : env.IsType U Γ expression) :
    Exposure env U registry Γ expression Γ .refl expression where
  added := []
  result := expression
  postMap := .refl
  trace := .refl
  generated := .refl hΓ
  post := .refl hΓ
  map_eq := rfl
  result_eq := lift'_refl
  sound := by simpa only [lift'_refl] using
    (TypeConversion.refl : TypeConversion env U Γ expression expression)
  headType := formed

private theorem literalPi_trace
    {registry : CanonicalHead.Registry} {A B result : VExpr} {added : List VExpr}
    (h : CanonicalDataHead.Trace registry (.forallE A B) added result) :
    added = [] ∧ result = .forallE A B := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | next step _ => simp only [CanonicalDataHead.step_pi] at step; contradiction

theorem Exposure.literalPi_components
    {Δ : List VExpr} {ρ : Lift} {C D : VExpr}
    (E : Exposure env U registry Γ (.forallE A B) Δ ρ (.forallE C D)) :
    C = A.lift' ρ ∧ D = B.lift' ρ.cons := by
  have ht := literalPi_trace E.trace
  have hm : E.postMap = ρ := by
    simpa only [ht.1, List.length_nil, Lift.skipN, Lift.refl_comp] using E.map_eq
  have he := E.result_eq
  rw [ht.2, hm] at he
  exact ⟨(VExpr.forallE.inj he).1.symm, (VExpr.forallE.inj he).2.symm⟩

def PiWitness.literal (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U))
    (hA : env.IsType U Γ A) (hB : env.IsType U (A :: Γ) B)
    (typed : key.input.HasType domain) (formed : domain.HasType (.sort true))
    (path : TypeConversion env U Γ key.domain A)
    (bridge : TypeRelated env U registry Γ key.domain A domain)
    (row : ∀ Δ ρ, FutureInsertion env U Γ Δ ρ → ∀ x y,
      Admitted env U registry Δ (key.rename ρ) x y →
      TypeRelated env U registry Δ ((B.lift' ρ.cons).inst x)
        ((B.lift' ρ.cons).inst y) (result.rename ρ)) :
    PiWitness env U registry (relations env U registry n)
      Γ (.forallE A B) (.forallE A B) A B domain [(key, result)] where
  context := Γ
  map := .refl
  leftDomain := A
  rightDomain := A
  leftBody := B
  rightBody := B
  leftExposure := .literal hΓ (hA.forallE hB)
  rightExposure := .literal hΓ (hA.forallE hB)
  leftDomainType := hA
  rightDomainType := hA
  leftBodyType := hB
  rightBodyType := hB
  domains := .refl
  bodies := .refl
  prototypeDomainPath := by simpa only [lift'_refl] using
    (TypeConversion.refl : TypeConversion env U Γ A A)
  prototypeBodyPath := by
    rw [lift'_depth_zero (l := Lift.refl.cons) rfl]
    exact .refl
  domainRelated := by
    simpa only [Profile.rename_refl, TypeRelated] using
      (bridge.symm henv typed.wf_type).left_diagonal
  rowDomains := by
    intro k r hm
    cases List.mem_singleton.mp hm
    simpa only [Key.rename_refl, Profile.rename_refl, lift'_refl, TypeRelated] using
      (show ∃ support : Profile n, key.input.HasType support ∧
        support.HasType (.sort true) ∧ support ≤ domain ∧
        TypeConversion env U Γ key.domain A ∧
        TypeRelated env U registry Γ key.domain A support from
        ⟨domain, typed, formed, Profile.le_refl _, path, bridge⟩)
  rowBodies := by
    intro k r hm Δ ρ future x y admitted
    cases List.mem_singleton.mp hm
    simp only [Lift.refl_comp] at admitted ⊢
    have pair := row Δ ρ future x y admitted
    exact ⟨pair, pair, pair.left_diagonal⟩

theorem TypeRelated.literalPi (henv : env.Ordered)
    (hA : env.IsType U Γ A) (hB : env.IsType U (A :: Γ) B)
    (typed : key.input.HasType domain) (formed : domain.HasType (.sort true))
    (path : TypeConversion env U Γ key.domain A)
    (bridge : TypeRelated env U registry Γ key.domain A domain)
    (row : ∀ Δ ρ, FutureInsertion env U Γ Δ ρ → ∀ x y,
      Admitted env U registry Δ (key.rename ρ) x y →
      TypeRelated env U registry Δ ((B.lift' ρ.cons).inst x)
        ((B.lift' ρ.cons).inst y) (result.rename ρ)) :
    TypeRelated env U registry Γ (.forallE A B) (.forallE A B)
      (.pi A B domain [(key, result)]) := by
  intro Δ ρ future atom member
  have atom_eq : atom = AtomData.pi (A.lift' ρ) (B.lift' ρ.cons)
      (domain.rename ρ) [(key.rename ρ, result.rename ρ)] := by
    exact List.mem_singleton.mp member
  subst atom
  refine ⟨PiWitness.literal henv (future.targetWF henv)
    (hA.weak' henv future.weakening) (hB.weak' henv (.cons future.weakening))
    (Profile.rename_hasType_iff.mpr typed) ?_
    (path.weak' henv future.weakening) (bridge.future henv future) ?_⟩
  · simpa only [Profile.rename_sort] using
      (Profile.rename_hasType_iff (ρ := ρ)).mpr formed
  · intro Ω τ next x y admitted
    have admitted' : Admitted env U registry Ω (key.rename (ρ.comp τ)) x y := by
      simpa only [Key.rename_comp] using admitted
    simpa only [show (ρ.comp τ).cons = ρ.cons.comp τ.cons from rfl,
      lift'_comp, Profile.rename_comp] using row Ω (ρ.comp τ)
      (future.comp next henv) x y admitted'

end Lean4Lean.AnchoredSemantics
