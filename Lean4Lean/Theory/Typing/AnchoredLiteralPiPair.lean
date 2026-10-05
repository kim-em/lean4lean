import Lean4Lean.Theory.Typing.AnchoredLiteralPi

/-! Binary literal Pi introduction retains all finite row capabilities.
The future-world constructor only forwards the given lower-rank evidence. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  {Γ : List VExpr} {A A' B B' prototypeDomain prototypeBody : VExpr}
  {domain : Profile n} {rows : List (Key n × Profile n)}

def PiWitness.literalPair
    (hΓ : OnCtx Γ (env.IsType U))
    (hA : env.IsType U Γ A) (hA' : env.IsType U Γ A')
    (hB : env.IsType U (A :: Γ) B) (hB' : env.IsType U (A' :: Γ) B')
    (domains : TypeConversion env U Γ A A')
    (bodies : TypeConversion env U (A :: Γ) B B')
    (prototypeA : TypeConversion env U Γ A prototypeDomain)
    (prototypeB : TypeConversion env U (A :: Γ) B prototypeBody)
    (domainRelated : TypeRelated env U registry Γ A A' domain)
    (rowDomains : ∀ key output, (key, output) ∈ rows →
      ∃ support : Profile n, key.input.HasType support ∧ support.HasType (.sort true) ∧
        support ≤ domain ∧ TypeConversion env U Γ key.domain A ∧
        TypeRelated env U registry Γ key.domain A support)
    (rowBodies : ∀ key output, (key, output) ∈ rows →
      ∀ Δ ρ, FutureInsertion env U Γ Δ ρ → ∀ x y,
      Admitted env U registry Δ (key.rename ρ) x y →
      TypeRelated env U registry Δ ((B.lift' ρ.cons).inst x) ((B.lift' ρ.cons).inst y)
        (output.rename ρ) ∧
      TypeRelated env U registry Δ ((B'.lift' ρ.cons).inst x) ((B'.lift' ρ.cons).inst y)
        (output.rename ρ) ∧
      TypeRelated env U registry Δ ((B.lift' ρ.cons).inst x) ((B'.lift' ρ.cons).inst x)
        (output.rename ρ)) :
    PiWitness env U registry (relations env U registry n) Γ (.forallE A B) (.forallE A' B')
      prototypeDomain prototypeBody domain rows where
  context := Γ
  map := .refl
  leftDomain := A
  rightDomain := A'
  leftBody := B
  rightBody := B'
  leftExposure := .literal hΓ (hA.forallE hB)
  rightExposure := .literal hΓ (hA'.forallE hB')
  leftDomainType := hA
  rightDomainType := hA'
  leftBodyType := hB
  rightBodyType := hB'
  domains := domains
  bodies := bodies
  prototypeDomainPath := by simpa only [lift'_refl] using prototypeA
  prototypeBodyPath := by
    simpa only [lift'_depth_zero (l := Lift.refl.cons) rfl] using prototypeB
  domainRelated := by simpa only [Profile.rename_refl, TypeRelated] using domainRelated
  rowDomains := by
    simpa only [Key.rename_refl, Profile.rename_refl, lift'_refl, TypeRelated] using rowDomains
  rowBodies := by simpa only [Lift.refl_comp, TypeRelated, Admitted] using rowBodies

theorem TypeRelated.literalPiPair
    (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U))
    (hA : env.IsType U Γ A) (hA' : env.IsType U Γ A')
    (hB : env.IsType U (A :: Γ) B) (hB' : env.IsType U (A' :: Γ) B')
    (domains : TypeConversion env U Γ A A')
    (bodies : TypeConversion env U (A :: Γ) B B')
    (prototypeA : TypeConversion env U Γ A prototypeDomain)
    (prototypeB : TypeConversion env U (A :: Γ) B prototypeBody)
    (domainRelated : TypeRelated env U registry Γ A A' domain)
    (rowDomains : ∀ key output, (key, output) ∈ rows →
      ∃ support : Profile n, key.input.HasType support ∧ support.HasType (.sort true) ∧
        support ≤ domain ∧ TypeConversion env U Γ key.domain A ∧
        TypeRelated env U registry Γ key.domain A support)
    (rowBodies : ∀ key output, (key, output) ∈ rows →
      ∀ Δ ρ, FutureInsertion env U Γ Δ ρ → ∀ x y,
      Admitted env U registry Δ (key.rename ρ) x y →
      TypeRelated env U registry Δ ((B.lift' ρ.cons).inst x) ((B.lift' ρ.cons).inst y)
        (output.rename ρ) ∧
      TypeRelated env U registry Δ ((B'.lift' ρ.cons).inst x) ((B'.lift' ρ.cons).inst y)
        (output.rename ρ) ∧
      TypeRelated env U registry Δ ((B.lift' ρ.cons).inst x) ((B'.lift' ρ.cons).inst x)
        (output.rename ρ)) :
    TypeRelated env U registry Γ (.forallE A B) (.forallE A' B')
      (Profile.pi prototypeDomain prototypeBody domain rows) := by
  intro Δ ρ future atom member
  have he := List.mem_singleton.mp member
  subst atom
  refine ⟨PiWitness.literalPair (future.targetWF henv)
    (hA.weak' henv future.weakening) (hA'.weak' henv future.weakening)
    (hB.weak' henv future.weakening.cons) (hB'.weak' henv future.weakening.cons)
    (domains.weak' henv future.weakening) (bodies.weak' henv future.weakening.cons)
    (prototypeA.weak' henv future.weakening) (prototypeB.weak' henv future.weakening.cons)
    (domainRelated.future henv future) ?_ ?_⟩
  · intro key output member
    obtain ⟨⟨originalKey, originalOutput⟩, originalMember, he⟩ := List.mem_map.mp member
    cases he
    obtain ⟨support, typed, formed, bounded, path, related⟩ :=
      rowDomains originalKey originalOutput originalMember
    refine ⟨support.rename ρ, Profile.rename_hasType_iff.mpr typed, ?_, (Profile.rename_le_iff.mpr bounded),
      path.weak' henv future.weakening, related.future henv future⟩
    simpa only [Profile.rename_sort] using (Profile.rename_hasType_iff (ρ := ρ)).mpr formed
  · intro key output member Ω τ next x y admitted
    obtain ⟨⟨originalKey, originalOutput⟩, originalMember, he⟩ := List.mem_map.mp member
    cases he
    have incoming : Admitted env U registry Ω (Key.rename (ρ.comp τ) originalKey) x y := by
      simpa only [Key.rename, Profile.rename, lift'_comp, ← Atom.rename_comp, List.map_map, Function.comp_def] using admitted
    have result := rowBodies originalKey originalOutput originalMember Ω (ρ.comp τ)
      (future.comp next henv) x y incoming
    simpa only [show (ρ.comp τ).cons = ρ.cons.comp τ.cons from rfl,
      lift'_comp, Profile.rename, ← Atom.rename_comp, List.map_map, Function.comp_def] using result

end Lean4Lean.AnchoredSemantics
