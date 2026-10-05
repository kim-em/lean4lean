import Lean4Lean.Theory.Typing.AnchoredFunctionTraceExpansion
import Lean4Lean.Theory.Typing.AnchoredBeta
import Lean4Lean.Theory.Typing.AnchoredRecordTrace
import Lean4Lean.Theory.Typing.AnchoredDataAbsorption

/-! Closed paired native trace expansion. Each side is an actual successful
trace through the same inhabited front or a literal lifted base endpoint.
Function applications recurse strictly on finite observation rank, retaining
the caller's actual Pi display through the closed proof-copy contraction.
-/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
open private sort_cover pi_cover family_cover TypeRelated.sort_member_path from Lean4Lean.Theory.Typing.AnchoredBeta
set_option backward.isDefEq.respectTransparency false

private theorem sortCode
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {left right type : VExpr} {support : Profile (n + 1)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (H : Related env U registry Γ left right type (Profile.sort relevant) support) :
    TypeRelated env U registry Γ left right (Profile.sort (n := n + 1) relevant) := by
  exact H.code_of_sortable henv hscoped hΓ (Profile.HasType.sort relevant)

private theorem piCode
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {left right type A B : VExpr}
    {domain : Profile n} {rows : List (Key n × Profile n)} {support : Profile (n + 1)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (H : Related env U registry Γ left right type (Profile.pi A B domain rows) support) :
    TypeRelated env U registry Γ left right (Profile.pi A B domain rows) := by
  have hs := H (.pi A B domain rows) (List.mem_singleton_self _) Γ .refl (.refl hΓ)
  simp only [Profile.rename_refl, lift'_refl] at hs
  rcases hs with empty | ⟨Δ, ρ, insertion, _, _, values⟩
  · cases empty
  have code := values (.pi (A.lift' ρ) (B.lift' ρ.cons)
      (domain.rename ρ) (Rows.rename ρ rows)) (List.mem_singleton_self _)
  change TypeRelated env U registry Δ (left.lift' ρ) (right.lift' ρ)
    (Profile.pi (A.lift' ρ) (B.lift' ρ.cons) (domain.rename ρ) (Rows.rename ρ rows)) at code
  apply TypeRelated.absorb henv hscoped insertion
  have profileEq : (Profile.pi A B domain rows).rename ρ =
      Profile.pi (A.lift' ρ) (B.lift' ρ.cons) (domain.rename ρ) (Rows.rename ρ rows) := by
    rw [Profile.pi, Profile.rename_singleton, Atom.rename_pi]
    rfl
  rw [profileEq]
  exact code

private theorem familyCode
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {left right type : VExpr}
    {demand : FamilyData (Profile n)} {support : Profile (n + 1)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (H : Related env U registry Γ left right type
      (Profile.singleton (n := n + 1) (.family demand)) support) :
    TypeRelated env U registry Γ left right
      (Profile.singleton (n := n + 1) (.family demand)) := by
  have hs := H _ (List.mem_singleton_self _) Γ .refl (.refl hΓ)
  simp only [Profile.rename_refl, lift'_refl] at hs
  rcases hs with empty | ⟨Δ, ρ, insertion, _, _, values⟩
  · cases empty
  apply TypeRelated.absorb henv hscoped insertion
  exact values _ (List.mem_singleton_self _)

theorem Related.prependEndpoints
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ front : List VExpr} {left right leftResult rightResult type : VExpr}
    {value support : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftTrace : TraceEndpoint registry front left leftResult)
    (rightTrace : TraceEndpoint registry front right rightResult)
    (generated : ProofInsertion env U Γ (front ++ Γ) (.skipN .refl front.length))
    (leftEq : env.IsDefEq U (front ++ Γ)
      (left.lift' (.skipN .refl front.length)) leftResult (type.lift' (.skipN .refl front.length)))
    (rightEq : env.IsDefEq U (front ++ Γ)
      (right.lift' (.skipN .refl front.length)) rightResult (type.lift' (.skipN .refl front.length)))
    (H : Related env U registry (front ++ Γ) leftResult rightResult
      (type.lift' (.skipN .refl front.length))
      (value.rename (.skipN .refl front.length)) (support.rename (.skipN .refl front.length))) :
    Related env U registry Γ left right type value support := by
  induction n generalizing Γ front left right leftResult rightResult type with
  | zero => exact H.prependEndpoints_zero henv hscoped leftTrace rightTrace generated leftEq rightEq
  | succ n ih =>
    apply Related.of_singletons
    intro atom member
    have single := H.singleton_of_mem (List.mem_map_of_mem member)
    have typed : (Profile.singleton atom).HasType support := by
      apply Profile.rename_hasType_iff.mp
      simpa only [Profile.rename_singleton] using single.singleton_typed (generated.targetWF henv)
    have typeCode := single.typeCode henv hscoped (generated.targetWF henv) (by
      intro empty
      cases empty)
    have baseCode := TypeRelated.absorb henv hscoped generated typeCode
    have finishCode {p : Profile (n + 1)} (wf : p.WF) {flag : Bool}
        (cover : (AtomData.sort flag : Atom (n + 1)) ∈ support.atoms)
        (code : TypeRelated env U registry (front ++ Γ) leftResult rightResult
          (p.rename (.skipN .refl front.length))) :
        TypeRelated env U registry Γ left right p := by
      obtain ⟨level, path⟩ := TypeRelated.sort_member_path henv generated.baseWF baseCode cover
      have raised := path.weak' henv generated.weakening
      exact TypeRelated.prependEndpoints henv hscoped wf leftTrace rightTrace generated
        (.single (raised.cast leftEq)) (.single (raised.cast rightEq)) code
    apply CoreRelated.related henv hscoped
    refine ⟨typed, baseCode, ?_⟩
    intro observed observedMember
    have equal : observed = atom := List.mem_singleton.mp observedMember
    subst observed
    cases atom with
    | fn key output =>
      apply FunctionBehavior.prependEndpoints henv hscoped
        (fun Γ front le re l r A p d hl hr gen cl cr h => ih hl hr gen cl cr h)
        leftTrace rightTrace generated leftEq rightEq
      simpa only [Profile.fn, Profile.rename_singleton, Atom.rename_fn] using single
    | pad atom =>
      have old : Related env U registry (front ++ Γ) leftResult rightResult
          (type.lift' (.skipN .refl front.length))
          (Profile.singleton (atom.rename (.skipN .refl front.length))).pad
          (support.rename (.skipN .refl front.length)) := single
      have reduced := old.unpad henv (generated.targetWF henv)
      have reduced' : Related env U registry (front ++ Γ) leftResult rightResult
          (type.lift' (.skipN .refl front.length))
          ((Profile.singleton atom).rename (.skipN .refl front.length))
          (support.down.rename (.skipN .refl front.length)) := by
        simpa only [Profile.rename_singleton, Profile.down_rename] using reduced
      exact ih leftTrace rightTrace generated leftEq rightEq reduced'
    | sort flag =>
      obtain ⟨r, cover⟩ := sort_cover typed
      apply finishCode typed.wf_value cover
      have code := sortCode henv hscoped (generated.targetWF henv) single
      change TypeRelated env U registry (front ++ Γ) leftResult rightResult
        ((Profile.sort flag).rename (.skipN .refl front.length))
      rw [Profile.rename_sort]
      exact code
    | family demand =>
      obtain ⟨r, cover⟩ := family_cover typed
      apply finishCode typed.wf_value cover
      exact familyCode henv hscoped (generated.targetWF henv) single
    | ctor demand =>
      apply RankedData.ConstructorRelation.prependEndpoints henv hscoped
        leftTrace rightTrace generated leftEq rightEq
      exact single.constructorRelation henv hscoped (generated.targetWF henv)
    | record demand =>
      apply RankedData.RecordRelation.prependEndpoints henv hscoped
        (fun Γ front le re l r A p d hl hr gen cl cr h => ih hl hr gen cl cr h)
        leftTrace rightTrace generated leftEq rightEq
      exact single.recordRelation henv hscoped (generated.targetWF henv)
    | pi A B domain rows =>
      obtain ⟨r, cover⟩ := pi_cover typed
      apply finishCode typed.wf_value cover
      have code := piCode henv hscoped (generated.targetWF henv) single
      simpa only [Profile.pi, Profile.singleton, Profile.mk, Profile.rename, Atom.rename, Rows.rename, Key.rename, List.map_cons, List.map_nil] using code

end Lean4Lean.AnchoredSemantics
