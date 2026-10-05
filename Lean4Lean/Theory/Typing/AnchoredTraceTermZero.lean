import Lean4Lean.Theory.Typing.AnchoredTraceEndpoint
import Lean4Lean.Theory.Typing.AnchoredCoreIntroduction
import Lean4Lean.Theory.Typing.AnchoredCodeExtraction
import Lean4Lean.Theory.Typing.AnchoredHeadBeta

/-! The closed universe-demand base case of paired native trace expansion.
The raw equality is cast using the actual retained type capability, never a
comparison of independently inferred universes. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

/-- A nonempty singleton relation retains its intrinsic typing, even when
its chosen semantic core is behind a generated proof frame. -/
theorem Related.singleton_typed
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {left right type : VExpr} {atom : Atom n} {support : Profile n}
    (hΓ : OnCtx Γ (env.IsType U))
    (H : Related env U registry Γ left right type (.singleton atom) support) :
    (Profile.singleton atom).HasType support := by
  cases n <;>
    have original := H atom (List.mem_singleton_self _) Γ .refl (.refl hΓ)
  all_goals
    simp only [lift'_refl, Profile.rename_refl] at original
    rcases original with empty | ⟨_, _, _, typed, _⟩
    · cases empty
    · exact Profile.rename_hasType_iff.mp typed

theorem Related.prependEndpoints_zero
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ front : List VExpr} {left right leftResult rightResult type : VExpr}
    {value support : Profile 0}
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
  obtain ⟨cover, coverMember, _⟩ := typed atom (List.mem_singleton_self _)
  have sort := baseCode Γ .refl (.refl generated.baseWF) cover (by
    simpa [Profile.rename, Profile.atoms, Atom.rename] using coverMember)
  simp only [lift'_refl] at sort
  obtain ⟨level, path⟩ := SortRelated.path henv sort
  have raisedPath := path.weak' henv generated.weakening
  have valueCode := single.code_of_sortable henv hscoped (generated.targetWF henv)
    (show (Profile.singleton (atom.rename (.skipN .refl front.length))).HasType (.sort true) from
      Profile.HasType.sort _)
  have expanded := TypeRelated.prependEndpoints henv hscoped typed.wf_value
    leftTrace rightTrace generated (.single (raisedPath.cast leftEq))
      (.single (raisedPath.cast rightEq)) (by
        simpa only [Profile.rename_singleton] using valueCode)
  exact (show CoreRelated env U registry Γ left right type (.singleton atom) support from
    ⟨typed, baseCode, expanded⟩).related henv hscoped

end Lean4Lean.AnchoredSemantics
