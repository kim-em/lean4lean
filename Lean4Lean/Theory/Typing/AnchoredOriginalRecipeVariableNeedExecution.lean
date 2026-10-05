import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecipeVariableBodyCompile

/-! Execute a computed variable demand from the actual exposed caller Need.
This does not ask for an interpreted argument or a live profile. In particular
it covers empty demands and returns ordinary code at the destination variable.
No canonical proof or captured substitution survives in that output. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open private raiseQueryAnnotation from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecipeVariableBodyCompile
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

/-- The caller supplies exactly the Need already exposed by `recipe.body`.
The original row's adapter compiles it at any destination local layout and
substitution, including a different selected anchor. -/
theorem RecipeVariableDemand.executeNeed
    {strata : EquationStratification env} {keyInput output : Profile n}
    {node : EndpointState sourceEnv U source (.bvar index) assigned}
    (demand : RecipeVariableDemand env U registry target keyInput output)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (sorted : output.HasType (.sort relevant))
    (need : (⟨n, keyInput⟩ : Need) ∈ available index)
    (controls : OriginalWorldControls strata controlSource)
    (frontier : List (EquationWorldClosureOrder.World strata.rules.length)) :
    ∃ footprint, ∃ certificate : RichCert sourceEnv env U registry target node
      locals σ relevant output footprint,
    ∃ ready : ControlledStoredQuery controls frontier (.certificate certificate),
      footprint.Available available ∧ ready.annotation.worlds = [] ∧
      ∀ policy, certificate.headDepth policy = 0 := by
  let query : RichObs sourceEnv env U registry target node locals σ keyInput
      [(index, ⟨n, keyInput⟩)] := .legacy (.legacy (.var locals σ index keyInput))
  let annotation : WorldObsProvenance strata query := .var
  have resources : Footprint.Available [(index, ⟨n, keyInput⟩)] available := by
    intro i requested member
    cases List.mem_singleton.mp member
    exact need
  let selection : GeneralNormalProfileAdapter env U registry target keyInput demand.input :=
    GeneralProfileAdapter.select (by
      intro atom member
      change atom ∈ demand.input.atoms.map AdapterNormal.atom at member
      change atom ∈ keyInput.atoms.map AdapterNormal.atom
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      exact List.mem_map.mpr ⟨original, demand.covered originalMember, rfl⟩)
  let adapter := (GeneralNormalProfileAdapter.raise henv hscoped formed demand.bound selection).comp demand.adapter
  obtain ⟨raisedAnnotation, worlds⟩ := raiseQueryAnnotation query annotation demand.bound
  obtain ⟨footprint, certificate, certificateAnnotation, supplied, included, depth⟩ :=
    (query.raise demand.bound).codeFromGeneral_worlds_depth henv raisedAnnotation adapter
      (Profile.HasType.raise_sort demand.bound sorted) resources
  let result := RichCert.observe (RichObs.lowerRaised (RichObs.code certificate)) sorted
  let resultAnnotation : WorldCertProvenance strata result :=
    .observe (.lowerRaised (.code certificateAnnotation)) sorted
  have noWorlds : certificateAnnotation.worlds = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro world member
    have lower := included member
    rw [worlds] at lower
    change world ∈ ([] : List (EquationWorldClosureOrder.World strata.rules.length)) at lower
    cases lower
  have zeroDepth : ∀ policy, result.headDepth policy = 0 := by
    intro policy
    have bounded := depth policy
    simp only [RichObs.headDepth_raise, query, RichObs.headDepth, SortableObs.headDepth,
      Obs.headDepth] at bounded
    simpa only [result, RichCert.headDepth, RichObs.headDepth_lowerRaised,
      RichObs.headDepth] using Nat.eq_zero_of_le_zero bounded
  refine ⟨footprint, result, ⟨resultAnnotation, ?_, ?_⟩, supplied, ?_, zeroDepth⟩
  · intro control active
    change result.headDepth _ ≤ _
    rw [zeroDepth]
    exact Nat.zero_le _
  · intro world member
    change world ∈ certificateAnnotation.worlds at member
    rw [noWorlds] at member
    cases member
  · exact noWorlds

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
