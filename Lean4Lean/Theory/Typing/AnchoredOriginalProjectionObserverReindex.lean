import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionObserver

/-! Hereditary reconstruction of a whole projected argument cut. Every
primitive field node is reindexed at its own exact support before source
reflection; finite unions, adapters and grade changes retain that node.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- A whole cut returns actual typed projection syntax at the original
argument location. No assertion that the cut's old assigned type reflects
is used, and the argument provenance is not reconstructed from raw typing. -/
theorem ProjectionObs.reindexFromCoherence
    {sourceEnv env : VEnv} {U : Nat}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {origin : CutOriginAt root boundary (.proj name index major) 0}
    {registry : CanonicalHead.Registry} {target : List VExpr} {locals baseLocals : List Nat}
    {fullRealization σ : Subst} {fullAvailable available : Valuation}
    (query : ProjectionObs env registry target
      (origin.view.cast origin.expression_eq rfl) locals fullRealization demand footprint)
    (rootContext : ContextDerivation sourceEnv U rootSource)
    (argumentContext : ContextDerivation sourceEnv U (boundary ++ rootSource))
    (argument : EndpointState sourceEnv U (boundary ++ rootSource)
      (.proj name index major) argumentType)
    (argumentProvenance : EndpointProvenance argumentContext argument)
    (realizationTail : Subst.lift_l (.skipN .refl origin.depth) fullRealization = σ)
    (availableTail : ∀ index, fullAvailable (index + origin.depth) = available index)
    (resources : footprint.Available fullAvailable)
    (coherence : DisplayCoherenceAnswer env registry target
      (origin.sourceDisplay rootContext)
      (origin.argumentDisplay argumentContext argument argumentProvenance)
      fullRealization fullAvailable locals baseLocals) :
    ∃ nextFootprint, Nonempty (ProjectionObs env registry target argument
      baseLocals σ demand nextFootprint) ∧ nextFootprint.Available available := by
  induction query with
  | field nameEq member majorObservation fieldCertificate typed alignment =>
    let metadata : OriginalProjectionMetadata env registry target
        (origin.view.cast origin.expression_eq rfl) locals fullRealization _ _ :=
      ⟨⟨member, _, majorObservation, _, _, fieldCertificate, typed, alignment⟩, nameEq⟩
    have majorResources := fun i need member => resources i need (List.mem_append_left _ member)
    have fieldResources := fun i need member => resources i need (List.mem_append_right _ member)
    obtain ⟨next, _, nextMajor, nextField⟩ := metadata.reindexFromCoherence
      rootContext argumentContext argument argumentProvenance realizationTail availableTail
      majorResources fieldResources coherence
    exact ⟨next.packet.majorFootprint ++ next.packet.fieldFootprint,
      ⟨.field next.name_eq next.packet.member next.packet.majorObservation
        next.packet.fieldCertificate next.packet.typed next.packet.alignment⟩,
      fun i need member => (List.mem_append.mp member).elim (nextMajor i need) (nextField i need)⟩
  | empty => exact ⟨[], ⟨.empty⟩, fun _ _ member => nomatch member⟩
  | union left right ihLeft ihRight =>
    obtain ⟨leftFootprint, ⟨leftQuery⟩, leftResources⟩ :=
      ihLeft (fun i need member => resources i need (List.mem_append_left _ member))
    obtain ⟨rightFootprint, ⟨rightQuery⟩, rightResources⟩ :=
      ihRight (fun i need member => resources i need (List.mem_append_right _ member))
    exact ⟨leftFootprint ++ rightFootprint, ⟨.union leftQuery rightQuery⟩,
      fun i need member => (List.mem_append.mp member).elim
        (leftResources i need) (rightResources i need)⟩
  | view child change ih =>
    obtain ⟨nextFootprint, ⟨next⟩, nextResources⟩ := ih resources
    exact ⟨nextFootprint, ⟨.view next change⟩, nextResources⟩
  | unpad child ih =>
    obtain ⟨nextFootprint, ⟨next⟩, nextResources⟩ := ih resources
    exact ⟨nextFootprint, ⟨.unpad next⟩, nextResources⟩
  | raise child bound ih =>
    obtain ⟨nextFootprint, ⟨next⟩, nextResources⟩ := ih resources
    exact ⟨nextFootprint, ⟨.raise next bound⟩, nextResources⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
