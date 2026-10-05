import Lean4Lean.Theory.Typing.AnchoredOriginalCapturedQueryData

/-! Finite captured-need adapters and the actual retained owner's numeric
bound. These structural facts do not import a semantic replay interpreter. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
open private lifted_substitution from Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedCaptureReindex

noncomputable def RichGroupedCaptureEntry.scopeDisplay
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      locals σ available initial rawCapture leftValue rightValue)
    (scope : CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps entry.depth
      (entry.owner.context entry.initialContext)) :
    OriginalNestedDisplay U scope.scope ((rawCapture.subst ownerRaw).lift' (.skipN .refl entry.depth))
      (entry.owner.assigned.subst scope.raw) where
  sourceEnv := sourceEnv
  source := entry.owner.source
  sourceExpression := entry.owner.expression
  sourceType := entry.owner.assigned
  context := entry.owner.context entry.initialContext
  node := entry.owner.node
  provenance := entry.owner.provenance entry.initialContext
  raw := scope.raw
  graph := scope.graph
  expression_eq := by
    rw [entry.expression_eq, scope.raw_eq]
    exact (lifted_substitution _ _ _).symm
  type_eq := rfl

private noncomputable def needAdapter {need : Need}
    (queryBound : n ≤ k)
    (adapter : GeneralNormalProfileAdapter env U registry target (profile : Profile k)
      (raiseProfile k queryBound input))
    (bounded : need.rank ≤ n)
    (covered : ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    GeneralNormalProfileAdapter env U registry target profile
      (raiseProfile k (Nat.le_trans bounded queryBound) need.profile) := by
  have selected : GeneralNormalProfileAdapter env U registry target
      (raiseProfile k queryBound input) (raiseProfile k queryBound (need.atGrade n)) :=
    GeneralProfileAdapter.select (by
      intro atom member
      obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
      exact List.mem_map.mpr ⟨old, raiseProfile_subset queryBound covered old present, rfl⟩)
  simpa only [Need.atGrade, dif_pos bounded, raiseProfile_trans] using GeneralProfileAdapter.comp adapter selected

/-- A grouped owner pays for its actual semantic frame, as retained by the
entry, independently of the declaration environment. -/
theorem RichGroupedCapture.ownerQuery_cost_le_environment
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {context : ContextDerivation headerEnv U headerSource}
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    (tail : OriginalRichFrame headerEnv env U registry target context locals σ τ available)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ available initial rawCapture leftValue rightValue)
    {entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      locals σ available initial rawCapture leftValue rightValue}
    (member : entry ∈ entries) :
    (Closure.close (entry.owner.node.dependencyOrigin ordered) (entry.frame.dependencyEnvironment ordered)).cost ≤
      environmentCost ((tail.group domain ordered initial entries).dependencyEnvironment headerOrdered) := by
  rw [OriginalRichFrame.group_environment]
  have actual : (Closure.close (entry.owner.node.dependencyOrigin ordered) (entry.frame.dependencyEnvironment ordered)).cost ≤
      (entry.owner.dependencyClosure ordered initial).cost :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_left (entry.frame_environment_le ordered) 1)
  exact Nat.le_trans (Nat.le_trans actual (Nat.le_add_right _ _))
    (environment_entry (entries.lookup_member ordered headerOrdered member initial (tail.dependencyEnvironment headerOrdered)))

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
