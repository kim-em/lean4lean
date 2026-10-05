import Lean4Lean.Theory.Typing.AnchoredOriginalScopedCaptureReindex
import Lean4Lean.Theory.Typing.AnchoredOriginalCappedApplicationCapture

/-! A requested own-capture value comes from its retained original query and
finite adapter. Target relatedness alone is deliberately not used to invent
source observations. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

noncomputable def ownCaptureArgumentDisplay
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (argument : EndpointState sourceEnv U source a A)
    (location : Located root argument)
    (lineage : location.contextDerivation initial = context) :
    OriginalNestedDisplay U common (a.subst raw) (A.subst raw) := {
  sourceEnv := sourceEnv, source := source, sourceExpression := a, sourceType := A
  context := context, node := argument
  provenance := ⟨_, _, _, root, initial, location, lineage.symm⟩
  raw := raw, graph := graph, expression_eq := rfl, type_eq := rfl }

/-- The own-capture branch of source-variable reconstruction. It dispatches
the stored ORIGINAL query, adapts its returned query at the exact recorded
rank, and selects the requested need. Both source frame closure and the
strict call bound are computed from the actual capture frame. -/
theorem reindexOwnCaptureBoundedHead
    {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered) (baseClosed : base.available.AtomClosed)
    (tail : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (capped : CappedCaptureGenerated base commonCaps commonLeft commonRight graph tail.frame.raw)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (initial : ContextDerivation sourceEnv U rootSource)
    (argument : EndpointState sourceEnv U source a A)
    (location : Located root argument)
    (lineage : location.contextDerivation initial = context)
    (query : RichObs sourceEnv env U registry target argument locals (raw.comp commonLeft)
      (rawInput : Profile k) argumentFootprint)
    (queryAvailable : argumentFootprint.Available available)
    (queryBound : n ≤ k)
    (queryAdapter : GeneralNormalProfileAdapter env U registry target rawInput (raiseProfile k queryBound (input : Profile n)))
    (certificate : RichCert sourceEnv env U registry target (.ref domain) locals (raw.comp commonLeft)
      true (support : Profile n) footprint)
    (resources : footprint.Available available) (typed : input.HasType support)
    (arguments : Related env U registry target (a.subst (raw.comp commonLeft))
      (a.subst (raw.comp commonRight)) (A.subst (raw.comp commonLeft)) input support)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms)
    (variableNode : EndpointState sourceEnv U (A :: source) (.bvar 0) variableType)
    (need : Need) (member : need ∈ needs)
    (destination : OriginalNestedDisplay U common (a.subst raw) destinationType)
    (destinationOrdered : destination.sourceEnv.Ordered)
    (destinationFrame : OriginalCaptureRealization destination.graph env registry target
      destinationLocals commonLeft commonRight destinationAvailable)
    (destinationGenerated : CappedCaptureGenerated base commonCaps commonLeft commonRight
      destination.graph destinationFrame.frame.raw)
    (destinationClosed : destinationAvailable.AtomClosed)
    (reindex : GeneratedObservationCall base commonCaps
      (ownCaptureArgumentDisplay graph initial argument location lineage) destination
      commonLeft commonRight ordered destinationOrdered
      (richSchedule .expressionReindex
        ((Closure.close (variableNode.dependencyOrigin ordered)
          ((tail.frame.capture domain initial argument location lineage query queryAvailable certificate resources
            typed arguments needs bounded covered).dependencyEnvironment ordered)).cost +
         (Closure.close (destination.node.dependencyOrigin destinationOrdered)
           (destinationFrame.frame.dependencyEnvironment destinationOrdered)).cost))) :
    Nonempty (BoundedGeneratedQueryReply base commonCaps destination commonLeft commonRight need.profile
      (environmentCost (destinationFrame.frame.dependencyEnvironment destinationOrdered))) := by
  obtain ⟨closedAvailable, closedTail, closedCapped, included, closed, sameEnvironment⟩ :=
    tail.closeResources capped baseClosed
  have scheduled : richSchedule .expressionReindex
      ((Closure.close (argument.dependencyOrigin ordered) (closedTail.frame.dependencyEnvironment ordered)).cost +
       (Closure.close (destination.node.dependencyOrigin destinationOrdered)
         (destinationFrame.frame.dependencyEnvironment destinationOrdered)).cost) <
      richSchedule .expressionReindex
        ((Closure.close (variableNode.dependencyOrigin ordered)
          ((tail.frame.capture domain initial argument location lineage query queryAvailable certificate resources
            typed arguments needs bounded covered).dependencyEnvironment ordered)).cost +
         (Closure.close (destination.node.dependencyOrigin destinationOrdered)
           (destinationFrame.frame.dependencyEnvironment destinationOrdered)).cost) := by
    rw [sameEnvironment]
    exact richSchedule_strict (Nat.add_lt_add_right
      (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (capturedVariable_bundle_lt (variableNode.dependencyOrigin ordered)
        (argument.dependencyOrigin ordered) (domain.dependencyOrigin ordered) (tail.frame.dependencyEnvironment ordered))) _) _ _
  obtain ⟨answer⟩ := reindex closedTail closedCapped closed destinationFrame destinationGenerated destinationClosed
    scheduled query (fun index need present => included index need (queryAvailable index need present))
  exact ⟨(answer.mapQuery (answer.answer.reply.query.adaptRequest henv hscoped formed queryBound queryAdapter)).localDemand
    need (bounded need member) (covered need member)⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
