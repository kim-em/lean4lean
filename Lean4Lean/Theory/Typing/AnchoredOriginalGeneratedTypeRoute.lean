import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedPiDomainRouteStep

/-! Finite original type-alignment histories. An edge is literal
source-expression reindexing, assigned-type comparison of actual original
terms, or a retained original equality derivation.
The data contains no completed alignment or semantic replay function. Each
edge's recursive reserve is computed before the incoming query is known. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

inductive GeneratedTypeRoute
    (base : OriginalCaptureBase env U registry target) (commonCaps : CaptureCaps)
    (commonLeft commonRight : Subst) :
    {leftExpression leftAssigned rightExpression rightAssigned : VExpr} →
    OriginalNestedDisplay U common leftExpression leftAssigned →
    OriginalNestedDisplay U common rightExpression rightAssigned → Nat → Nat → Type where
  | identity (display : OriginalNestedDisplay U common expression assigned) (capacity : Nat) :
      GeneratedTypeRoute base commonCaps commonLeft commonRight display display capacity capacity
  | same
      (left : OriginalNestedDisplay U common expression leftAssigned)
      (right : OriginalNestedDisplay U common expression rightAssigned)
      (leftOrdered : left.sourceEnv.Ordered) (rightOrdered : right.sourceEnv.Ordered)
      (capacity : Nat)
      (rightFrame : ParameterReplyFrame base commonCaps right.graph commonLeft commonRight) :
      GeneratedTypeRoute base commonCaps commonLeft commonRight left right capacity (rightFrame.capacity rightOrdered)
  | equality
      {context : ContextDerivation sourceEnv U source}
      (graph : OriginalCaptureMap (common := common) context raw)
      (original : Derivation sourceEnv U source A B (.sort level)) (forward : Bool)
      (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env) (capacity : Nat) :
      GeneratedTypeRoute base commonCaps commonLeft commonRight
        (parameterEqualityDisplay graph original forward) (parameterEqualityDisplay graph original (!forward))
        capacity capacity
  | assigned
      (left : OriginalNestedDisplay U common expression leftAssigned)
      (right : OriginalNestedDisplay U common expression rightAssigned)
      (leftOrdered : left.sourceEnv.Ordered) (rightOrdered : right.sourceEnv.Ordered)
      (capacity : Nat)
      (rightFrame : ParameterReplyFrame base commonCaps right.graph commonLeft commonRight) :
      GeneratedTypeRoute base commonCaps commonLeft commonRight
        left.formationDisplay right.formationDisplay capacity (rightFrame.capacity rightOrdered)
  | trans
      (first : GeneratedTypeRoute base commonCaps commonLeft commonRight left middle startCapacity middleCapacity)
      (second : GeneratedTypeRoute base commonCaps commonLeft commonRight middle right middleCapacity endCapacity) :
      GeneratedTypeRoute base commonCaps commonLeft commonRight left right startCapacity endCapacity
  | piDomain
      (left right : OriginalPiTypeRouteSide U common)
      (leftBelow : left.sourceEnv ≤ env)
      (route : GeneratedTypeRoute base commonCaps commonLeft commonRight
        left.display right.display startCapacity endCapacity) :
      GeneratedTypeRoute base commonCaps commonLeft commonRight
        left.domainDisplay right.domainDisplay startCapacity endCapacity

noncomputable def GeneratedTypeRoute.schedule
    (route : GeneratedTypeRoute base commonCaps commonLeft commonRight left right startCapacity endCapacity) : Nat :=
  match route with
  | .identity .. => 0
  | .same left right lf rf capacity frame =>
      richSchedule .expressionReindex
        ((left.node.dependencyOrigin lf).weight * (1 + capacity) +
         (Closure.close (right.node.dependencyOrigin rf) (frame.realization.frame.dependencyEnvironment rf)).cost)
  | .equality _ original _ ordered _ capacity =>
      richSchedule .fundamental ((original.dependencyOrigin ordered).weight * (1 + capacity))
  | .assigned left right lf rf capacity frame =>
      richSchedule .assignedComparison
        ((left.node.dependencyOrigin lf).weight * (1 + capacity) +
         (Closure.close (right.node.dependencyOrigin rf) (frame.realization.frame.dependencyEnvironment rf)).cost)
  | .trans first second => max first.schedule second.schedule
  | .piDomain _ _ _ route => route.schedule

/-- These are precisely the original mutual-induction clauses for the
retained edges. They are consumed by replay and are not stored in its data. -/
def GeneratedTypeRoute.Calls
    {base : OriginalCaptureBase env U registry target}
    (route : GeneratedTypeRoute base commonCaps commonLeft commonRight left right startCapacity endCapacity)
    (limit : Nat) : Prop :=
  match route with
  | .identity .. => True
  | .same left right lf rf _ _ =>
      GeneratedObservationCall base commonCaps left right commonLeft commonRight lf rf limit
  | .equality (context := context) _ original forward ordered _ _ =>
      ParameterEqualityInductionAt env registry ordered context original forward limit
  | .assigned left right lf rf _ _ =>
      GeneratedAssignedCall base commonCaps left right commonLeft commonRight lf rf limit
  | .trans first second => first.Calls limit ∧ second.Calls limit
  | .piDomain _ _ _ route => route.Calls limit

/-- Replay the type supports returned by owner F. Each equality uses its
predecessor's actual selected frame; each R/C edge selects its own bounded
frame. Pi-domain extraction embeds the support in an empty-row Pi query,
so this contract uses sort-true supports, including the empty support. -/
theorem GeneratedTypeRoute.replay
    {base : OriginalCaptureBase env U registry target}
    (route : GeneratedTypeRoute base commonCaps commonLeft commonRight left right startCapacity endCapacity)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (calls : route.Calls limit) (scheduled : route.schedule < limit)
    (incoming : BoundedParameterReply base commonCaps start left commonLeft commonRight (profile : Profile n) startCapacity)
    (sorted : profile.HasType (.sort true)) :
    Nonempty (BoundedParameterReply base commonCaps start right commonLeft commonRight profile endCapacity) := by
  induction route generalizing n start with
  | identity => exact ⟨incoming⟩
  | same left right lf rf capacity frame =>
    exact incoming.reindexAt henv lf rf sorted frame.realization frame.capped frame.closed scheduled calls
  | equality graph original forward ordered below capacity =>
    obtain ⟨result, _, _⟩ := incoming.equality graph original forward henv ordered below formed sorted scheduled calls
    exact ⟨result⟩
  | assigned left right lf rf capacity frame =>
    exact incoming.assignedAt henv lf rf sorted frame scheduled calls
  | trans first second ihFirst ihSecond =>
    obtain ⟨middle⟩ := ihFirst calls.1 (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) scheduled) incoming sorted
    exact ihSecond calls.2 (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) scheduled) middle sorted
  | piDomain left right below route ih =>
    exact BoundedParameterReply.piDomainStep left right below henv hscoped formed
      (fun answer sorted => ih calls scheduled answer sorted) incoming sorted

/-- The actual seven-edge parameter history is data independent of the
queried profile. In particular the three original equality derivations,
their distinct source contexts and both universe ledgers survive capture. -/
noncomputable def parameterCellsTypeRoute
    {env familyEnv baseEnv typesEnv ctorEnv : VEnv} {U : Nat}
    {registry : CanonicalHead.Registry} {target common : List VExpr}
    {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
    {familyContext : ContextDerivation familyEnv U familySource}
    {seedContext universeContext : ContextDerivation baseEnv U seedSource}
    {requestedContext : ContextDerivation typesEnv U requestedSource}
    {ctorContext : ContextDerivation ctorEnv U ctorSource}
    (familyGraph : OriginalCaptureMap (common := common) familyContext raw)
    (seedGraph : OriginalCaptureMap (common := common) seedContext raw)
    (universeGraph : OriginalCaptureMap (common := common) universeContext raw)
    (requestedGraph : OriginalCaptureMap (common := common) requestedContext raw)
    (ctorGraph : OriginalCaptureMap (common := common) ctorContext raw)
    (family : EndpointRef familyEnv U familySource familyDomain (.sort familyLevel))
    (familyProvenance : EndpointProvenance familyContext (.ref family))
    (familyCell : Derivation baseEnv U seedSource seedDomain familyDomain (.sort familySort))
    (universeCell : Derivation baseEnv U seedSource seedDomain requestedDomain (.sort universeSort))
    (ctorCell : Derivation typesEnv U requestedSource requestedDomain ctorDomain (.sort ctorSort))
    (constructor : EndpointRef ctorEnv U ctorSource ctorDomain (.sort ctorLevel))
    (ctorProvenance : EndpointProvenance ctorContext (.ref constructor))
    (familyOrdered : familyEnv.Ordered) (baseOrdered : baseEnv.Ordered)
    (typesOrdered : typesEnv.Ordered) (ctorOrdered : ctorEnv.Ordered)
    (baseBelow : baseEnv ≤ env) (typesBelow : typesEnv ≤ env)
    (capacity : Nat)
    (seedFrame : ParameterReplyFrame base commonCaps seedGraph commonLeft commonRight)
    (universeFrame : ParameterReplyFrame base commonCaps universeGraph commonLeft commonRight)
    (requestedFrame : ParameterReplyFrame base commonCaps requestedGraph commonLeft commonRight)
    (ctorFrame : ParameterReplyFrame base commonCaps ctorGraph commonLeft commonRight) :
    GeneratedTypeRoute base commonCaps commonLeft commonRight
      (familyGraph.parameterCellDisplay family familyProvenance)
      (ctorGraph.parameterCellDisplay constructor ctorProvenance)
      capacity (ctorFrame.capacity ctorOrdered) :=
  .trans (.same (familyGraph.parameterCellDisplay family familyProvenance) (parameterEqualityDisplay seedGraph familyCell false) familyOrdered baseOrdered capacity seedFrame)
    (.trans (.equality seedGraph familyCell false baseOrdered baseBelow (seedFrame.capacity baseOrdered))
      (.trans (.same (parameterEqualityDisplay seedGraph familyCell true) (parameterEqualityDisplay universeGraph universeCell true) baseOrdered baseOrdered
          (seedFrame.capacity baseOrdered) universeFrame)
        (.trans (.equality universeGraph universeCell true baseOrdered baseBelow (universeFrame.capacity baseOrdered))
          (.trans (.same (parameterEqualityDisplay universeGraph universeCell false) (parameterEqualityDisplay requestedGraph ctorCell true) baseOrdered typesOrdered
              (universeFrame.capacity baseOrdered) requestedFrame)
            (.trans (.equality requestedGraph ctorCell true typesOrdered typesBelow (requestedFrame.capacity typesOrdered))
              (.same (parameterEqualityDisplay requestedGraph ctorCell false) (ctorGraph.parameterCellDisplay constructor ctorProvenance) typesOrdered ctorOrdered (requestedFrame.capacity typesOrdered) ctorFrame))))))

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
