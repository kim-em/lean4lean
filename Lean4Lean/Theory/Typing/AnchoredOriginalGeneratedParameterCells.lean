import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedParameterEquality

/-! Dependent parameter cells are replayed in declaration order. Every
source reindex call chooses its own actual prior capture frame. The three
original equalities retain that selected frame; no intermediate semantic
alignment or completed capture group is supplied. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- An initial prior frame contains no answer to the next query. Its exact
capacity is the bound retained by recursive source reconstruction. -/
structure ParameterReplyFrame
    (base : OriginalCaptureBase env U registry target) (commonCaps : CaptureCaps)
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (commonLeft commonRight : Subst) where
  locals : List Nat
  available : Valuation
  realization : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available
  capped : CappedCaptureGenerated base commonCaps commonLeft commonRight graph realization.frame.raw
  closed : available.AtomClosed

noncomputable def ParameterReplyFrame.capacity
    {sourceEnv : VEnv} {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    (frame : ParameterReplyFrame base commonCaps graph commonLeft commonRight)
    (ordered : sourceEnv.Ordered) : Nat :=
  environmentCost (frame.realization.frame.dependencyEnvironment ordered)

/-- All seven calls are actual fixed original induction clauses. A call
receives the frame returned by its predecessor, not an independently chosen
resource valuation. Arbitrarily many previously captured parameters are
allowed in each original context. -/
theorem parameterCellsTransferGenerated
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
    (henv : env.Ordered) (familyOrdered : familyEnv.Ordered)
    (baseOrdered : baseEnv.Ordered) (typesOrdered : typesEnv.Ordered) (ctorOrdered : ctorEnv.Ordered)
    (baseBelow : baseEnv ≤ env) (typesBelow : typesEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (seedFrame : ParameterReplyFrame base commonCaps seedGraph commonLeft commonRight)
    (universeFrame : ParameterReplyFrame base commonCaps universeGraph commonLeft commonRight)
    (requestedFrame : ParameterReplyFrame base commonCaps requestedGraph commonLeft commonRight)
    (ctorFrame : ParameterReplyFrame base commonCaps ctorGraph commonLeft commonRight)
    (incoming : BoundedParameterReply base commonCaps start
      (familyGraph.parameterCellDisplay family familyProvenance)
      commonLeft commonRight (profile : Profile n) capacity)
    (sorted : profile.HasType (.sort relevant))
    (familyReserve : richSchedule .expressionReindex
      ((family.dependencyOrigin familyOrdered).weight * (1 + capacity) +
       (familyCell.dependencyOrigin baseOrdered).weight * (1 + seedFrame.capacity baseOrdered)) < limit)
    (familyEqualityReserve : richSchedule .fundamental
      ((familyCell.dependencyOrigin baseOrdered).weight * (1 + seedFrame.capacity baseOrdered)) < limit)
    (seedReserve : richSchedule .expressionReindex
      ((familyCell.dependencyOrigin baseOrdered).weight * (1 + seedFrame.capacity baseOrdered) +
       (universeCell.dependencyOrigin baseOrdered).weight * (1 + universeFrame.capacity baseOrdered)) < limit)
    (universeReserve : richSchedule .fundamental
      ((universeCell.dependencyOrigin baseOrdered).weight * (1 + universeFrame.capacity baseOrdered)) < limit)
    (requestedReserve : richSchedule .expressionReindex
      ((universeCell.dependencyOrigin baseOrdered).weight * (1 + universeFrame.capacity baseOrdered) +
       (ctorCell.dependencyOrigin typesOrdered).weight * (1 + requestedFrame.capacity typesOrdered)) < limit)
    (ctorEqualityReserve : richSchedule .fundamental
      ((ctorCell.dependencyOrigin typesOrdered).weight * (1 + requestedFrame.capacity typesOrdered)) < limit)
    (ctorReserve : richSchedule .expressionReindex
      ((ctorCell.dependencyOrigin typesOrdered).weight * (1 + requestedFrame.capacity typesOrdered) +
       (constructor.dependencyOrigin ctorOrdered).weight * (1 + ctorFrame.capacity ctorOrdered)) < limit)
    (familyR : GeneratedObservationCall base commonCaps
      (familyGraph.parameterCellDisplay family familyProvenance)
      (parameterEqualityDisplay seedGraph familyCell false) commonLeft commonRight familyOrdered baseOrdered limit)
    (familyF : ParameterEqualityInductionAt env registry baseOrdered seedContext familyCell false limit)
    (seedR : GeneratedObservationCall base commonCaps
      (parameterEqualityDisplay seedGraph familyCell true)
      (parameterEqualityDisplay universeGraph universeCell true) commonLeft commonRight baseOrdered baseOrdered limit)
    (universeF : ParameterEqualityInductionAt env registry baseOrdered universeContext universeCell true limit)
    (requestedR : GeneratedObservationCall base commonCaps
      (parameterEqualityDisplay universeGraph universeCell false)
      (parameterEqualityDisplay requestedGraph ctorCell true) commonLeft commonRight baseOrdered typesOrdered limit)
    (ctorF : ParameterEqualityInductionAt env registry typesOrdered requestedContext ctorCell true limit)
    (ctorR : GeneratedObservationCall base commonCaps
      (parameterEqualityDisplay requestedGraph ctorCell false)
      (ctorGraph.parameterCellDisplay constructor ctorProvenance) commonLeft commonRight typesOrdered ctorOrdered limit) :
    Nonempty (BoundedParameterReply base commonCaps start
      (ctorGraph.parameterCellDisplay constructor ctorProvenance)
      commonLeft commonRight profile (ctorFrame.capacity ctorOrdered)) := by
  obtain ⟨familyRight⟩ := incoming.reindexAt henv familyOrdered baseOrdered sorted
    seedFrame.realization seedFrame.capped seedFrame.closed familyReserve familyR
  obtain ⟨familyLeft, _, _⟩ := familyRight.equality seedGraph familyCell false henv baseOrdered baseBelow
    formed sorted familyEqualityReserve familyF
  obtain ⟨universeLeft⟩ := familyLeft.reindexAt henv baseOrdered baseOrdered sorted
    universeFrame.realization universeFrame.capped universeFrame.closed seedReserve seedR
  obtain ⟨universeRight, _, _⟩ := universeLeft.equality universeGraph universeCell true henv baseOrdered baseBelow
    formed sorted universeReserve universeF
  obtain ⟨ctorLeft⟩ := universeRight.reindexAt henv baseOrdered typesOrdered sorted
    requestedFrame.realization requestedFrame.capped requestedFrame.closed requestedReserve requestedR
  obtain ⟨ctorRight, _, _⟩ := ctorLeft.equality requestedGraph ctorCell true henv typesOrdered typesBelow
    formed sorted ctorEqualityReserve ctorF
  exact ctorRight.reindexAt henv typesOrdered ctorOrdered sorted
    ctorFrame.realization ctorFrame.capped ctorFrame.closed ctorReserve ctorR

/-- When the retained seed is already the requested universe tuple,
there is no extra universe equality root to charge or invoke. The actual
same-source middle R step joins the two independently typed contexts. -/
theorem parameterCellsTransferGeneratedSame
    {env familyEnv baseEnv typesEnv ctorEnv : VEnv} {U : Nat}
    {registry : CanonicalHead.Registry} {target common : List VExpr}
    {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
    {familyContext : ContextDerivation familyEnv U familySource}
    {seedContext : ContextDerivation baseEnv U seedSource}
    {requestedContext : ContextDerivation typesEnv U requestedSource}
    {ctorContext : ContextDerivation ctorEnv U ctorSource}
    (familyGraph : OriginalCaptureMap (common := common) familyContext raw)
    (seedGraph : OriginalCaptureMap (common := common) seedContext raw)
    (requestedGraph : OriginalCaptureMap (common := common) requestedContext raw)
    (ctorGraph : OriginalCaptureMap (common := common) ctorContext raw)
    (family : EndpointRef familyEnv U familySource familyDomain (.sort familyLevel))
    (familyProvenance : EndpointProvenance familyContext (.ref family))
    (familyCell : Derivation baseEnv U seedSource seedDomain familyDomain (.sort familySort))
    (ctorCell : Derivation typesEnv U requestedSource seedDomain ctorDomain (.sort ctorSort))
    (constructor : EndpointRef ctorEnv U ctorSource ctorDomain (.sort ctorLevel))
    (ctorProvenance : EndpointProvenance ctorContext (.ref constructor))
    (henv : env.Ordered) (familyOrdered : familyEnv.Ordered)
    (baseOrdered : baseEnv.Ordered) (typesOrdered : typesEnv.Ordered) (ctorOrdered : ctorEnv.Ordered)
    (baseBelow : baseEnv ≤ env) (typesBelow : typesEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (seedFrame : ParameterReplyFrame base commonCaps seedGraph commonLeft commonRight)
    (requestedFrame : ParameterReplyFrame base commonCaps requestedGraph commonLeft commonRight)
    (ctorFrame : ParameterReplyFrame base commonCaps ctorGraph commonLeft commonRight)
    (incoming : BoundedParameterReply base commonCaps start
      (familyGraph.parameterCellDisplay family familyProvenance)
      commonLeft commonRight (profile : Profile n) capacity)
    (sorted : profile.HasType (.sort relevant))
    (familyReserve : richSchedule .expressionReindex
      ((family.dependencyOrigin familyOrdered).weight * (1 + capacity) +
       (familyCell.dependencyOrigin baseOrdered).weight * (1 + seedFrame.capacity baseOrdered)) < limit)
    (familyEqualityReserve : richSchedule .fundamental
      ((familyCell.dependencyOrigin baseOrdered).weight * (1 + seedFrame.capacity baseOrdered)) < limit)
    (requestedReserve : richSchedule .expressionReindex
      ((familyCell.dependencyOrigin baseOrdered).weight * (1 + seedFrame.capacity baseOrdered) +
       (ctorCell.dependencyOrigin typesOrdered).weight * (1 + requestedFrame.capacity typesOrdered)) < limit)
    (ctorEqualityReserve : richSchedule .fundamental
      ((ctorCell.dependencyOrigin typesOrdered).weight * (1 + requestedFrame.capacity typesOrdered)) < limit)
    (ctorReserve : richSchedule .expressionReindex
      ((ctorCell.dependencyOrigin typesOrdered).weight * (1 + requestedFrame.capacity typesOrdered) +
       (constructor.dependencyOrigin ctorOrdered).weight * (1 + ctorFrame.capacity ctorOrdered)) < limit)
    (familyR : GeneratedObservationCall base commonCaps
      (familyGraph.parameterCellDisplay family familyProvenance)
      (parameterEqualityDisplay seedGraph familyCell false) commonLeft commonRight familyOrdered baseOrdered limit)
    (familyF : ParameterEqualityInductionAt env registry baseOrdered seedContext familyCell false limit)
    (requestedR : GeneratedObservationCall base commonCaps
      (parameterEqualityDisplay seedGraph familyCell true)
      (parameterEqualityDisplay requestedGraph ctorCell true) commonLeft commonRight baseOrdered typesOrdered limit)
    (ctorF : ParameterEqualityInductionAt env registry typesOrdered requestedContext ctorCell true limit)
    (ctorR : GeneratedObservationCall base commonCaps
      (parameterEqualityDisplay requestedGraph ctorCell false)
      (ctorGraph.parameterCellDisplay constructor ctorProvenance) commonLeft commonRight typesOrdered ctorOrdered limit) :
    Nonempty (BoundedParameterReply base commonCaps start
      (ctorGraph.parameterCellDisplay constructor ctorProvenance)
      commonLeft commonRight profile (ctorFrame.capacity ctorOrdered)) := by
  obtain ⟨familyRight⟩ := incoming.reindexAt henv familyOrdered baseOrdered sorted
    seedFrame.realization seedFrame.capped seedFrame.closed familyReserve familyR
  obtain ⟨familyLeft, _, _⟩ := familyRight.equality seedGraph familyCell false henv baseOrdered baseBelow
    formed sorted familyEqualityReserve familyF
  obtain ⟨ctorLeft⟩ := familyLeft.reindexAt henv baseOrdered typesOrdered sorted
    requestedFrame.realization requestedFrame.capped requestedFrame.closed requestedReserve requestedR
  obtain ⟨ctorRight, _, _⟩ := ctorLeft.equality requestedGraph ctorCell true henv typesOrdered typesBelow
    formed sorted ctorEqualityReserve ctorF
  exact ctorRight.reindexAt henv typesOrdered ctorOrdered sorted
    ctorFrame.realization ctorFrame.capped ctorFrame.closed ctorReserve ctorR

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
