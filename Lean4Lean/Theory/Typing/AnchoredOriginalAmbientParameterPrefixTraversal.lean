import Lean4Lean.Theory.Typing.AnchoredOriginalParameterTraceCursor
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionParameters
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientFamilyCellCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientRawParameterTypeRoute
import Lean4Lean.Theory.Typing.AnchoredOriginalTypeRouteCharges
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyNormalizationRouteLedger
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientFamilyApplyPiChainLedger
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyTelescopeCursor
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientFamilyHistoryTraversal

/-! Synchronized declaration cursors use the same original installation
packet and declaration position. Each cell retains the exact previous trace,
including the original formation references of its context. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics
open OriginalEndpointFactor OriginalTail OriginalEndpointFactor.Dependency
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
set_option Elab.async false

structure ProjectionParameterCellsAt
    (packet : OriginalProjectionParameters sourceEnv U name info seedLevels)
    (requestedWF : ∀ level ∈ requestedLevels, level.WF U)
    (seedWF : ∀ level ∈ seedLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) seedLevels requestedLevels) (index : Nat) where
  common : VExpr
  family : VExpr
  constructor : VExpr
  commonAt : packet.shape.common[index]? = some common
  familyAt : packet.shape.familyParams[index]? = some family
  constructorAt : packet.shape.ctorParams[index]? = some constructor
  familyCell : packet.instantiated.family.Cell (packet.shape.common.length - (index+1))
    (common.instL seedLevels) (family.instL seedLevels)
  universeCell : (packet.shape.commonUniverse seedWF requestedWF equivalent).Cell
    (packet.shape.common.length - (index+1)) (common.instL seedLevels) (common.instL requestedLevels)
  constructorCell : (packet.shape.instance requestedWF).constructor.Cell
    (packet.shape.common.length - (index+1)) (common.instL requestedLevels) (constructor.instL requestedLevels)

/-- Select every leg at the same declaration position from the actual frozen
packet. Universe equality cells retain the seed prefix, while constructor
cells retain their separately checked requested-universe prefix. -/
theorem projectionParameterCellsAt
    (packet : OriginalProjectionParameters sourceEnv U name info seedLevels)
    (requestedWF : ∀ level ∈ requestedLevels, level.WF U)
    (seedWF : ∀ level ∈ seedLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) seedLevels requestedLevels)
    (index : Nat) (bounded : index < info.nparams) :
    Nonempty (ProjectionParameterCellsAt packet requestedWF seedWF equivalent index) := by
  have familyLength : packet.shape.familyParams.length = info.nparams :=
    VExpr.takeForalls_domains_length packet.shape.familyTake
  have constructorLength : packet.shape.ctorParams.length = info.nparams :=
    VExpr.takeForalls_domains_length packet.shape.ctorTake
  have commonLength : packet.shape.common.length = info.nparams := by
    have same := packet.instantiated.family.length_eq
    simp only [List.length_map, List.length_reverse] at same
    exact same.trans familyLength
  have commonBound : index < packet.shape.common.length := by omega
  have familyBound : index < packet.shape.familyParams.length := by omega
  have constructorBound : index < packet.shape.ctorParams.length := by omega
  let common := packet.shape.common[index]
  let family := packet.shape.familyParams[index]
  let constructor := packet.shape.ctorParams[index]
  have commonAt : packet.shape.common[index]? = some common := List.getElem?_eq_getElem commonBound
  have familyAt : packet.shape.familyParams[index]? = some family := List.getElem?_eq_getElem familyBound
  have constructorAt : packet.shape.ctorParams[index]? = some constructor := List.getElem?_eq_getElem constructorBound
  have commonReverse : packet.shape.common.reverse[packet.shape.common.length-(index+1)]? = some common :=
    (List.getElem?_reverse' (by omega)).trans commonAt
  have familyReverse : packet.shape.familyParams.reverse[packet.shape.common.length-(index+1)]? = some family := by
    rw [commonLength, ← familyLength]
    exact (List.getElem?_reverse' (by omega)).trans familyAt
  have constructorReverse : packet.shape.ctorParams.reverse[packet.shape.common.length-(index+1)]? = some constructor := by
    rw [commonLength, ← constructorLength]
    exact (List.getElem?_reverse' (by omega)).trans constructorAt
  obtain ⟨familyCell⟩ := packet.instantiated.family.cell (packet.shape.common.length-(index+1))
    (by simp only [List.getElem?_map, commonReverse]; rfl)
    (by simp only [List.getElem?_map, familyReverse]; rfl)
  obtain ⟨universeCell⟩ := (packet.shape.commonUniverse seedWF requestedWF equivalent).cell
    (packet.shape.common.length-(index+1))
    (by simp only [List.getElem?_map, commonReverse]; rfl)
    (by simp only [List.getElem?_map, commonReverse]; rfl)
  obtain ⟨constructorCell⟩ := (packet.shape.instance requestedWF).constructor.cell
    (packet.shape.common.length-(index+1))
    (by simp only [List.getElem?_map, commonReverse]; rfl)
    (by simp only [List.getElem?_map, constructorReverse]; rfl)
  exact ⟨⟨common, family, constructor, commonAt, familyAt, constructorAt,
    familyCell, universeCell, constructorCell⟩⟩


private theorem head_of_wrapForalls_drop
    {domains : List VExpr} (selected : domains[index]? = some domain)
    (cursor : VExpr.forallE A B = VExpr.wrapForalls (domains.drop index) tail) : A = domain := by
  obtain ⟨bounded, same⟩ := List.getElem?_eq_some_iff.mp selected
  rw [List.drop_eq_getElem_cons bounded] at cursor
  exact (VExpr.forallE.inj cursor).1.trans same

/-- The current family stage's literal domain is the family endpoint of
this exact retained cell, at the chosen seed universes. -/
theorem ProjectionParameterCellsAt.familyDomain
    {packet : OriginalProjectionParameters sourceEnv U name info seedLevels}
    {requestedWF : ∀ level ∈ requestedLevels, level.WF U}
    {seedWF : ∀ level ∈ seedLevels, level.WF U}
    {equivalent : List.Forall₂ (· ≈ ·) seedLevels requestedLevels}
    (cells : ProjectionParameterCellsAt packet requestedWF seedWF equivalent index)
    (cursor : VExpr.forallE A B = VExpr.wrapForalls
      ((packet.shape.familyParams.map (·.instL seedLevels)).drop index) tail) :
    A = cells.family.instL seedLevels :=
  head_of_wrapForalls_drop (by simp only [List.getElem?_map, cells.familyAt]; rfl) cursor

theorem ProjectionParameterCellsAt.constructorDomain
    {packet : OriginalProjectionParameters sourceEnv U name info seedLevels}
    {requestedWF : ∀ level ∈ requestedLevels, level.WF U}
    {seedWF : ∀ level ∈ seedLevels, level.WF U}
    {equivalent : List.Forall₂ (· ≈ ·) seedLevels requestedLevels}
    (cells : ProjectionParameterCellsAt packet requestedWF seedWF equivalent index)
    (cursor : VExpr.forallE A B = VExpr.wrapForalls
      ((packet.shape.ctorParams.map (·.instL requestedLevels)).drop index) tail) :
    A = cells.constructor.instL requestedLevels :=
  head_of_wrapForalls_drop (by simp only [List.getElem?_map, cells.constructorAt]; rfl) cursor

/-- This is a literal prefix of the frozen source telescope; its proof
context remains the deterministic trace cursor rather than a new reification. -/
theorem ProjectionParameterCellsAt.sourcePrefix
    {packet : OriginalProjectionParameters sourceEnv U name info seedLevels}
    {requestedWF : ∀ level ∈ requestedLevels, level.WF U}
    {seedWF : ∀ level ∈ seedLevels, level.WF U}
    {equivalent : List.Forall₂ (· ≈ ·) seedLevels requestedLevels}
    (cells : ProjectionParameterCellsAt packet requestedWF seedWF equivalent index)
    (levels : List VLevel) :
    (packet.shape.common.reverse.map (·.instL levels)).drop (packet.shape.common.length-(index+1)+1) =
      (packet.shape.common.take index).reverse.map (·.instL levels) := by
  obtain ⟨bounded, _⟩ := List.getElem?_eq_some_iff.mp cells.commonAt
  rw [← List.map_drop, List.drop_reverse]
  have same : packet.shape.common.length - (packet.shape.common.length-(index+1)+1) = index := by omega
  rw [same]


/-- A prefix is indexed by its actual remaining equality trace and the
shared raw argument map. The ledger belongs to the returned concrete frame. -/
structure AmbientTracePrefix
    {base : OriginalCaptureBase env U registry target}
    (trace : OriginalContextEquality headerEnv U source destination)
    (offset : Nat) (raw : Subst) (common : List VExpr)
    (commonCaps : CaptureCaps) (commonLeft commonRight : Subst)
    (ordered : headerEnv.Ordered) (sources : ParameterRouteSources sourceEnv U)
    (ownerInitial : List Closure) (count : Nat) where
  graph : OriginalCaptureMap (common := common) (trace.drop offset).context raw
  frame : AmbientParameterReplyFrame base commonCaps graph commonLeft commonRight
  ledger : ParameterRouteLedger sources ownerInitial count (frame.realization.frame.dependencyEnvironment ordered)

private theorem recontextParameterFrame
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation headerEnv U source}
    {nextContext : ContextDerivation headerEnv U nextSource}
    {graph : OriginalCaptureMap (common := common) context raw}
    (frame : AmbientParameterReplyFrame base caps graph commonLeft commonRight)
    (sameSource : source = nextSource) (sameContext : HEq context nextContext)
    (ordered : headerEnv.Ordered) :
    ∃ nextGraph : OriginalCaptureMap (common := common) nextContext raw,
      ∃ nextFrame : AmbientParameterReplyFrame base caps nextGraph commonLeft commonRight,
        nextFrame.realization.frame.dependencyEnvironment ordered =
          frame.realization.frame.dependencyEnvironment ordered := by
  subst nextSource
  have same := eq_of_heq sameContext
  subst nextContext
  exact ⟨graph, frame, rfl⟩

/-- Capture advances the stored proof context itself. The next map appends
exactly the same actual argument used by the family predecessor. -/
theorem AmbientTracePrefix.afterCapture
    {base : OriginalCaptureBase env U registry target}
    {trace : OriginalContextEquality headerEnv U source destination}
    (selected : trace.Cell offset A B)
    (sourceAt : source[offset]? = some A)
    {graph : OriginalCaptureMap (common := common) (trace.drop (offset+1)).context raw}
    {ownerContext : ContextDerivation ownerEnv U ownerSource}
    (ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw)
    (argument : EndpointState ownerEnv U ownerSource expression assigned)
    (provenance : EndpointProvenance ownerContext argument)
    (captured : AmbientParameterReplyFrame base caps
      (.capture graph (.left selected.original) ownerGraph argument provenance) commonLeft commonRight)
    (ordered : headerEnv.Ordered)
    (ledger : ParameterRouteLedger sources ownerInitial count
      (captured.realization.frame.dependencyEnvironment ordered)) :
    Nonempty (AmbientTracePrefix (base := base) trace offset (raw.cons (expression.subst ownerRaw))
      common caps commonLeft commonRight ordered sources ownerInitial count) := by
  have sourceShape : source.drop offset = A :: source.drop (offset+1) := by
    obtain ⟨bounded, same⟩ := List.getElem?_eq_some_iff.mp sourceAt
    rw [List.drop_eq_getElem_cons bounded, same]
  obtain ⟨nextGraph, nextFrame, same⟩ := recontextParameterFrame captured sourceShape.symm
    selected.next_context.symm ordered
  exact ⟨⟨nextGraph, nextFrame, ParameterRouteLedger.bounded ledger _ (Nat.le_of_eq (congrArg environmentCost same))⟩⟩

/-- A concrete next family selection supplies this equality. Transporting
all auxiliary prefixes by it cannot choose a different predecessor. -/
theorem AmbientTracePrefix.atRaw
    {base : OriginalCaptureBase env U registry target}
    {trace : OriginalContextEquality headerEnv U source destination}
    (state : AmbientTracePrefix (base := base) trace offset raw common caps commonLeft commonRight
      ordered sources ownerInitial count)
    (same : nextRaw = raw) :
    Nonempty (AmbientTracePrefix (base := base) trace offset nextRaw common caps commonLeft commonRight
      ordered sources ownerInitial count) := by
  subst nextRaw
  exact ⟨state⟩



private noncomputable def cellChargedTrans
    {first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial between}
    {second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right between final}
    (firstPaid : first.Charged sources ownerInitial count)
    (secondPaid : second.Charged sources ownerInitial count) :
    (first.trans second).Charged sources ownerInitial count := by
  rw [RawGeneratedTypeRoute.Charged.eq_def]
  exact ⟨firstPaid, secondPaid⟩

private noncomputable def cellChargedSame
    (left : OriginalNestedDisplay U common expression leftType)
    (right : OriginalNestedDisplay U common expression rightType)
    (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered) (initial : List Closure)
    (frame : OriginalTypeRouteFrame env registry target right.graph commonLeft commonRight)
    (paid : ParameterRouteCharge sources ownerInitial count
      (.bundle (.close (left.node.dependencyOrigin lf) initial)
        (.close (right.node.dependencyOrigin rf) (frame.realization.frame.dependencyEnvironment rf)))) :
    (RawGeneratedTypeRoute.same left right lf rf initial frame).Charged sources ownerInitial count := by
  rw [RawGeneratedTypeRoute.Charged.eq_def]
  exact paid

private noncomputable def cellChargedEquality
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (original : Derivation sourceEnv U source A B (.sort level)) (forward : Bool)
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env) (initial : List Closure)
    (paid : ParameterRouteCharge sources ownerInitial count (.close (original.dependencyOrigin ordered) initial)) :
    (RawGeneratedTypeRoute.equality (registry := registry) (target := target)
      (commonLeft := commonLeft) (commonRight := commonRight) graph original forward ordered below initial).Charged sources ownerInitial count := by
  rw [RawGeneratedTypeRoute.Charged.eq_def]
  exact paid

section CellPaths
variable
  {base : OriginalCaptureBase env U registry target}
  {seedContext universeContext : ContextDerivation baseEnv U seedSource}
  {requestedContext : ContextDerivation typesEnv U requestedSource}
  {ctorContext : ContextDerivation ctorEnv U ctorSource}
  (family : OriginalNestedDisplay U common (familyDomain.subst raw) familyAssigned)
  (seedGraph : OriginalCaptureMap (common := common) seedContext raw)
  (universeGraph : OriginalCaptureMap (common := common) universeContext raw)
  (requestedGraph : OriginalCaptureMap (common := common) requestedContext raw)
  (ctorGraph : OriginalCaptureMap (common := common) ctorContext raw)
  (familyCell : Derivation baseEnv U seedSource seedDomain familyDomain (.sort familySort))
  (universeCell : Derivation baseEnv U seedSource seedDomain requestedDomain (.sort universeSort))
  (ctorCell : Derivation typesEnv U requestedSource requestedDomain ctorDomain (.sort ctorSort))
  (constructor : EndpointRef ctorEnv U ctorSource ctorDomain (.sort ctorLevel))
  (ctorProvenance : EndpointProvenance ctorContext (.ref constructor))
  (familyOrdered : family.sourceEnv.Ordered) (baseOrdered : baseEnv.Ordered)
  (typesOrdered : typesEnv.Ordered) (ctorOrdered : ctorEnv.Ordered)
  (baseBelow : baseEnv ≤ env) (typesBelow : typesEnv ≤ env)
  (initial : List Closure)
  (seedFrame : AmbientParameterReplyFrame base caps seedGraph commonLeft commonRight)
  (universeFrame : AmbientParameterReplyFrame base caps universeGraph commonLeft commonRight)
  (requestedFrame : AmbientParameterReplyFrame base caps requestedGraph commonLeft commonRight)
  (ctorFrame : AmbientParameterReplyFrame base caps ctorGraph commonLeft commonRight)

/-- The first prefix follows the actual family cell backwards. -/
noncomputable def parameterSeedPath :
    RawGeneratedTypeRoute env registry target commonLeft commonRight family
      (seedGraph.parameterCellDisplay (.left familyCell) (.ofLocation .here seedContext))
      initial (seedFrame.realization.frame.dependencyEnvironment baseOrdered) :=
  (RawGeneratedTypeRoute.same family (seedGraph.typeEqualityDisplay familyCell false) familyOrdered baseOrdered
    initial seedFrame.toParameterReplyFrame.typeRouteFrame).trans
      (.equality seedGraph familyCell false baseOrdered baseBelow
        (seedFrame.realization.frame.dependencyEnvironment baseOrdered))

/-- The second prefix has its own retained context proof, at the same
seed universes. The source expression and raw substitution are literal. -/
noncomputable def parameterUniversePath :
    RawGeneratedTypeRoute env registry target commonLeft commonRight family
      (universeGraph.parameterCellDisplay (.left universeCell) (.ofLocation .here universeContext))
      initial (universeFrame.realization.frame.dependencyEnvironment baseOrdered) :=
  (parameterSeedPath family seedGraph familyCell familyOrdered baseOrdered baseBelow initial seedFrame).trans
    (.same (seedGraph.typeEqualityDisplay familyCell true) (universeGraph.typeEqualityDisplay universeCell true)
      baseOrdered baseOrdered (seedFrame.realization.frame.dependencyEnvironment baseOrdered)
      universeFrame.toParameterReplyFrame.typeRouteFrame)

/-- The requested-universe prefix is obtained from the retained universe
cell followed by the actual constructor-cell source occurrence. -/
noncomputable def parameterRequestedPath :
    RawGeneratedTypeRoute env registry target commonLeft commonRight family
      (requestedGraph.parameterCellDisplay (.left ctorCell) (.ofLocation .here requestedContext))
      initial (requestedFrame.realization.frame.dependencyEnvironment typesOrdered) :=
  ((parameterUniversePath family seedGraph universeGraph familyCell universeCell familyOrdered
    baseOrdered baseBelow initial seedFrame universeFrame).trans
      (.equality universeGraph universeCell true baseOrdered baseBelow
        (universeFrame.realization.frame.dependencyEnvironment baseOrdered))).trans
      (.same (universeGraph.typeEqualityDisplay universeCell false) (requestedGraph.typeEqualityDisplay ctorCell true)
        baseOrdered typesOrdered (universeFrame.realization.frame.dependencyEnvironment baseOrdered)
        requestedFrame.toParameterReplyFrame.typeRouteFrame)

/-- The real constructor header is a fourth parallel prefix, not another
parameter slot following the three retained equality contexts. -/
noncomputable def parameterConstructorPath :
    RawGeneratedTypeRoute env registry target commonLeft commonRight family
      (ctorGraph.parameterCellDisplay constructor ctorProvenance)
      initial (ctorFrame.realization.frame.dependencyEnvironment ctorOrdered) :=
  ((parameterRequestedPath family seedGraph universeGraph requestedGraph familyCell universeCell ctorCell
    familyOrdered baseOrdered typesOrdered baseBelow initial seedFrame universeFrame requestedFrame).trans
      (.equality requestedGraph ctorCell true typesOrdered typesBelow
        (requestedFrame.realization.frame.dependencyEnvironment typesOrdered))).trans
      (.same (requestedGraph.typeEqualityDisplay ctorCell false) (ctorGraph.parameterCellDisplay constructor ctorProvenance)
        typesOrdered ctorOrdered (requestedFrame.realization.frame.dependencyEnvironment typesOrdered)
        ctorFrame.toParameterReplyFrame.typeRouteFrame)

include familyOrdered in
theorem parameterSeedPath_generated (familyBelow : family.sourceEnv ≤ env) :
    (parameterSeedPath family seedGraph familyCell familyOrdered baseOrdered baseBelow initial seedFrame).AmbientGenerated base caps := by
  refine ⟨?_, ?_, ?_⟩
  · simp [parameterSeedPath, RawGeneratedTypeRoute.WellFormed.eq_def]
  · simp only [parameterSeedPath, RawGeneratedTypeRoute.Ambient.eq_def]
    exact ⟨⟨familyBelow, baseBelow⟩, trivial⟩
  · intro boxed member
    simp only [parameterSeedPath, RawGeneratedTypeRoute.frames.eq_def, List.mem_append, List.not_mem_nil,
      or_false, List.mem_singleton] at member
    subst boxed
    exact seedFrame.generation

theorem parameterUniversePath_generated (familyBelow : family.sourceEnv ≤ env) :
    (parameterUniversePath family seedGraph universeGraph familyCell universeCell familyOrdered
      baseOrdered baseBelow initial seedFrame universeFrame).AmbientGenerated base caps := by
  refine (parameterSeedPath_generated family seedGraph familyCell familyOrdered baseOrdered baseBelow initial
    seedFrame familyBelow).trans ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [RawGeneratedTypeRoute.WellFormed.eq_def]; trivial
  · rw [RawGeneratedTypeRoute.Ambient.eq_def]; exact ⟨baseBelow, baseBelow⟩
  · intro boxed member
    rw [RawGeneratedTypeRoute.frames.eq_def, List.mem_singleton] at member
    subst boxed
    exact universeFrame.generation

theorem parameterRequestedPath_generated (familyBelow : family.sourceEnv ≤ env) :
    (parameterRequestedPath family seedGraph universeGraph requestedGraph familyCell universeCell ctorCell
      familyOrdered baseOrdered typesOrdered baseBelow initial seedFrame universeFrame requestedFrame).AmbientGenerated base caps := by
  apply RawGeneratedTypeRoute.AmbientGenerated.trans
  · apply (parameterUniversePath_generated family seedGraph universeGraph familyCell universeCell
      familyOrdered baseOrdered baseBelow initial seedFrame universeFrame familyBelow).trans
    exact ⟨by rw [RawGeneratedTypeRoute.WellFormed.eq_def]; trivial,
      by rw [RawGeneratedTypeRoute.Ambient.eq_def]; trivial,
      by intro boxed member; rw [RawGeneratedTypeRoute.frames.eq_def] at member; cases member⟩
  · refine ⟨?_, ?_, ?_⟩
    · rw [RawGeneratedTypeRoute.WellFormed.eq_def]; trivial
    · rw [RawGeneratedTypeRoute.Ambient.eq_def]
      exact ⟨baseBelow, requestedFrame.generation.ambient.2.below⟩
    · intro boxed member
      rw [RawGeneratedTypeRoute.frames.eq_def, List.mem_singleton] at member
      subst boxed
      exact requestedFrame.generation

theorem parameterConstructorPath_generated (familyBelow : family.sourceEnv ≤ env) :
    (parameterConstructorPath family seedGraph universeGraph requestedGraph ctorGraph familyCell universeCell ctorCell
      constructor ctorProvenance familyOrdered baseOrdered typesOrdered ctorOrdered baseBelow typesBelow initial
      seedFrame universeFrame requestedFrame ctorFrame).AmbientGenerated base caps := by
  apply RawGeneratedTypeRoute.AmbientGenerated.trans
  · apply (parameterRequestedPath_generated family seedGraph universeGraph requestedGraph familyCell universeCell ctorCell
      familyOrdered baseOrdered typesOrdered baseBelow initial seedFrame universeFrame requestedFrame familyBelow).trans
    exact ⟨by rw [RawGeneratedTypeRoute.WellFormed.eq_def]; trivial,
      by rw [RawGeneratedTypeRoute.Ambient.eq_def]; trivial,
      by intro boxed member; rw [RawGeneratedTypeRoute.frames.eq_def] at member; cases member⟩
  · refine ⟨?_, ?_, ?_⟩
    · rw [RawGeneratedTypeRoute.WellFormed.eq_def]; trivial
    · rw [RawGeneratedTypeRoute.Ambient.eq_def]
      exact ⟨typesBelow, ctorFrame.generation.ambient.2.below⟩
    · intro boxed member
      rw [RawGeneratedTypeRoute.frames.eq_def, List.mem_singleton] at member
      subst boxed
      exact ctorFrame.generation


/-- All paths use the same preceding slot ledgers. The original equality
occurrences pay their own finite cells, including both universe endpoints. -/
noncomputable def parameterPaths_charged
    (familyOccurrence : ParameterRouteOccurrence sources familyOrdered family.node)
    (familyLeft : ParameterRouteOccurrence sources baseOrdered (.ref (.left familyCell)))
    (familyRight : ParameterRouteOccurrence sources baseOrdered (.ref (.right familyCell)))
    (universeLeft : ParameterRouteOccurrence sources baseOrdered (.ref (.left universeCell)))
    (universeRight : ParameterRouteOccurrence sources baseOrdered (.ref (.right universeCell)))
    (ctorLeft : ParameterRouteOccurrence sources typesOrdered (.ref (.left ctorCell)))
    (ctorRight : ParameterRouteOccurrence sources typesOrdered (.ref (.right ctorCell)))
    (ctorOccurrence : ParameterRouteOccurrence sources ctorOrdered (.ref constructor))
    (incomingLedger : ParameterRouteLedger sources ownerInitial count initial)
    (seedLedger : ParameterRouteLedger sources ownerInitial count
      (seedFrame.realization.frame.dependencyEnvironment baseOrdered))
    (universeLedger : ParameterRouteLedger sources ownerInitial count
      (universeFrame.realization.frame.dependencyEnvironment baseOrdered))
    (requestedLedger : ParameterRouteLedger sources ownerInitial count
      (requestedFrame.realization.frame.dependencyEnvironment typesOrdered))
    (ctorLedger : ParameterRouteLedger sources ownerInitial count
      (ctorFrame.realization.frame.dependencyEnvironment ctorOrdered)) :
    (parameterSeedPath family seedGraph familyCell familyOrdered baseOrdered baseBelow initial seedFrame).Charged sources ownerInitial count ×
    (parameterUniversePath family seedGraph universeGraph familyCell universeCell familyOrdered
      baseOrdered baseBelow initial seedFrame universeFrame).Charged sources ownerInitial count ×
    (parameterRequestedPath family seedGraph universeGraph requestedGraph familyCell universeCell ctorCell
      familyOrdered baseOrdered typesOrdered baseBelow initial seedFrame universeFrame requestedFrame).Charged sources ownerInitial count ×
    (parameterConstructorPath family seedGraph universeGraph requestedGraph ctorGraph familyCell universeCell ctorCell
      constructor ctorProvenance familyOrdered baseOrdered typesOrdered ctorOrdered baseBelow typesBelow initial
      seedFrame universeFrame requestedFrame ctorFrame).Charged sources ownerInitial count := by
  have seedPaid : (parameterSeedPath family seedGraph familyCell familyOrdered baseOrdered baseBelow initial seedFrame).Charged sources ownerInitial count := by
    simp only [parameterSeedPath, RawGeneratedTypeRoute.Charged.eq_def]
    exact ⟨.reindex familyOccurrence familyRight incomingLedger seedLedger,
      .equality ⟨baseEnv, baseOrdered, seedSource, seedDomain, familyDomain, .sort familySort,
        familyCell, familyLeft⟩ seedLedger⟩
  have universePaid : (parameterUniversePath family seedGraph universeGraph familyCell universeCell familyOrdered
      baseOrdered baseBelow initial seedFrame universeFrame).Charged sources ownerInitial count := by
    exact cellChargedTrans seedPaid (cellChargedSame _ _ _ _ _ _
      (.reindex familyLeft universeLeft seedLedger universeLedger))
  have requestedPaid : (parameterRequestedPath family seedGraph universeGraph requestedGraph familyCell universeCell ctorCell
      familyOrdered baseOrdered typesOrdered baseBelow initial seedFrame universeFrame requestedFrame).Charged sources ownerInitial count := by
    exact cellChargedTrans (cellChargedTrans universePaid (cellChargedEquality _ _ _ _ _ _
      (.equality ⟨baseEnv, baseOrdered, seedSource, seedDomain, requestedDomain, .sort universeSort,
        universeCell, universeLeft⟩ universeLedger)))
      (cellChargedSame _ _ _ _ _ _ (.reindex universeRight ctorLeft universeLedger requestedLedger))
  have ctorPaid : (parameterConstructorPath family seedGraph universeGraph requestedGraph ctorGraph familyCell universeCell ctorCell
      constructor ctorProvenance familyOrdered baseOrdered typesOrdered ctorOrdered baseBelow typesBelow initial
      seedFrame universeFrame requestedFrame ctorFrame).Charged sources ownerInitial count := by
    exact cellChargedTrans (cellChargedTrans requestedPaid (cellChargedEquality _ _ _ _ _ _
      (.equality ⟨typesEnv, typesOrdered, requestedSource, requestedDomain, ctorDomain, .sort ctorSort,
        ctorCell, ctorLeft⟩ requestedLedger)))
      (cellChargedSame _ _ _ _ _ _ (.reindex ctorRight ctorOccurrence requestedLedger ctorLedger))
  exact ⟨seedPaid, universePaid, requestedPaid, ctorPaid⟩

end CellPaths



section SameCellPaths
variable
  {base : OriginalCaptureBase env U registry target}
  {seedContext : ContextDerivation baseEnv U seedSource}
  {requestedContext : ContextDerivation typesEnv U requestedSource}
  {ctorContext : ContextDerivation ctorEnv U ctorSource}
  (family : OriginalNestedDisplay U common (familyDomain.subst raw) familyAssigned)
  (seedGraph : OriginalCaptureMap (common := common) seedContext raw)
  (requestedGraph : OriginalCaptureMap (common := common) requestedContext raw)
  (ctorGraph : OriginalCaptureMap (common := common) ctorContext raw)
  (familyCell : Derivation baseEnv U seedSource seedDomain familyDomain (.sort familySort))
  (ctorCell : Derivation typesEnv U requestedSource seedDomain ctorDomain (.sort ctorSort))
  (constructor : EndpointRef ctorEnv U ctorSource ctorDomain (.sort ctorLevel))
  (ctorProvenance : EndpointProvenance ctorContext (.ref constructor))
  (familyOrdered : family.sourceEnv.Ordered) (baseOrdered : baseEnv.Ordered)
  (typesOrdered : typesEnv.Ordered) (ctorOrdered : ctorEnv.Ordered)
  (baseBelow : baseEnv ≤ env) (typesBelow : typesEnv ≤ env)
  (initial : List Closure)
  (seedFrame : AmbientParameterReplyFrame base caps seedGraph commonLeft commonRight)
  (requestedFrame : AmbientParameterReplyFrame base caps requestedGraph commonLeft commonRight)
  (ctorFrame : AmbientParameterReplyFrame base caps ctorGraph commonLeft commonRight)

/-- Equal seed and requested universes use the literal common domain.
No reflexive universe derivation is invented or added to the ledger. -/
noncomputable def parameterSameRequestedPath :
    RawGeneratedTypeRoute env registry target commonLeft commonRight family
      (requestedGraph.parameterCellDisplay (.left ctorCell) (.ofLocation .here requestedContext))
      initial (requestedFrame.realization.frame.dependencyEnvironment typesOrdered) :=
  (parameterSeedPath family seedGraph familyCell familyOrdered baseOrdered baseBelow initial seedFrame).trans
    (.same (seedGraph.typeEqualityDisplay familyCell true) (requestedGraph.typeEqualityDisplay ctorCell true)
      baseOrdered typesOrdered (seedFrame.realization.frame.dependencyEnvironment baseOrdered)
      requestedFrame.toParameterReplyFrame.typeRouteFrame)

noncomputable def parameterSameConstructorPath :
    RawGeneratedTypeRoute env registry target commonLeft commonRight family
      (ctorGraph.parameterCellDisplay constructor ctorProvenance)
      initial (ctorFrame.realization.frame.dependencyEnvironment ctorOrdered) :=
  ((parameterSameRequestedPath family seedGraph requestedGraph familyCell ctorCell familyOrdered baseOrdered
    typesOrdered baseBelow initial seedFrame requestedFrame).trans
      (.equality requestedGraph ctorCell true typesOrdered typesBelow
        (requestedFrame.realization.frame.dependencyEnvironment typesOrdered))).trans
      (.same (requestedGraph.typeEqualityDisplay ctorCell false) (ctorGraph.parameterCellDisplay constructor ctorProvenance)
        typesOrdered ctorOrdered (requestedFrame.realization.frame.dependencyEnvironment typesOrdered)
        ctorFrame.toParameterReplyFrame.typeRouteFrame)

theorem parameterSameRequestedPath_generated (familyBelow : family.sourceEnv ≤ env) :
    (parameterSameRequestedPath family seedGraph requestedGraph familyCell ctorCell familyOrdered baseOrdered
      typesOrdered baseBelow initial seedFrame requestedFrame).AmbientGenerated base caps := by
  apply (parameterSeedPath_generated family seedGraph familyCell familyOrdered baseOrdered baseBelow initial seedFrame
    familyBelow).trans
  refine ⟨?_, ?_, ?_⟩
  · rw [RawGeneratedTypeRoute.WellFormed.eq_def]; trivial
  · rw [RawGeneratedTypeRoute.Ambient.eq_def]
    exact ⟨baseBelow, requestedFrame.generation.ambient.2.below⟩
  · intro boxed member
    rw [RawGeneratedTypeRoute.frames.eq_def, List.mem_singleton] at member
    subst boxed
    exact requestedFrame.generation

theorem parameterSameConstructorPath_generated (familyBelow : family.sourceEnv ≤ env) :
    (parameterSameConstructorPath family seedGraph requestedGraph ctorGraph familyCell ctorCell constructor ctorProvenance
      familyOrdered baseOrdered typesOrdered ctorOrdered baseBelow typesBelow initial seedFrame requestedFrame ctorFrame).AmbientGenerated base caps := by
  apply RawGeneratedTypeRoute.AmbientGenerated.trans
  · apply (parameterSameRequestedPath_generated family seedGraph requestedGraph familyCell ctorCell familyOrdered
      baseOrdered typesOrdered baseBelow initial seedFrame requestedFrame familyBelow).trans
    exact ⟨by rw [RawGeneratedTypeRoute.WellFormed.eq_def]; trivial,
      by rw [RawGeneratedTypeRoute.Ambient.eq_def]; trivial,
      by intro boxed member; rw [RawGeneratedTypeRoute.frames.eq_def] at member; cases member⟩
  · refine ⟨?_, ?_, ?_⟩
    · rw [RawGeneratedTypeRoute.WellFormed.eq_def]; trivial
    · rw [RawGeneratedTypeRoute.Ambient.eq_def]
      exact ⟨typesBelow, ctorFrame.generation.ambient.2.below⟩
    · intro boxed member
      rw [RawGeneratedTypeRoute.frames.eq_def, List.mem_singleton] at member
      subst boxed
      exact ctorFrame.generation

noncomputable def parameterSamePaths_charged
    (familyOccurrence : ParameterRouteOccurrence sources familyOrdered family.node)
    (familyLeft : ParameterRouteOccurrence sources baseOrdered (.ref (.left familyCell)))
    (familyRight : ParameterRouteOccurrence sources baseOrdered (.ref (.right familyCell)))
    (ctorLeft : ParameterRouteOccurrence sources typesOrdered (.ref (.left ctorCell)))
    (ctorRight : ParameterRouteOccurrence sources typesOrdered (.ref (.right ctorCell)))
    (ctorOccurrence : ParameterRouteOccurrence sources ctorOrdered (.ref constructor))
    (incomingLedger : ParameterRouteLedger sources ownerInitial count initial)
    (seedLedger : ParameterRouteLedger sources ownerInitial count
      (seedFrame.realization.frame.dependencyEnvironment baseOrdered))
    (requestedLedger : ParameterRouteLedger sources ownerInitial count
      (requestedFrame.realization.frame.dependencyEnvironment typesOrdered))
    (ctorLedger : ParameterRouteLedger sources ownerInitial count
      (ctorFrame.realization.frame.dependencyEnvironment ctorOrdered)) :
    (parameterSeedPath family seedGraph familyCell familyOrdered baseOrdered baseBelow initial seedFrame).Charged sources ownerInitial count ×
    (parameterSameRequestedPath family seedGraph requestedGraph familyCell ctorCell familyOrdered baseOrdered
      typesOrdered baseBelow initial seedFrame requestedFrame).Charged sources ownerInitial count ×
    (parameterSameConstructorPath family seedGraph requestedGraph ctorGraph familyCell ctorCell constructor ctorProvenance
      familyOrdered baseOrdered typesOrdered ctorOrdered baseBelow typesBelow initial seedFrame requestedFrame ctorFrame).Charged sources ownerInitial count := by
  have seedPaid : (parameterSeedPath family seedGraph familyCell familyOrdered baseOrdered baseBelow initial seedFrame).Charged sources ownerInitial count := by
    simp only [parameterSeedPath, RawGeneratedTypeRoute.Charged.eq_def]
    exact ⟨.reindex familyOccurrence familyRight incomingLedger seedLedger,
      .equality ⟨baseEnv, baseOrdered, seedSource, seedDomain, familyDomain, .sort familySort,
        familyCell, familyLeft⟩ seedLedger⟩
  have requestedPaid : (parameterSameRequestedPath family seedGraph requestedGraph familyCell ctorCell familyOrdered
      baseOrdered typesOrdered baseBelow initial seedFrame requestedFrame).Charged sources ownerInitial count :=
    cellChargedTrans seedPaid (cellChargedSame _ _ _ _ _ _
      (.reindex familyLeft ctorLeft seedLedger requestedLedger))
  have ctorPaid : (parameterSameConstructorPath family seedGraph requestedGraph ctorGraph familyCell ctorCell constructor ctorProvenance
      familyOrdered baseOrdered typesOrdered ctorOrdered baseBelow typesBelow initial seedFrame requestedFrame ctorFrame).Charged sources ownerInitial count :=
    cellChargedTrans (cellChargedTrans requestedPaid (cellChargedEquality _ _ _ _ _ _
      (.equality ⟨typesEnv, typesOrdered, requestedSource, seedDomain, ctorDomain, .sort ctorSort,
        ctorCell, ctorLeft⟩ requestedLedger)))
      (cellChargedSame _ _ _ _ _ _ (.reindex ctorRight ctorOccurrence requestedLedger ctorLedger))
  exact ⟨seedPaid, requestedPaid, ctorPaid⟩

end SameCellPaths

section ParallelCapture
variable
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  {major : EndpointRef sourceEnv U source majorExpression majorType}
  (initialContext : ContextDerivation sourceEnv U source)
  (domain : EndpointRef sourceEnv U source A (.sort u))
  (body : EndpointState sourceEnv U (A :: source) B (.sort v))
  (function : EndpointState sourceEnv U source f (.forallE A B))
  (argument : EndpointState sourceEnv U source a A)
  (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
  (hu : u.WF U) (hv : v.WF U)
  (location : Located major (.app hu hv (.ref domain) body function argument result))
  (sourceGraph : OriginalCaptureMap (common := common) (location.contextDerivation initialContext) sourceRaw)
  {right : OriginalPiTypeRouteSide U common}
  (history : OriginalApplyPiHistory env registry target commonLeft commonRight
    (originalApplicationTypeRouteSide initialContext domain body function argument result hu hv location sourceGraph) right)
  (noBinders : location.binderPrefix = [])
  (sourceBound : ∀ ordered : sourceEnv.Ordered,
    environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost (location.dependencyEnvironment ordered ownerInitial))
  {base : OriginalCaptureBase env U registry target}
  {seedContext universeContext : ContextDerivation baseEnv U seedSource}
  {requestedContext : ContextDerivation typesEnv U requestedSource}
  {ctorContext : ContextDerivation ctorEnv U ctorSource}
  (seedGraph : OriginalCaptureMap (common := common) seedContext right.raw)
  (universeGraph : OriginalCaptureMap (common := common) universeContext right.raw)
  (requestedGraph : OriginalCaptureMap (common := common) requestedContext right.raw)
  (ctorGraph : OriginalCaptureMap (common := common) ctorContext right.raw)
  (familyCell : Derivation baseEnv U seedSource seedDomain right.A (.sort familySort))
  (universeCell : Derivation baseEnv U seedSource seedDomain requestedDomain (.sort universeSort))
  (ctorCell : Derivation typesEnv U requestedSource requestedDomain ctorDomain (.sort ctorSort))
  (constructor : EndpointRef ctorEnv U ctorSource ctorDomain (.sort ctorLevel))
  (ctorProvenance : EndpointProvenance ctorContext (.ref constructor))
  (baseOrdered : baseEnv.Ordered) (typesOrdered : typesEnv.Ordered) (ctorOrdered : ctorEnv.Ordered)
  (seedFrame : AmbientParameterReplyFrame base caps seedGraph commonLeft commonRight)
  (universeFrame : AmbientParameterReplyFrame base caps universeGraph commonLeft commonRight)
  (requestedFrame : AmbientParameterReplyFrame base caps requestedGraph commonLeft commonRight)
  (ctorFrame : AmbientParameterReplyFrame base caps ctorGraph commonLeft commonRight)

include noBinders sourceBound ctorProvenance in
/-- One actual family argument advances all four prior prefixes in
parallel. Every output raw map is `right.raw.cons (a.subst sourceRaw)` and
every output ledger has count `count+1`; no output is used as another
prefix's input. The only semantic calls come from the original lower bank. -/
theorem OriginalApplyPiHistory.captureParameterPrefixesAmbient
    (seedHeader requestedHeader : ParameterRouteHeader sourceEnv U)
    (generated : history.AmbientGenerated base caps)
    (sources : ParameterRouteSources sourceEnv U :=
      ⟨history.leftOrdered, source, fieldExpression, fieldType, majorExpression, majorType,
        field, major, seedHeader, requestedHeader⟩)
    (sourcesEq : sources =
      ⟨history.leftOrdered, source, fieldExpression, fieldType, majorExpression, majorType,
        field, major, seedHeader, requestedHeader⟩ := by rfl)
    (wholeCharged : history.whole.Charged sources ownerInitial count)
    (familyOccurrence : ParameterRouteOccurrence sources history.rightOrdered right.domainDisplay.node)
    (familyLeft : ParameterRouteOccurrence sources baseOrdered (.ref (.left familyCell)))
    (familyRight : ParameterRouteOccurrence sources baseOrdered (.ref (.right familyCell)))
    (universeLeft : ParameterRouteOccurrence sources baseOrdered (.ref (.left universeCell)))
    (universeRight : ParameterRouteOccurrence sources baseOrdered (.ref (.right universeCell)))
    (ctorLeft : ParameterRouteOccurrence sources typesOrdered (.ref (.left ctorCell)))
    (ctorRight : ParameterRouteOccurrence sources typesOrdered (.ref (.right ctorCell)))
    (ctorOccurrence : ParameterRouteOccurrence sources ctorOrdered (.ref constructor))
    (incomingLedger : ParameterRouteLedger sources ownerInitial count history.final)
    (seedLedger : ParameterRouteLedger sources ownerInitial count
      (seedFrame.realization.frame.dependencyEnvironment baseOrdered))
    (universeLedger : ParameterRouteLedger sources ownerInitial count
      (universeFrame.realization.frame.dependencyEnvironment baseOrdered))
    (requestedLedger : ParameterRouteLedger sources ownerInitial count
      (requestedFrame.realization.frame.dependencyEnvironment typesOrdered))
    (ctorLedger : ParameterRouteLedger sources ownerInitial count
      (ctorFrame.realization.frame.dependencyEnvironment ctorOrdered))
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (bank : OriginalLowerCallBank env U registry limit)
    (paid : richSchedule .expressionReindex
      (2 * sources.weight * parameterRouteCapacity sources count ownerInitial) < limit) :
    ∃ seedCapture : AmbientParameterReplyFrame base caps
        (.capture seedGraph (.left familyCell) sourceGraph argument
          (.ofLocation (.appArgument location) initialContext)) commonLeft commonRight,
    ∃ universeCapture : AmbientParameterReplyFrame base caps
        (.capture universeGraph (.left universeCell) sourceGraph argument
          (.ofLocation (.appArgument location) initialContext)) commonLeft commonRight,
    ∃ requestedCapture : AmbientParameterReplyFrame base caps
        (.capture requestedGraph (.left ctorCell) sourceGraph argument
          (.ofLocation (.appArgument location) initialContext)) commonLeft commonRight,
    ∃ ctorCapture : AmbientParameterReplyFrame base caps
        (.capture ctorGraph constructor sourceGraph argument
          (.ofLocation (.appArgument location) initialContext)) commonLeft commonRight,
      Nonempty (ParameterRouteLedger sources ownerInitial (count+1)
        (seedCapture.realization.frame.dependencyEnvironment baseOrdered)) ∧
      Nonempty (ParameterRouteLedger sources ownerInitial (count+1)
        (universeCapture.realization.frame.dependencyEnvironment baseOrdered)) ∧
      Nonempty (ParameterRouteLedger sources ownerInitial (count+1)
        (requestedCapture.realization.frame.dependencyEnvironment typesOrdered)) ∧
      Nonempty (ParameterRouteLedger sources ownerInitial (count+1)
        (ctorCapture.realization.frame.dependencyEnvironment ctorOrdered)) := by
  have baseBelow := seedFrame.generation.ambient.2.below
  have typesBelow := requestedFrame.generation.ambient.2.below
  have familyBelow := generated.header.ambient.2.below
  let seedPath := parameterSeedPath right.domainDisplay seedGraph familyCell history.rightOrdered baseOrdered
    baseBelow history.final seedFrame
  let universePath := parameterUniversePath right.domainDisplay seedGraph universeGraph familyCell universeCell
    history.rightOrdered baseOrdered baseBelow history.final seedFrame universeFrame
  let requestedPath := parameterRequestedPath right.domainDisplay seedGraph universeGraph requestedGraph
    familyCell universeCell ctorCell history.rightOrdered baseOrdered typesOrdered baseBelow history.final
    seedFrame universeFrame requestedFrame
  let ctorPath := parameterConstructorPath right.domainDisplay seedGraph universeGraph requestedGraph ctorGraph
    familyCell universeCell ctorCell constructor ctorProvenance history.rightOrdered baseOrdered typesOrdered ctorOrdered
    baseBelow typesBelow history.final seedFrame universeFrame requestedFrame ctorFrame
  have charges := parameterPaths_charged right.domainDisplay seedGraph universeGraph requestedGraph ctorGraph
    familyCell universeCell ctorCell constructor ctorProvenance history.rightOrdered baseOrdered typesOrdered ctorOrdered
    baseBelow typesBelow history.final seedFrame universeFrame requestedFrame ctorFrame
    familyOccurrence familyLeft familyRight universeLeft universeRight ctorLeft ctorRight ctorOccurrence
    incomingLedger seedLedger universeLedger requestedLedger ctorLedger
  obtain ⟨seedCapture, seedPaid⟩ := history.captureCellAmbient_counted (field := field)
    initialContext domain body function argument result hu hv location sourceGraph noBinders sourceBound
    seedGraph (.left familyCell) (.ofLocation .here seedContext) baseOrdered seedFrame seedHeader requestedHeader generated
    seedPath (parameterSeedPath_generated right.domainDisplay seedGraph familyCell history.rightOrdered baseOrdered
      baseBelow history.final seedFrame familyBelow)
    henv hscoped formed bank sources sourcesEq wholeCharged charges.1 familyLeft seedLedger paid
  obtain ⟨universeCapture, universePaid⟩ := history.captureCellAmbient_counted (field := field)
    initialContext domain body function argument result hu hv location sourceGraph noBinders sourceBound
    universeGraph (.left universeCell) (.ofLocation .here universeContext) baseOrdered universeFrame seedHeader requestedHeader generated
    universePath (parameterUniversePath_generated right.domainDisplay seedGraph universeGraph familyCell universeCell
      history.rightOrdered baseOrdered baseBelow history.final seedFrame universeFrame familyBelow)
    henv hscoped formed bank sources sourcesEq wholeCharged charges.2.1 universeLeft universeLedger paid
  obtain ⟨requestedCapture, requestedPaid⟩ := history.captureCellAmbient_counted (field := field)
    initialContext domain body function argument result hu hv location sourceGraph noBinders sourceBound
    requestedGraph (.left ctorCell) (.ofLocation .here requestedContext) typesOrdered requestedFrame seedHeader requestedHeader generated
    requestedPath (parameterRequestedPath_generated right.domainDisplay seedGraph universeGraph requestedGraph
      familyCell universeCell ctorCell history.rightOrdered baseOrdered typesOrdered baseBelow history.final
      seedFrame universeFrame requestedFrame familyBelow)
    henv hscoped formed bank sources sourcesEq wholeCharged charges.2.2.1 ctorLeft requestedLedger paid
  obtain ⟨ctorCapture, ctorPaid⟩ := history.captureCellAmbient_counted (field := field)
    initialContext domain body function argument result hu hv location sourceGraph noBinders sourceBound
    ctorGraph constructor ctorProvenance ctorOrdered ctorFrame seedHeader requestedHeader generated
    ctorPath (parameterConstructorPath_generated right.domainDisplay seedGraph universeGraph requestedGraph ctorGraph
      familyCell universeCell ctorCell constructor ctorProvenance history.rightOrdered baseOrdered typesOrdered ctorOrdered
      baseBelow typesBelow history.final seedFrame universeFrame requestedFrame ctorFrame familyBelow)
    henv hscoped formed bank sources sourcesEq wholeCharged charges.2.2.2 ctorOccurrence ctorLedger paid
  exact ⟨seedCapture, universeCapture, requestedCapture, ctorCapture, seedPaid, universePaid, requestedPaid, ctorPaid⟩

end ParallelCapture

section SameParallelCapture
variable
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  {major : EndpointRef sourceEnv U source majorExpression majorType}
  (initialContext : ContextDerivation sourceEnv U source)
  (domain : EndpointRef sourceEnv U source A (.sort u))
  (body : EndpointState sourceEnv U (A :: source) B (.sort v))
  (function : EndpointState sourceEnv U source f (.forallE A B))
  (argument : EndpointState sourceEnv U source a A)
  (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
  (hu : u.WF U) (hv : v.WF U)
  (location : Located major (.app hu hv (.ref domain) body function argument result))
  (sourceGraph : OriginalCaptureMap (common := common) (location.contextDerivation initialContext) sourceRaw)
  {right : OriginalPiTypeRouteSide U common}
  (history : OriginalApplyPiHistory env registry target commonLeft commonRight
    (originalApplicationTypeRouteSide initialContext domain body function argument result hu hv location sourceGraph) right)
  (noBinders : location.binderPrefix = [])
  (sourceBound : ∀ ordered : sourceEnv.Ordered,
    environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost (location.dependencyEnvironment ordered ownerInitial))
  {base : OriginalCaptureBase env U registry target}
  {seedContext : ContextDerivation baseEnv U seedSource}
  {requestedContext : ContextDerivation typesEnv U requestedSource}
  {ctorContext : ContextDerivation ctorEnv U ctorSource}
  (seedGraph : OriginalCaptureMap (common := common) seedContext right.raw)
  (requestedGraph : OriginalCaptureMap (common := common) requestedContext right.raw)
  (ctorGraph : OriginalCaptureMap (common := common) ctorContext right.raw)
  (familyCell : Derivation baseEnv U seedSource seedDomain right.A (.sort familySort))
  (ctorCell : Derivation typesEnv U requestedSource seedDomain ctorDomain (.sort ctorSort))
  (constructor : EndpointRef ctorEnv U ctorSource ctorDomain (.sort ctorLevel))
  (ctorProvenance : EndpointProvenance ctorContext (.ref constructor))
  (baseOrdered : baseEnv.Ordered) (typesOrdered : typesEnv.Ordered) (ctorOrdered : ctorEnv.Ordered)
  (seedFrame : AmbientParameterReplyFrame base caps seedGraph commonLeft commonRight)
  (requestedFrame : AmbientParameterReplyFrame base caps requestedGraph commonLeft commonRight)
  (ctorFrame : AmbientParameterReplyFrame base caps ctorGraph commonLeft commonRight)

include noBinders sourceBound ctorProvenance in
/-- One actual family argument advances the same-universe prefixes in
parallel. Every output raw map is `right.raw.cons (a.subst sourceRaw)` and
every output ledger has count `count+1`; no output is used as another
prefix's input. The only semantic calls come from the original lower bank. -/
theorem OriginalApplyPiHistory.captureSameParameterPrefixesAmbient
    (seedHeader requestedHeader : ParameterRouteHeader sourceEnv U)
    (generated : history.AmbientGenerated base caps)
    (sources : ParameterRouteSources sourceEnv U :=
      ⟨history.leftOrdered, source, fieldExpression, fieldType, majorExpression, majorType,
        field, major, seedHeader, requestedHeader⟩)
    (sourcesEq : sources =
      ⟨history.leftOrdered, source, fieldExpression, fieldType, majorExpression, majorType,
        field, major, seedHeader, requestedHeader⟩ := by rfl)
    (wholeCharged : history.whole.Charged sources ownerInitial count)
    (familyOccurrence : ParameterRouteOccurrence sources history.rightOrdered right.domainDisplay.node)
    (familyLeft : ParameterRouteOccurrence sources baseOrdered (.ref (.left familyCell)))
    (familyRight : ParameterRouteOccurrence sources baseOrdered (.ref (.right familyCell)))
    (ctorLeft : ParameterRouteOccurrence sources typesOrdered (.ref (.left ctorCell)))
    (ctorRight : ParameterRouteOccurrence sources typesOrdered (.ref (.right ctorCell)))
    (ctorOccurrence : ParameterRouteOccurrence sources ctorOrdered (.ref constructor))
    (incomingLedger : ParameterRouteLedger sources ownerInitial count history.final)
    (seedLedger : ParameterRouteLedger sources ownerInitial count
      (seedFrame.realization.frame.dependencyEnvironment baseOrdered))
    (requestedLedger : ParameterRouteLedger sources ownerInitial count
      (requestedFrame.realization.frame.dependencyEnvironment typesOrdered))
    (ctorLedger : ParameterRouteLedger sources ownerInitial count
      (ctorFrame.realization.frame.dependencyEnvironment ctorOrdered))
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (bank : OriginalLowerCallBank env U registry limit)
    (paid : richSchedule .expressionReindex
      (2 * sources.weight * parameterRouteCapacity sources count ownerInitial) < limit) :
    ∃ seedCapture : AmbientParameterReplyFrame base caps
        (.capture seedGraph (.left familyCell) sourceGraph argument
          (.ofLocation (.appArgument location) initialContext)) commonLeft commonRight,
    ∃ requestedCapture : AmbientParameterReplyFrame base caps
        (.capture requestedGraph (.left ctorCell) sourceGraph argument
          (.ofLocation (.appArgument location) initialContext)) commonLeft commonRight,
    ∃ ctorCapture : AmbientParameterReplyFrame base caps
        (.capture ctorGraph constructor sourceGraph argument
          (.ofLocation (.appArgument location) initialContext)) commonLeft commonRight,
      Nonempty (ParameterRouteLedger sources ownerInitial (count+1)
        (seedCapture.realization.frame.dependencyEnvironment baseOrdered)) ∧
      Nonempty (ParameterRouteLedger sources ownerInitial (count+1)
        (requestedCapture.realization.frame.dependencyEnvironment typesOrdered)) ∧
      Nonempty (ParameterRouteLedger sources ownerInitial (count+1)
        (ctorCapture.realization.frame.dependencyEnvironment ctorOrdered)) := by
  have baseBelow := seedFrame.generation.ambient.2.below
  have typesBelow := requestedFrame.generation.ambient.2.below
  have familyBelow := generated.header.ambient.2.below
  let seedPath := parameterSeedPath right.domainDisplay seedGraph familyCell history.rightOrdered baseOrdered
    baseBelow history.final seedFrame
  let requestedPath := parameterSameRequestedPath right.domainDisplay seedGraph requestedGraph
    familyCell ctorCell history.rightOrdered baseOrdered typesOrdered baseBelow history.final
    seedFrame requestedFrame
  let ctorPath := parameterSameConstructorPath right.domainDisplay seedGraph requestedGraph ctorGraph
    familyCell ctorCell constructor ctorProvenance history.rightOrdered baseOrdered typesOrdered ctorOrdered
    baseBelow typesBelow history.final seedFrame requestedFrame ctorFrame
  have charges := parameterSamePaths_charged right.domainDisplay seedGraph requestedGraph ctorGraph
    familyCell ctorCell constructor ctorProvenance history.rightOrdered baseOrdered typesOrdered ctorOrdered
    baseBelow typesBelow history.final seedFrame requestedFrame ctorFrame
    familyOccurrence familyLeft familyRight ctorLeft ctorRight ctorOccurrence
    incomingLedger seedLedger requestedLedger ctorLedger
  obtain ⟨seedCapture, seedPaid⟩ := history.captureCellAmbient_counted (field := field)
    initialContext domain body function argument result hu hv location sourceGraph noBinders sourceBound
    seedGraph (.left familyCell) (.ofLocation .here seedContext) baseOrdered seedFrame seedHeader requestedHeader generated
    seedPath (parameterSeedPath_generated right.domainDisplay seedGraph familyCell history.rightOrdered baseOrdered
      baseBelow history.final seedFrame familyBelow)
    henv hscoped formed bank sources sourcesEq wholeCharged charges.1 familyLeft seedLedger paid
  obtain ⟨requestedCapture, requestedPaid⟩ := history.captureCellAmbient_counted (field := field)
    initialContext domain body function argument result hu hv location sourceGraph noBinders sourceBound
    requestedGraph (.left ctorCell) (.ofLocation .here requestedContext) typesOrdered requestedFrame seedHeader requestedHeader generated
    requestedPath (parameterSameRequestedPath_generated right.domainDisplay seedGraph requestedGraph
      familyCell ctorCell history.rightOrdered baseOrdered typesOrdered baseBelow history.final
      seedFrame requestedFrame familyBelow)
    henv hscoped formed bank sources sourcesEq wholeCharged charges.2.1 ctorLeft requestedLedger paid
  obtain ⟨ctorCapture, ctorPaid⟩ := history.captureCellAmbient_counted (field := field)
    initialContext domain body function argument result hu hv location sourceGraph noBinders sourceBound
    ctorGraph constructor ctorProvenance ctorOrdered ctorFrame seedHeader requestedHeader generated
    ctorPath (parameterSameConstructorPath_generated right.domainDisplay seedGraph requestedGraph ctorGraph
      familyCell ctorCell constructor ctorProvenance history.rightOrdered baseOrdered typesOrdered ctorOrdered
      baseBelow typesBelow history.final seedFrame requestedFrame ctorFrame familyBelow)
    henv hscoped formed bank sources sourcesEq wholeCharged charges.2.2 ctorOccurrence ctorLedger paid
  exact ⟨seedCapture, requestedCapture, ctorCapture, seedPaid, requestedPaid, ctorPaid⟩

end SameParallelCapture


section TraceCapture
variable
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  {major : EndpointRef sourceEnv U source majorExpression majorType}
  (initialContext : ContextDerivation sourceEnv U source)
  (domain : EndpointRef sourceEnv U source A (.sort u))
  (body : EndpointState sourceEnv U (A :: source) B (.sort v))
  (function : EndpointState sourceEnv U source f (.forallE A B))
  (argument : EndpointState sourceEnv U source a A)
  (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
  (hu : u.WF U) (hv : v.WF U)
  (location : Located major (.app hu hv (.ref domain) body function argument result))
  (sourceGraph : OriginalCaptureMap (common := common) (location.contextDerivation initialContext) sourceRaw)
  {right : OriginalPiTypeRouteSide U common}
  (history : OriginalApplyPiHistory env registry target commonLeft commonRight
    (originalApplicationTypeRouteSide initialContext domain body function argument result hu hv location sourceGraph) right)
  (noBinders : location.binderPrefix = [])
  (sourceBound : ∀ ordered : sourceEnv.Ordered,
    environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost (location.dependencyEnvironment ordered ownerInitial))
  {base : OriginalCaptureBase env U registry target}
  {familyTrace : OriginalContextEquality baseEnv U commonSeedSource familySource}
  {universeTrace : OriginalContextEquality baseEnv U commonSeedSource commonRequestedSource}
  {ctorTrace : OriginalContextEquality typesEnv U commonRequestedSource ctorSource}
  (familySelected : familyTrace.Cell offset seedDomain right.A)
  (universeSelected : universeTrace.Cell offset seedDomain requestedDomain)
  (ctorSelected : ctorTrace.Cell offset requestedDomain ctorDomain)
  (seedAt : commonSeedSource[offset]? = some seedDomain)
  (requestedAt : commonRequestedSource[offset]? = some requestedDomain)
  (baseOrdered : baseEnv.Ordered) (typesOrdered : typesEnv.Ordered)
  (seedHeader requestedHeader : ParameterRouteHeader sourceEnv U)
  (sources : ParameterRouteSources sourceEnv U :=
    ⟨history.leftOrdered, source, fieldExpression, fieldType, majorExpression, majorType,
      field, major, seedHeader, requestedHeader⟩)
  (sourcesEq : sources =
    ⟨history.leftOrdered, source, fieldExpression, fieldType, majorExpression, majorType,
      field, major, seedHeader, requestedHeader⟩ := by rfl)
  (seedState : AmbientTracePrefix (base := base) familyTrace (offset+1) right.raw common caps commonLeft commonRight
    baseOrdered sources ownerInitial count)
  (universeState : AmbientTracePrefix (base := base) universeTrace (offset+1) right.raw common caps commonLeft commonRight
    baseOrdered sources ownerInitial count)
  (requestedState : AmbientTracePrefix (base := base) ctorTrace (offset+1) right.raw common caps commonLeft commonRight
    typesOrdered sources ownerInitial count)
  {ctorContext : ContextDerivation ctorEnv U headerSource}
  (ctorGraph : OriginalCaptureMap (common := common) ctorContext right.raw)
  (constructor : EndpointRef ctorEnv U headerSource ctorDomain (.sort ctorLevel))
  (ctorProvenance : EndpointProvenance ctorContext (.ref constructor))
  (ctorOrdered : ctorEnv.Ordered)
  (ctorFrame : AmbientParameterReplyFrame base caps ctorGraph commonLeft commonRight)

include noBinders sourceBound ctorProvenance sourcesEq seedState universeState requestedState seedAt requestedAt in
/-- The actual cell selections advance their own original context trees.
All three resulting prefixes accept the exact raw equality returned by
this predecessor's family successor; no independently chosen stage occurs. -/
theorem OriginalApplyPiHistory.captureRetainedParameterPrefixesAmbient
    (generated : history.AmbientGenerated base caps)
    (wholeCharged : history.whole.Charged sources ownerInitial count)
    (familyOccurrence : ParameterRouteOccurrence sources history.rightOrdered right.domainDisplay.node)
    (familyLeft : ParameterRouteOccurrence sources baseOrdered (.ref (.left familySelected.original)))
    (familyRight : ParameterRouteOccurrence sources baseOrdered (.ref (.right familySelected.original)))
    (universeLeft : ParameterRouteOccurrence sources baseOrdered (.ref (.left universeSelected.original)))
    (universeRight : ParameterRouteOccurrence sources baseOrdered (.ref (.right universeSelected.original)))
    (ctorLeft : ParameterRouteOccurrence sources typesOrdered (.ref (.left ctorSelected.original)))
    (ctorRight : ParameterRouteOccurrence sources typesOrdered (.ref (.right ctorSelected.original)))
    (ctorOccurrence : ParameterRouteOccurrence sources ctorOrdered (.ref constructor))
    (incomingLedger : ParameterRouteLedger sources ownerInitial count history.final)
    (ctorLedger : ParameterRouteLedger sources ownerInitial count
      (ctorFrame.realization.frame.dependencyEnvironment ctorOrdered))
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (bank : OriginalLowerCallBank env U registry limit)
    (paid : richSchedule .expressionReindex
      (2 * sources.weight * parameterRouteCapacity sources count ownerInitial) < limit) :
    ∃ ctorCapture : AmbientParameterReplyFrame base caps
        (.capture ctorGraph constructor sourceGraph argument
          (.ofLocation (.appArgument location) initialContext)) commonLeft commonRight,
      Nonempty (ParameterRouteLedger sources ownerInitial (count+1)
        (ctorCapture.realization.frame.dependencyEnvironment ctorOrdered)) ∧
      ∀ nextRaw, nextRaw = right.raw.cons (a.subst sourceRaw) →
        Nonempty (AmbientTracePrefix (base := base) familyTrace offset nextRaw common caps commonLeft commonRight
          baseOrdered sources ownerInitial (count+1)) ∧
        Nonempty (AmbientTracePrefix (base := base) universeTrace offset nextRaw common caps commonLeft commonRight
          baseOrdered sources ownerInitial (count+1)) ∧
        Nonempty (AmbientTracePrefix (base := base) ctorTrace offset nextRaw common caps commonLeft commonRight
          typesOrdered sources ownerInitial (count+1)) := by
  obtain ⟨seedCapture, universeCapture, requestedCapture, ctorCapture,
      ⟨seedLedger⟩, ⟨universeLedger⟩, ⟨requestedLedger⟩, ctorLedger⟩ :=
    history.captureParameterPrefixesAmbient (field := field) initialContext domain body function argument result
      hu hv location sourceGraph noBinders sourceBound seedState.graph universeState.graph requestedState.graph ctorGraph
      familySelected.original universeSelected.original ctorSelected.original constructor ctorProvenance
      baseOrdered typesOrdered ctorOrdered seedState.frame universeState.frame requestedState.frame ctorFrame
      seedHeader requestedHeader generated sources sourcesEq wholeCharged familyOccurrence familyLeft familyRight
      universeLeft universeRight ctorLeft ctorRight ctorOccurrence incomingLedger seedState.ledger universeState.ledger
      requestedState.ledger ctorLedger henv hscoped formed bank paid
  obtain ⟨nextSeed⟩ := AmbientTracePrefix.afterCapture familySelected seedAt sourceGraph argument
    (.ofLocation (.appArgument location) initialContext) seedCapture baseOrdered seedLedger
  obtain ⟨nextUniverse⟩ := AmbientTracePrefix.afterCapture universeSelected seedAt sourceGraph argument
    (.ofLocation (.appArgument location) initialContext) universeCapture baseOrdered universeLedger
  obtain ⟨nextRequested⟩ := AmbientTracePrefix.afterCapture ctorSelected requestedAt sourceGraph argument
    (.ofLocation (.appArgument location) initialContext) requestedCapture typesOrdered requestedLedger
  refine ⟨ctorCapture, ctorLedger, ?_⟩
  intro nextRaw same
  exact ⟨nextSeed.atRaw same, nextUniverse.atRaw same, nextRequested.atRaw same⟩

end TraceCapture

section SameTraceCapture
variable
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  {major : EndpointRef sourceEnv U source majorExpression majorType}
  (initialContext : ContextDerivation sourceEnv U source)
  (domain : EndpointRef sourceEnv U source A (.sort u))
  (body : EndpointState sourceEnv U (A :: source) B (.sort v))
  (function : EndpointState sourceEnv U source f (.forallE A B))
  (argument : EndpointState sourceEnv U source a A)
  (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
  (hu : u.WF U) (hv : v.WF U)
  (location : Located major (.app hu hv (.ref domain) body function argument result))
  (sourceGraph : OriginalCaptureMap (common := common) (location.contextDerivation initialContext) sourceRaw)
  {right : OriginalPiTypeRouteSide U common}
  (history : OriginalApplyPiHistory env registry target commonLeft commonRight
    (originalApplicationTypeRouteSide initialContext domain body function argument result hu hv location sourceGraph) right)
  (noBinders : location.binderPrefix = [])
  (sourceBound : ∀ ordered : sourceEnv.Ordered,
    environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost (location.dependencyEnvironment ordered ownerInitial))
  {base : OriginalCaptureBase env U registry target}
  {familyTrace : OriginalContextEquality baseEnv U commonSeedSource familySource}
  {ctorTrace : OriginalContextEquality typesEnv U commonSeedSource ctorSource}
  (familySelected : familyTrace.Cell offset seedDomain right.A)
  (ctorSelected : ctorTrace.Cell offset seedDomain ctorDomain)
  (seedAt : commonSeedSource[offset]? = some seedDomain)
  (baseOrdered : baseEnv.Ordered) (typesOrdered : typesEnv.Ordered)
  (seedHeader requestedHeader : ParameterRouteHeader sourceEnv U)
  (sources : ParameterRouteSources sourceEnv U :=
    ⟨history.leftOrdered, source, fieldExpression, fieldType, majorExpression, majorType,
      field, major, seedHeader, requestedHeader⟩)
  (sourcesEq : sources =
    ⟨history.leftOrdered, source, fieldExpression, fieldType, majorExpression, majorType,
      field, major, seedHeader, requestedHeader⟩ := by rfl)
  (seedState : AmbientTracePrefix (base := base) familyTrace (offset+1) right.raw common caps commonLeft commonRight
    baseOrdered sources ownerInitial count)
  (requestedState : AmbientTracePrefix (base := base) ctorTrace (offset+1) right.raw common caps commonLeft commonRight
    typesOrdered sources ownerInitial count)
  {ctorContext : ContextDerivation ctorEnv U headerSource}
  (ctorGraph : OriginalCaptureMap (common := common) ctorContext right.raw)
  (constructor : EndpointRef ctorEnv U headerSource ctorDomain (.sort ctorLevel))
  (ctorProvenance : EndpointProvenance ctorContext (.ref constructor))
  (ctorOrdered : ctorEnv.Ordered)
  (ctorFrame : AmbientParameterReplyFrame base caps ctorGraph commonLeft commonRight)

include noBinders sourceBound ctorProvenance sourcesEq seedState requestedState seedAt in
/-- The actual cell selections advance their own original context trees.
Both resulting prefixes accept the exact raw equality returned by
this predecessor's family successor; no independently chosen stage occurs. -/
theorem OriginalApplyPiHistory.captureRetainedSameParameterPrefixesAmbient
    (generated : history.AmbientGenerated base caps)
    (wholeCharged : history.whole.Charged sources ownerInitial count)
    (familyOccurrence : ParameterRouteOccurrence sources history.rightOrdered right.domainDisplay.node)
    (familyLeft : ParameterRouteOccurrence sources baseOrdered (.ref (.left familySelected.original)))
    (familyRight : ParameterRouteOccurrence sources baseOrdered (.ref (.right familySelected.original)))
    (ctorLeft : ParameterRouteOccurrence sources typesOrdered (.ref (.left ctorSelected.original)))
    (ctorRight : ParameterRouteOccurrence sources typesOrdered (.ref (.right ctorSelected.original)))
    (ctorOccurrence : ParameterRouteOccurrence sources ctorOrdered (.ref constructor))
    (incomingLedger : ParameterRouteLedger sources ownerInitial count history.final)
    (ctorLedger : ParameterRouteLedger sources ownerInitial count
      (ctorFrame.realization.frame.dependencyEnvironment ctorOrdered))
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (bank : OriginalLowerCallBank env U registry limit)
    (paid : richSchedule .expressionReindex
      (2 * sources.weight * parameterRouteCapacity sources count ownerInitial) < limit) :
    ∃ ctorCapture : AmbientParameterReplyFrame base caps
        (.capture ctorGraph constructor sourceGraph argument
          (.ofLocation (.appArgument location) initialContext)) commonLeft commonRight,
      Nonempty (ParameterRouteLedger sources ownerInitial (count+1)
        (ctorCapture.realization.frame.dependencyEnvironment ctorOrdered)) ∧
      ∀ nextRaw, nextRaw = right.raw.cons (a.subst sourceRaw) →
        Nonempty (AmbientTracePrefix (base := base) familyTrace offset nextRaw common caps commonLeft commonRight
          baseOrdered sources ownerInitial (count+1)) ∧
        Nonempty (AmbientTracePrefix (base := base) ctorTrace offset nextRaw common caps commonLeft commonRight
          typesOrdered sources ownerInitial (count+1)) := by
  obtain ⟨seedCapture, requestedCapture, ctorCapture,
      ⟨seedLedger⟩, ⟨requestedLedger⟩, ctorLedger⟩ :=
    history.captureSameParameterPrefixesAmbient (field := field) initialContext domain body function argument result
      hu hv location sourceGraph noBinders sourceBound seedState.graph requestedState.graph ctorGraph
      familySelected.original ctorSelected.original constructor ctorProvenance
      baseOrdered typesOrdered ctorOrdered seedState.frame requestedState.frame ctorFrame
      seedHeader requestedHeader generated sources sourcesEq wholeCharged familyOccurrence familyLeft familyRight
      ctorLeft ctorRight ctorOccurrence incomingLedger seedState.ledger 
      requestedState.ledger ctorLedger henv hscoped formed bank paid
  obtain ⟨nextSeed⟩ := AmbientTracePrefix.afterCapture familySelected seedAt sourceGraph argument
    (.ofLocation (.appArgument location) initialContext) seedCapture baseOrdered seedLedger
  obtain ⟨nextRequested⟩ := AmbientTracePrefix.afterCapture ctorSelected seedAt sourceGraph argument
    (.ofLocation (.appArgument location) initialContext) requestedCapture typesOrdered requestedLedger
  refine ⟨ctorCapture, ctorLedger, ?_⟩
  intro nextRaw same
  exact ⟨nextSeed.atRaw same, nextRequested.atRaw same⟩

end SameTraceCapture


/-- Both directions name occurrences of the very same retained equality
root; neither endpoint is reconstructed from a raw equality. -/
structure ParameterCellOccurrences (sources : ParameterRouteSources sourceEnv U)
    (ordered : equalityEnv.Ordered) (original : Derivation equalityEnv U source A B (.sort level)) where
  left : ParameterRouteOccurrence sources ordered (.ref (.left original))
  right : ParameterRouteOccurrence sources ordered (.ref (.right original))

section Occurrences
variable
    {selection : RichHeaderSelection sourceEnv U name levels ordered}
    (ledger : FamilyParameterLedger selection)
    (registered : sourceEnv.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (field : EndpointRef sourceEnv U source fieldExpression fieldType)
    (major : EndpointRef sourceEnv U source majorExpression majorType)
    (cells : ProjectionParameterCellsAt (selectProjectionParameters ordered registered selection.seedWF)
      levelsWF selection.seedWF selection.equivalent index)

noncomputable def ProjectionParameterCellsAt.familyOccurrences :
    ParameterCellOccurrences (projectionRouteSources ordered registered levelsWF field major ledger.routeHeader)
      (selectProjectionParameters ordered registered selection.seedWF).origin.baseOrdered cells.familyCell.original := by
  let packet := selectProjectionParameters ordered registered selection.seedWF
  have member : packet.baseDependency cells.familyCell.root ∈ ledger.dependencies :=
    ledger.seedBase_mem registered cells.familyCell.root (List.mem_cons_of_mem _ cells.familyCell.retained)
  exact ⟨.seed (.equalityLeft (packet.baseDependency cells.familyCell.root) member .here),
    .seed (.equalityRight (packet.baseDependency cells.familyCell.root) member .here)⟩

noncomputable def ProjectionParameterCellsAt.constructorOccurrences :
    ParameterCellOccurrences (projectionRouteSources ordered registered levelsWF field major ledger.routeHeader)
      (selectProjectionParameters ordered registered selection.seedWF).origin.typesOrdered cells.constructorCell.original := by
  let requested := selectProjectionParameters ordered registered levelsWF
  have member : requested.typeDependency cells.constructorCell.root ∈
      projectionParameterDependencies ordered registered levelsWF :=
    List.mem_append_right _ (List.mem_map.mpr ⟨cells.constructorCell.root, cells.constructorCell.retained, rfl⟩)
  exact ⟨.requested (.equalityLeft (requested.typeDependency cells.constructorCell.root) member .here),
    .requested (.equalityRight (requested.typeDependency cells.constructorCell.root) member .here)⟩

/-- This constructor is intentionally restricted to the displayed OTHER
instance. In the same-seed branch the five-edge path omits this root. -/
noncomputable def ProjectionParameterCellsAt.universeOccurrences
    (displayed : levels = ledger.otherLevels) :
    ParameterCellOccurrences (projectionRouteSources ordered registered levelsWF field major ledger.routeHeader)
      (selectProjectionParameters ordered registered selection.seedWF).origin.baseOrdered cells.universeCell.original := by
  let packet := selectProjectionParameters ordered registered selection.seedWF
  have member : packet.baseDependency cells.universeCell.root ∈ ledger.dependencies :=
    ledger.universe_mem registered levelsWF displayed cells.universeCell.root cells.universeCell.retained
  exact ⟨.seed (.equalityLeft (packet.baseDependency cells.universeCell.root) member .here),
    .seed (.equalityRight (packet.baseDependency cells.universeCell.root) member .here)⟩

end Occurrences


/-- The constructor successor is selected from the captured ORIGINAL body.
It keeps the actual returned frame and the shared raw argument map, while
its exposed domain/body are computed from the retained telescope cursor. -/
theorem OriginalPiTypeRouteSide.nextCapturedParameterAmbient
    {base : OriginalCaptureBase env U registry target}
    (side : OriginalPiTypeRouteSide U common)
    (domain : EndpointRef side.sourceEnv U side.source side.A (.sort side.u))
    (domainEq : side.domain = .ref domain)
    (owner : OriginalApplicationTypeRouteSide U common)
    (ordered : side.sourceEnv.Ordered)
    (captured : AmbientParameterReplyFrame base caps (side.capturedBody domain domainEq owner).graph
      commonLeft commonRight)
    (occurrence : ParameterRouteOccurrence sources ordered side.display.node)
    (ledger : ParameterRouteLedger sources ownerInitial count
      (captured.realization.frame.dependencyEnvironment ordered))
    (cursor : FamilyTelescopeCursor domains tail index side)
    (remaining : index+1 < domains.length) :
    ∃ next : OriginalPiTypeRouteSide U common,
    ∃ nextOrdered : next.sourceEnv.Ordered,
    ∃ nextFrame : AmbientParameterReplyFrame base caps next.graph commonLeft commonRight,
      FamilyTelescopeCursor domains tail (index+1) next ∧
      next.raw = side.raw.cons (owner.a.subst owner.raw) ∧
      nextFrame.realization.frame.dependencyEnvironment nextOrdered =
        captured.realization.frame.dependencyEnvironment ordered ∧
      Nonempty (ParameterRouteOccurrence sources nextOrdered next.display.node) ∧
      Nonempty (ParameterRouteLedger sources ownerInitial count
        (nextFrame.realization.frame.dependencyEnvironment nextOrdered)) ∧
      ∃ nextDomain : EndpointRef next.sourceEnv U next.source next.A (.sort next.u),
        next.domain = .ref nextDomain := by
  obtain ⟨nextA, nextB, shape, cursorNext⟩ := cursor.next remaining
  let display := side.capturedBody domain domainEq owner
  have bodyOccurrence : ParameterRouteOccurrence sources ordered display.node := occurrence.piBody
  obtain ⟨next, nextOrdered, nextFrame, route, routeGenerated, envEq, domainShape, bodyShape, rawEq,
      frameGenerated, frameEq, routeCharged, nextOccurrence, nextLedger, nextDomain⟩ :=
    display.nativePiCursorAmbient_counted shape ordered captured.toParameterReplyFrame.typeRouteFrame
      captured.generation captured.generation.ambient.2.below bodyOccurrence ledger
  refine ⟨next, nextOrdered,
    { locals := nextFrame.locals, available := nextFrame.available, realization := nextFrame.realization,
      capped := frameGenerated.capped, closed := nextFrame.closed, generation := frameGenerated },
    cursorNext next domainShape bodyShape, rawEq, frameEq, nextOccurrence, nextLedger, nextDomain⟩

open private Located.dependencyEnvironment_of_prefix_nil
  from Lean4Lean.Theory.Typing.AnchoredOriginalFamilyArgumentPair

/-- The successor retains its exact raw substitution from this concrete
predecessor, so all auxiliary declaration contexts share its actual owner. -/
theorem AmbientFamilyHistoryStage.advancePreservingRaw
    {major : EndpointRef sourceEnv U source majorExpression (mkApps (.const name levels) arguments)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {initial : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) initial raw}
    {frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight}
    {ordered : sourceEnv.Ordered} {registered : sourceEnv.projections name info}
    {levelsWF : ∀ level ∈ levels, level.WF U} {seed : ParameterRouteHeader sourceEnv U}
    {base : OriginalCaptureBase env U registry target}
    (stage : AmbientFamilyHistoryStage major field initial graph frame ordered registered levelsWF seed ownerInitial
      base caps domains tail index)
    (frameGenerated : AmbientCaptureGenerated base caps commonLeft commonRight graph frame.realization.frame.raw)
    (frameBound : environmentCost (frame.realization.frame.dependencyEnvironment ordered) ≤ environmentCost ownerInitial)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (bank : OriginalLowerCallBank env U registry limit)
    (scheduled : stage.history.schedule < limit)
    (remaining : index+1 < domains.length) (sourceLength : domains.length ≤ arguments.length) :
    ∃ next : AmbientFamilyHistoryStage major field initial graph frame ordered registered levelsWF seed ownerInitial
      base caps domains tail (index+1),
      next.header.raw = stage.header.raw.cons
        ((assignedFamilyRouteSide major initial graph index (List.getElem?_eq_getElem stage.selected)).a.subst
          (assignedFamilyRouteSide major initial graph index (List.getElem?_eq_getElem stage.selected)).raw) := by
  rcases stage with ⟨selected, header, history, generated, sourceFrameEq, headerBelow, telescope,
    charged, occurrence, ledger⟩
  rcases header with ⟨headerEnv, headerSource, C, D, cu, dv, hcu, hdv, headerDomainState, headerBody,
    headerRootSource, headerExpression, headerType, headerRoot, headerInitial, headerLocation, headerRaw, headerGraph⟩
  rcases history with ⟨leftOrdered, rightOrdered, leftBelow, headerDomain, headerDomainEq, sourceFrame, headerFrame, whole⟩
  change EndpointRef headerEnv U headerSource C (.sort cu) at headerDomain
  change headerDomainState = .ref headerDomain at headerDomainEq
  subst headerDomainState
  let left := assignedFamilyRouteSide major initial graph index (List.getElem?_eq_getElem selected)
  let right := originalNativePiRouteSide headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
  let history : OriginalApplyPiHistory env registry target commonLeft commonRight left right :=
    ⟨leftOrdered, rightOrdered, leftBelow, headerDomain, rfl, sourceFrame, headerFrame, whole⟩
  let sources := projectionRouteSources ordered registered levelsWF field major seed
  change sourceFrame = assignedFamilyRouteFrame major initial graph index (List.getElem?_eq_getElem selected) frame at sourceFrameEq
  have sourceBound : ∀ hf : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment hf) ≤
        environmentCost (left.location.dependencyEnvironment hf ownerInitial) := by
    intro hf
    change environmentCost (sourceFrame.realization.frame.dependencyEnvironment hf) ≤ _
    rw [sourceFrameEq, assignedFamilyRouteFrame_environment,
      Located.dependencyEnvironment_of_prefix_nil hf left.location
        (assignedFamilyRouteSide_prefix major initial graph index (List.getElem?_eq_getElem selected))]
    exact frameBound
  obtain ⟨replayed⟩ := history.baselineReplayAmbient (field := field) left.initial left.domain left.body left.function
    left.argument left.result left.hu left.hv left.location left.graph headerInitial headerDomain headerBody
    hcu hdv headerLocation headerGraph generated (assignedFamilyRouteSide_prefix major initial graph index
      (List.getElem?_eq_getElem selected)) sourceBound henv hscoped headerBelow formed
      bank scheduled
  have sourceNext := Nat.lt_of_lt_of_le remaining sourceLength
  let nextSelected : arguments[index+1]? = some arguments[index+1] := List.getElem?_eq_getElem sourceNext
  let next := assignedFamilyRouteSide major initial graph (index+1) nextSelected
  let nextFrame := assignedFamilyRouteFrame major initial graph (index+1) nextSelected frame
  have nextBound : environmentCost (nextFrame.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost (next.location.dependencyEnvironment ordered ownerInitial) := by
    rw [Located.dependencyEnvironment_of_prefix_nil ordered next.location
      (assignedFamilyRouteSide_prefix major initial graph (index+1) nextSelected), assignedFamilyRouteFrame_environment]
    exact frameBound
  obtain ⟨nextDomain, nextBody, headerShape, cursorNext⟩ := telescope.next remaining
  obtain ⟨nextHeader, nextHistory, nextGenerated, frameEq, _, below, domainEq, bodyEq, rawEq,
      ⟨nextCharged⟩, ⟨nextOccurrence⟩, ⟨nextLedger⟩⟩ := history.nextParameterAmbient_counted sources
    left.initial left.domain left.body left.function left.argument left.result left.hu left.hv left.location left.graph
    headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
    (assignedFamilyRouteSide_prefix major initial graph index (List.getElem?_eq_getElem selected)) ownerInitial
    sourceBound headerBelow generated replayed charged occurrence ledger
    next.domain next.body next.function next.argument next.result next.hu next.hv next.location next.graph nextFrame
    (assignedFamilyRouteFrame_ambientGenerated major initial graph (index+1) nextSelected frame frameGenerated) nextBound
    (assignedFamilyRouteSide_adjacent major initial graph index (List.getElem?_eq_getElem selected) nextSelected) headerShape
  exact ⟨⟨sourceNext, nextHeader, nextHistory, nextGenerated, frameEq, below,
    cursorNext nextHeader domainEq bodyEq, nextCharged, nextOccurrence, nextLedger⟩, rawEq⟩

/-- The family successor and every retained prefix are computed together
from this one actual predecessor. -/
theorem AmbientFamilyHistoryStage.advanceRetainedPrefixes
    {major : EndpointRef sourceEnv U source majorExpression (mkApps (.const name levels) arguments)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {initial : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) initial raw}
    {frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight}
    {ordered : sourceEnv.Ordered} {registered : sourceEnv.projections name info}
    {levelsWF : ∀ level ∈ levels, level.WF U} {seed : ParameterRouteHeader sourceEnv U}
    {base : OriginalCaptureBase env U registry target}
    (stage : AmbientFamilyHistoryStage major field initial graph frame ordered registered levelsWF seed ownerInitial
      base caps domains tail index)
    (frameGenerated : AmbientCaptureGenerated base caps commonLeft commonRight graph frame.realization.frame.raw)
    (frameBound : environmentCost (frame.realization.frame.dependencyEnvironment ordered) ≤ environmentCost ownerInitial)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (bank : OriginalLowerCallBank env U registry limit)
    (scheduled : stage.history.schedule < limit)
    (remaining : index+1 < domains.length) (sourceLength : domains.length ≤ arguments.length)
    {familyTrace : OriginalContextEquality baseEnv U commonSeedSource familySource}
    {universeTrace : OriginalContextEquality baseEnv U commonSeedSource commonRequestedSource}
    {ctorTrace : OriginalContextEquality typesEnv U commonRequestedSource ctorSource}
    (familySelected : familyTrace.Cell offset seedDomain stage.header.A)
    (universeSelected : universeTrace.Cell offset seedDomain requestedDomain)
    (ctorSelected : ctorTrace.Cell offset requestedDomain ctorDomain)
    (seedAt : commonSeedSource[offset]? = some seedDomain)
    (requestedAt : commonRequestedSource[offset]? = some requestedDomain)
    (baseOrdered : baseEnv.Ordered) (typesOrdered : typesEnv.Ordered)
    (seedState : AmbientTracePrefix (base := base) familyTrace (offset+1) stage.header.raw common caps
      commonLeft commonRight baseOrdered
      (projectionRouteSources ordered registered levelsWF field major seed) ownerInitial index)
    (universeState : AmbientTracePrefix (base := base) universeTrace (offset+1) stage.header.raw common caps
      commonLeft commonRight baseOrdered
      (projectionRouteSources ordered registered levelsWF field major seed) ownerInitial index)
    (requestedState : AmbientTracePrefix (base := base) ctorTrace (offset+1) stage.header.raw common caps
      commonLeft commonRight typesOrdered
      (projectionRouteSources ordered registered levelsWF field major seed) ownerInitial index)
    {ctorContext : ContextDerivation ctorEnv U headerSource}
    (ctorGraph : OriginalCaptureMap (common := common) ctorContext stage.header.raw)
    (constructor : EndpointRef ctorEnv U headerSource ctorDomain (.sort ctorLevel))
    (ctorProvenance : EndpointProvenance ctorContext (.ref constructor))
    (ctorOrdered : ctorEnv.Ordered)
    (ctorFrame : AmbientParameterReplyFrame base caps ctorGraph commonLeft commonRight)
    (familyLeft : ParameterRouteOccurrence (projectionRouteSources ordered registered levelsWF field major seed)
      baseOrdered (.ref (.left familySelected.original)))
    (familyRight : ParameterRouteOccurrence (projectionRouteSources ordered registered levelsWF field major seed)
      baseOrdered (.ref (.right familySelected.original)))
    (universeLeft : ParameterRouteOccurrence (projectionRouteSources ordered registered levelsWF field major seed)
      baseOrdered (.ref (.left universeSelected.original)))
    (universeRight : ParameterRouteOccurrence (projectionRouteSources ordered registered levelsWF field major seed)
      baseOrdered (.ref (.right universeSelected.original)))
    (ctorLeft : ParameterRouteOccurrence (projectionRouteSources ordered registered levelsWF field major seed)
      typesOrdered (.ref (.left ctorSelected.original)))
    (ctorRight : ParameterRouteOccurrence (projectionRouteSources ordered registered levelsWF field major seed)
      typesOrdered (.ref (.right ctorSelected.original)))
    (ctorOccurrence : ParameterRouteOccurrence (projectionRouteSources ordered registered levelsWF field major seed)
      ctorOrdered (.ref constructor))
    (ctorLedger : ParameterRouteLedger (projectionRouteSources ordered registered levelsWF field major seed)
      ownerInitial index (ctorFrame.realization.frame.dependencyEnvironment ctorOrdered))
    (paid : richSchedule .expressionReindex
      (2 * (projectionRouteSources ordered registered levelsWF field major seed).weight *
        parameterRouteCapacity (projectionRouteSources ordered registered levelsWF field major seed) index ownerInitial) < limit) :
    ∃ next : AmbientFamilyHistoryStage major field initial graph frame ordered registered levelsWF seed ownerInitial
      base caps domains tail (index+1),
      next.header.raw = stage.header.raw.cons
        ((assignedFamilyRouteSide major initial graph index (List.getElem?_eq_getElem stage.selected)).a.subst
          (assignedFamilyRouteSide major initial graph index (List.getElem?_eq_getElem stage.selected)).raw) ∧
      Nonempty (AmbientTracePrefix (base := base) familyTrace offset next.header.raw common caps commonLeft commonRight
        baseOrdered (projectionRouteSources ordered registered levelsWF field major seed) ownerInitial (index+1)) ∧
      Nonempty (AmbientTracePrefix (base := base) universeTrace offset next.header.raw common caps commonLeft commonRight
        baseOrdered (projectionRouteSources ordered registered levelsWF field major seed) ownerInitial (index+1)) ∧
      Nonempty (AmbientTracePrefix (base := base) ctorTrace offset next.header.raw common caps commonLeft commonRight
        typesOrdered (projectionRouteSources ordered registered levelsWF field major seed) ownerInitial (index+1)) ∧
      ∃ ctorCapture : AmbientParameterReplyFrame base caps
          (.capture ctorGraph constructor
            (assignedFamilyRouteSide major initial graph index (List.getElem?_eq_getElem stage.selected)).graph
            (assignedFamilyRouteSide major initial graph index (List.getElem?_eq_getElem stage.selected)).argument
            (.ofLocation (.appArgument (assignedFamilyRouteSide major initial graph index
              (List.getElem?_eq_getElem stage.selected)).location)
              (assignedFamilyRouteSide major initial graph index (List.getElem?_eq_getElem stage.selected)).initial))
          commonLeft commonRight,
        Nonempty (ParameterRouteLedger (projectionRouteSources ordered registered levelsWF field major seed)
          ownerInitial (index+1) (ctorCapture.realization.frame.dependencyEnvironment ctorOrdered)) := by
  let left := assignedFamilyRouteSide major initial graph index (List.getElem?_eq_getElem stage.selected)
  let sources := projectionRouteSources ordered registered levelsWF field major seed
  have sourceBound : ∀ hf : sourceEnv.Ordered,
      environmentCost (stage.history.sourceFrame.realization.frame.dependencyEnvironment hf) ≤
        environmentCost (left.location.dependencyEnvironment hf ownerInitial) := by
    intro hf
    rw [stage.sourceFrameEq, assignedFamilyRouteFrame_environment,
      Located.dependencyEnvironment_of_prefix_nil hf left.location
        (assignedFamilyRouteSide_prefix major initial graph index (List.getElem?_eq_getElem stage.selected))]
    exact frameBound
  obtain ⟨next, rawEq⟩ := stage.advancePreservingRaw frameGenerated frameBound henv hscoped formed bank scheduled remaining sourceLength
  obtain ⟨ctorCapture, capturedLedger, prefixes⟩ := stage.history.captureRetainedParameterPrefixesAmbient (field := field)
    left.initial left.domain left.body left.function left.argument left.result left.hu left.hv left.location left.graph
    (assignedFamilyRouteSide_prefix major initial graph index (List.getElem?_eq_getElem stage.selected)) sourceBound
    familySelected universeSelected ctorSelected seedAt requestedAt baseOrdered typesOrdered
    seed sources.requested sources rfl seedState universeState requestedState
    ctorGraph constructor ctorProvenance ctorOrdered ctorFrame stage.generated stage.charged stage.occurrence.piDomain
    familyLeft familyRight universeLeft universeRight ctorLeft ctorRight ctorOccurrence stage.ledger ctorLedger
    henv hscoped formed bank paid
  obtain ⟨nextSeed, nextUniverse, nextRequested⟩ := prefixes next.header.raw rawEq
  exact ⟨next, rawEq, nextSeed, nextUniverse, nextRequested, ctorCapture, capturedLedger⟩

/-- The equal-universe successor uses only the two retained context traces. -/
theorem AmbientFamilyHistoryStage.advanceRetainedSamePrefixes
    {major : EndpointRef sourceEnv U source majorExpression (mkApps (.const name levels) arguments)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {initial : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) initial raw}
    {frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight}
    {ordered : sourceEnv.Ordered} {registered : sourceEnv.projections name info}
    {levelsWF : ∀ level ∈ levels, level.WF U} {seed : ParameterRouteHeader sourceEnv U}
    {base : OriginalCaptureBase env U registry target}
    (stage : AmbientFamilyHistoryStage major field initial graph frame ordered registered levelsWF seed ownerInitial
      base caps domains tail index)
    (frameGenerated : AmbientCaptureGenerated base caps commonLeft commonRight graph frame.realization.frame.raw)
    (frameBound : environmentCost (frame.realization.frame.dependencyEnvironment ordered) ≤ environmentCost ownerInitial)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (bank : OriginalLowerCallBank env U registry limit)
    (scheduled : stage.history.schedule < limit)
    (remaining : index+1 < domains.length) (sourceLength : domains.length ≤ arguments.length)
    {familyTrace : OriginalContextEquality baseEnv U commonSeedSource familySource}
    {ctorTrace : OriginalContextEquality typesEnv U commonSeedSource ctorSource}
    (familySelected : familyTrace.Cell offset seedDomain stage.header.A)
    (ctorSelected : ctorTrace.Cell offset seedDomain ctorDomain)
    (seedAt : commonSeedSource[offset]? = some seedDomain)
    (baseOrdered : baseEnv.Ordered) (typesOrdered : typesEnv.Ordered)
    (seedState : AmbientTracePrefix (base := base) familyTrace (offset+1) stage.header.raw common caps
      commonLeft commonRight baseOrdered
      (projectionRouteSources ordered registered levelsWF field major seed) ownerInitial index)
    (requestedState : AmbientTracePrefix (base := base) ctorTrace (offset+1) stage.header.raw common caps
      commonLeft commonRight typesOrdered
      (projectionRouteSources ordered registered levelsWF field major seed) ownerInitial index)
    {ctorContext : ContextDerivation ctorEnv U headerSource}
    (ctorGraph : OriginalCaptureMap (common := common) ctorContext stage.header.raw)
    (constructor : EndpointRef ctorEnv U headerSource ctorDomain (.sort ctorLevel))
    (ctorProvenance : EndpointProvenance ctorContext (.ref constructor))
    (ctorOrdered : ctorEnv.Ordered)
    (ctorFrame : AmbientParameterReplyFrame base caps ctorGraph commonLeft commonRight)
    (familyLeft : ParameterRouteOccurrence (projectionRouteSources ordered registered levelsWF field major seed)
      baseOrdered (.ref (.left familySelected.original)))
    (familyRight : ParameterRouteOccurrence (projectionRouteSources ordered registered levelsWF field major seed)
      baseOrdered (.ref (.right familySelected.original)))
    (ctorLeft : ParameterRouteOccurrence (projectionRouteSources ordered registered levelsWF field major seed)
      typesOrdered (.ref (.left ctorSelected.original)))
    (ctorRight : ParameterRouteOccurrence (projectionRouteSources ordered registered levelsWF field major seed)
      typesOrdered (.ref (.right ctorSelected.original)))
    (ctorOccurrence : ParameterRouteOccurrence (projectionRouteSources ordered registered levelsWF field major seed)
      ctorOrdered (.ref constructor))
    (ctorLedger : ParameterRouteLedger (projectionRouteSources ordered registered levelsWF field major seed)
      ownerInitial index (ctorFrame.realization.frame.dependencyEnvironment ctorOrdered))
    (paid : richSchedule .expressionReindex
      (2 * (projectionRouteSources ordered registered levelsWF field major seed).weight *
        parameterRouteCapacity (projectionRouteSources ordered registered levelsWF field major seed) index ownerInitial) < limit) :
    ∃ next : AmbientFamilyHistoryStage major field initial graph frame ordered registered levelsWF seed ownerInitial
      base caps domains tail (index+1),
      next.header.raw = stage.header.raw.cons
        ((assignedFamilyRouteSide major initial graph index (List.getElem?_eq_getElem stage.selected)).a.subst
          (assignedFamilyRouteSide major initial graph index (List.getElem?_eq_getElem stage.selected)).raw) ∧
      Nonempty (AmbientTracePrefix (base := base) familyTrace offset next.header.raw common caps commonLeft commonRight
        baseOrdered (projectionRouteSources ordered registered levelsWF field major seed) ownerInitial (index+1)) ∧
      Nonempty (AmbientTracePrefix (base := base) ctorTrace offset next.header.raw common caps commonLeft commonRight
        typesOrdered (projectionRouteSources ordered registered levelsWF field major seed) ownerInitial (index+1)) ∧
      ∃ ctorCapture : AmbientParameterReplyFrame base caps
          (.capture ctorGraph constructor
            (assignedFamilyRouteSide major initial graph index (List.getElem?_eq_getElem stage.selected)).graph
            (assignedFamilyRouteSide major initial graph index (List.getElem?_eq_getElem stage.selected)).argument
            (.ofLocation (.appArgument (assignedFamilyRouteSide major initial graph index
              (List.getElem?_eq_getElem stage.selected)).location)
              (assignedFamilyRouteSide major initial graph index (List.getElem?_eq_getElem stage.selected)).initial))
          commonLeft commonRight,
        Nonempty (ParameterRouteLedger (projectionRouteSources ordered registered levelsWF field major seed)
          ownerInitial (index+1) (ctorCapture.realization.frame.dependencyEnvironment ctorOrdered)) := by
  let left := assignedFamilyRouteSide major initial graph index (List.getElem?_eq_getElem stage.selected)
  let sources := projectionRouteSources ordered registered levelsWF field major seed
  have sourceBound : ∀ hf : sourceEnv.Ordered,
      environmentCost (stage.history.sourceFrame.realization.frame.dependencyEnvironment hf) ≤
        environmentCost (left.location.dependencyEnvironment hf ownerInitial) := by
    intro hf
    rw [stage.sourceFrameEq, assignedFamilyRouteFrame_environment,
      Located.dependencyEnvironment_of_prefix_nil hf left.location
        (assignedFamilyRouteSide_prefix major initial graph index (List.getElem?_eq_getElem stage.selected))]
    exact frameBound
  obtain ⟨next, rawEq⟩ := stage.advancePreservingRaw frameGenerated frameBound henv hscoped formed bank scheduled remaining sourceLength
  obtain ⟨ctorCapture, capturedLedger, prefixes⟩ := stage.history.captureRetainedSameParameterPrefixesAmbient (field := field)
    left.initial left.domain left.body left.function left.argument left.result left.hu left.hv left.location left.graph
    (assignedFamilyRouteSide_prefix major initial graph index (List.getElem?_eq_getElem stage.selected)) sourceBound
    familySelected ctorSelected seedAt baseOrdered typesOrdered
    seed sources.requested sources rfl seedState requestedState
    ctorGraph constructor ctorProvenance ctorOrdered ctorFrame stage.generated stage.charged stage.occurrence.piDomain
    familyLeft familyRight ctorLeft ctorRight ctorOccurrence stage.ledger ctorLedger
    henv hscoped formed bank paid
  obtain ⟨nextSeed, nextRequested⟩ := prefixes next.header.raw rawEq
  exact ⟨next, rawEq, nextSeed, nextRequested, ctorCapture, capturedLedger⟩

/-- A complete nonfinal slot: one selected family successor, all three
retained-context prefixes, and the actual next constructor Pi header. -/
theorem AmbientFamilyHistoryStage.advanceSynchronizedParameterPrefixes
    {major : EndpointRef sourceEnv U source majorExpression (mkApps (.const name levels) arguments)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {initial : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) initial raw}
    {frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight}
    {ordered : sourceEnv.Ordered} {registered : sourceEnv.projections name info}
    {levelsWF : ∀ level ∈ levels, level.WF U} {seed : ParameterRouteHeader sourceEnv U}
    {base : OriginalCaptureBase env U registry target}
    (stage : AmbientFamilyHistoryStage major field initial graph frame ordered registered levelsWF seed ownerInitial
      base caps domains tail index)
    (frameGenerated : AmbientCaptureGenerated base caps commonLeft commonRight graph frame.realization.frame.raw)
    (frameBound : environmentCost (frame.realization.frame.dependencyEnvironment ordered) ≤ environmentCost ownerInitial)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (bank : OriginalLowerCallBank env U registry limit)
    (scheduled : stage.history.schedule < limit)
    (remaining : index+1 < domains.length) (sourceLength : domains.length ≤ arguments.length)
    {familyTrace : OriginalContextEquality baseEnv U commonSeedSource familySource}
    {universeTrace : OriginalContextEquality baseEnv U commonSeedSource commonRequestedSource}
    {ctorTrace : OriginalContextEquality typesEnv U commonRequestedSource ctorSource}
    (familySelected : familyTrace.Cell offset seedDomain stage.header.A)
    (universeSelected : universeTrace.Cell offset seedDomain requestedDomain)
    (ctorSelected : ctorTrace.Cell offset requestedDomain ctorDomain)
    (seedAt : commonSeedSource[offset]? = some seedDomain)
    (requestedAt : commonRequestedSource[offset]? = some requestedDomain)
    (baseOrdered : baseEnv.Ordered) (typesOrdered : typesEnv.Ordered)
    (seedState : AmbientTracePrefix (base := base) familyTrace (offset+1) stage.header.raw common caps
      commonLeft commonRight baseOrdered
      (projectionRouteSources ordered registered levelsWF field major seed) ownerInitial index)
    (universeState : AmbientTracePrefix (base := base) universeTrace (offset+1) stage.header.raw common caps
      commonLeft commonRight baseOrdered
      (projectionRouteSources ordered registered levelsWF field major seed) ownerInitial index)
    (requestedState : AmbientTracePrefix (base := base) ctorTrace (offset+1) stage.header.raw common caps
      commonLeft commonRight typesOrdered
      (projectionRouteSources ordered registered levelsWF field major seed) ownerInitial index)
    {ctorRoot : EndpointRef ctorEnv U ctorRootSource ctorExpression ctorType}
    (ctorInitial : ContextDerivation ctorEnv U ctorRootSource)
    (constructor : EndpointRef ctorEnv U headerSource ctorDomain (.sort ctorLevel))
    (ctorBody : EndpointState ctorEnv U (ctorDomain :: headerSource) ctorBodyExpression (.sort ctorBodyLevel))
    (ctorHu : ctorLevel.WF U) (ctorHv : ctorBodyLevel.WF U)
    (ctorLocation : Located ctorRoot (.pi ctorHu ctorHv (.ref constructor) ctorBody))
    (ctorGraph : OriginalCaptureMap (common := common) (ctorLocation.contextDerivation ctorInitial) stage.header.raw)
    (ctorOrdered : ctorEnv.Ordered)
    (ctorFrame : AmbientParameterReplyFrame base caps ctorGraph commonLeft commonRight)
    (ctorCursor : FamilyTelescopeCursor ctorDomains ctorTail index
      (originalNativePiRouteSide ctorInitial constructor ctorBody ctorHu ctorHv ctorLocation ctorGraph))
    (ctorRemaining : index+1 < ctorDomains.length)
    (familyLeft : ParameterRouteOccurrence (projectionRouteSources ordered registered levelsWF field major seed)
      baseOrdered (.ref (.left familySelected.original)))
    (familyRight : ParameterRouteOccurrence (projectionRouteSources ordered registered levelsWF field major seed)
      baseOrdered (.ref (.right familySelected.original)))
    (universeLeft : ParameterRouteOccurrence (projectionRouteSources ordered registered levelsWF field major seed)
      baseOrdered (.ref (.left universeSelected.original)))
    (universeRight : ParameterRouteOccurrence (projectionRouteSources ordered registered levelsWF field major seed)
      baseOrdered (.ref (.right universeSelected.original)))
    (ctorLeft : ParameterRouteOccurrence (projectionRouteSources ordered registered levelsWF field major seed)
      typesOrdered (.ref (.left ctorSelected.original)))
    (ctorRight : ParameterRouteOccurrence (projectionRouteSources ordered registered levelsWF field major seed)
      typesOrdered (.ref (.right ctorSelected.original)))
    (ctorOccurrence : ParameterRouteOccurrence (projectionRouteSources ordered registered levelsWF field major seed)
      ctorOrdered (originalNativePiRouteSide ctorInitial constructor ctorBody ctorHu ctorHv ctorLocation ctorGraph).display.node)
    (ctorLedger : ParameterRouteLedger (projectionRouteSources ordered registered levelsWF field major seed)
      ownerInitial index (ctorFrame.realization.frame.dependencyEnvironment ctorOrdered))
    (paid : richSchedule .expressionReindex
      (2 * (projectionRouteSources ordered registered levelsWF field major seed).weight *
        parameterRouteCapacity (projectionRouteSources ordered registered levelsWF field major seed) index ownerInitial) < limit) :
    ∃ next : AmbientFamilyHistoryStage major field initial graph frame ordered registered levelsWF seed ownerInitial
      base caps domains tail (index+1),
      next.header.raw = stage.header.raw.cons
        ((assignedFamilyRouteSide major initial graph index (List.getElem?_eq_getElem stage.selected)).a.subst
          (assignedFamilyRouteSide major initial graph index (List.getElem?_eq_getElem stage.selected)).raw) ∧
      Nonempty (AmbientTracePrefix (base := base) familyTrace offset next.header.raw common caps commonLeft commonRight
        baseOrdered (projectionRouteSources ordered registered levelsWF field major seed) ownerInitial (index+1)) ∧
      Nonempty (AmbientTracePrefix (base := base) universeTrace offset next.header.raw common caps commonLeft commonRight
        baseOrdered (projectionRouteSources ordered registered levelsWF field major seed) ownerInitial (index+1)) ∧
      Nonempty (AmbientTracePrefix (base := base) ctorTrace offset next.header.raw common caps commonLeft commonRight
        typesOrdered (projectionRouteSources ordered registered levelsWF field major seed) ownerInitial (index+1)) ∧
      ∃ nextCtor : OriginalPiTypeRouteSide U common,
      ∃ nextCtorOrdered : nextCtor.sourceEnv.Ordered,
      ∃ nextCtorFrame : AmbientParameterReplyFrame base caps nextCtor.graph commonLeft commonRight,
        FamilyTelescopeCursor ctorDomains ctorTail (index+1) nextCtor ∧
        nextCtor.raw = next.header.raw ∧
        Nonempty (ParameterRouteOccurrence (projectionRouteSources ordered registered levelsWF field major seed)
          nextCtorOrdered nextCtor.display.node) ∧
        Nonempty (ParameterRouteLedger (projectionRouteSources ordered registered levelsWF field major seed)
          ownerInitial (index+1) (nextCtorFrame.realization.frame.dependencyEnvironment nextCtorOrdered)) ∧
        ∃ nextDomain : EndpointRef nextCtor.sourceEnv U nextCtor.source nextCtor.A (.sort nextCtor.u),
          nextCtor.domain = .ref nextDomain := by
  let left := assignedFamilyRouteSide major initial graph index (List.getElem?_eq_getElem stage.selected)
  let ctorSide := originalNativePiRouteSide ctorInitial constructor ctorBody ctorHu ctorHv ctorLocation ctorGraph
  obtain ⟨next, rawEq, nextSeed, nextUniverse, nextRequested, ctorCapture, ⟨capturedLedger⟩⟩ :=
    stage.advanceRetainedPrefixes frameGenerated frameBound henv hscoped formed bank scheduled remaining sourceLength
      familySelected universeSelected ctorSelected seedAt requestedAt baseOrdered typesOrdered
      seedState universeState requestedState ctorGraph constructor
      (.ofLocation (.piDomain ctorLocation) ctorInitial) ctorOrdered ctorFrame
      familyLeft familyRight universeLeft universeRight ctorLeft ctorRight ctorOccurrence.piDomain ctorLedger paid
  obtain ⟨nextCtor, nextCtorOrdered, nextCtorFrame, cursorNext, ctorRaw, frameEq, nextOccurrence, nextLedger, nextDomain⟩ :=
    ctorSide.nextCapturedParameterAmbient constructor rfl left ctorOrdered ctorCapture ctorOccurrence capturedLedger
      ctorCursor ctorRemaining
  exact ⟨next, rawEq, nextSeed, nextUniverse, nextRequested, nextCtor, nextCtorOrdered, nextCtorFrame,
    cursorNext, ctorRaw.trans rawEq.symm, nextOccurrence, nextLedger, nextDomain⟩

/-- The same-universe nonfinal slot omits the unnecessary universe trace
while retaining the exact family and constructor successor selections. -/
theorem AmbientFamilyHistoryStage.advanceSynchronizedSameParameterPrefixes
    {major : EndpointRef sourceEnv U source majorExpression (mkApps (.const name levels) arguments)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {initial : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) initial raw}
    {frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight}
    {ordered : sourceEnv.Ordered} {registered : sourceEnv.projections name info}
    {levelsWF : ∀ level ∈ levels, level.WF U} {seed : ParameterRouteHeader sourceEnv U}
    {base : OriginalCaptureBase env U registry target}
    (stage : AmbientFamilyHistoryStage major field initial graph frame ordered registered levelsWF seed ownerInitial
      base caps domains tail index)
    (frameGenerated : AmbientCaptureGenerated base caps commonLeft commonRight graph frame.realization.frame.raw)
    (frameBound : environmentCost (frame.realization.frame.dependencyEnvironment ordered) ≤ environmentCost ownerInitial)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (bank : OriginalLowerCallBank env U registry limit)
    (scheduled : stage.history.schedule < limit)
    (remaining : index+1 < domains.length) (sourceLength : domains.length ≤ arguments.length)
    {familyTrace : OriginalContextEquality baseEnv U commonSeedSource familySource}
    {ctorTrace : OriginalContextEquality typesEnv U commonSeedSource ctorSource}
    (familySelected : familyTrace.Cell offset seedDomain stage.header.A)
    (ctorSelected : ctorTrace.Cell offset seedDomain ctorDomain)
    (seedAt : commonSeedSource[offset]? = some seedDomain)
    (baseOrdered : baseEnv.Ordered) (typesOrdered : typesEnv.Ordered)
    (seedState : AmbientTracePrefix (base := base) familyTrace (offset+1) stage.header.raw common caps
      commonLeft commonRight baseOrdered
      (projectionRouteSources ordered registered levelsWF field major seed) ownerInitial index)
    (requestedState : AmbientTracePrefix (base := base) ctorTrace (offset+1) stage.header.raw common caps
      commonLeft commonRight typesOrdered
      (projectionRouteSources ordered registered levelsWF field major seed) ownerInitial index)
    {ctorRoot : EndpointRef ctorEnv U ctorRootSource ctorExpression ctorType}
    (ctorInitial : ContextDerivation ctorEnv U ctorRootSource)
    (constructor : EndpointRef ctorEnv U headerSource ctorDomain (.sort ctorLevel))
    (ctorBody : EndpointState ctorEnv U (ctorDomain :: headerSource) ctorBodyExpression (.sort ctorBodyLevel))
    (ctorHu : ctorLevel.WF U) (ctorHv : ctorBodyLevel.WF U)
    (ctorLocation : Located ctorRoot (.pi ctorHu ctorHv (.ref constructor) ctorBody))
    (ctorGraph : OriginalCaptureMap (common := common) (ctorLocation.contextDerivation ctorInitial) stage.header.raw)
    (ctorOrdered : ctorEnv.Ordered)
    (ctorFrame : AmbientParameterReplyFrame base caps ctorGraph commonLeft commonRight)
    (ctorCursor : FamilyTelescopeCursor ctorDomains ctorTail index
      (originalNativePiRouteSide ctorInitial constructor ctorBody ctorHu ctorHv ctorLocation ctorGraph))
    (ctorRemaining : index+1 < ctorDomains.length)
    (familyLeft : ParameterRouteOccurrence (projectionRouteSources ordered registered levelsWF field major seed)
      baseOrdered (.ref (.left familySelected.original)))
    (familyRight : ParameterRouteOccurrence (projectionRouteSources ordered registered levelsWF field major seed)
      baseOrdered (.ref (.right familySelected.original)))
    (ctorLeft : ParameterRouteOccurrence (projectionRouteSources ordered registered levelsWF field major seed)
      typesOrdered (.ref (.left ctorSelected.original)))
    (ctorRight : ParameterRouteOccurrence (projectionRouteSources ordered registered levelsWF field major seed)
      typesOrdered (.ref (.right ctorSelected.original)))
    (ctorOccurrence : ParameterRouteOccurrence (projectionRouteSources ordered registered levelsWF field major seed)
      ctorOrdered (originalNativePiRouteSide ctorInitial constructor ctorBody ctorHu ctorHv ctorLocation ctorGraph).display.node)
    (ctorLedger : ParameterRouteLedger (projectionRouteSources ordered registered levelsWF field major seed)
      ownerInitial index (ctorFrame.realization.frame.dependencyEnvironment ctorOrdered))
    (paid : richSchedule .expressionReindex
      (2 * (projectionRouteSources ordered registered levelsWF field major seed).weight *
        parameterRouteCapacity (projectionRouteSources ordered registered levelsWF field major seed) index ownerInitial) < limit) :
    ∃ next : AmbientFamilyHistoryStage major field initial graph frame ordered registered levelsWF seed ownerInitial
      base caps domains tail (index+1),
      next.header.raw = stage.header.raw.cons
        ((assignedFamilyRouteSide major initial graph index (List.getElem?_eq_getElem stage.selected)).a.subst
          (assignedFamilyRouteSide major initial graph index (List.getElem?_eq_getElem stage.selected)).raw) ∧
      Nonempty (AmbientTracePrefix (base := base) familyTrace offset next.header.raw common caps commonLeft commonRight
        baseOrdered (projectionRouteSources ordered registered levelsWF field major seed) ownerInitial (index+1)) ∧
      Nonempty (AmbientTracePrefix (base := base) ctorTrace offset next.header.raw common caps commonLeft commonRight
        typesOrdered (projectionRouteSources ordered registered levelsWF field major seed) ownerInitial (index+1)) ∧
      ∃ nextCtor : OriginalPiTypeRouteSide U common,
      ∃ nextCtorOrdered : nextCtor.sourceEnv.Ordered,
      ∃ nextCtorFrame : AmbientParameterReplyFrame base caps nextCtor.graph commonLeft commonRight,
        FamilyTelescopeCursor ctorDomains ctorTail (index+1) nextCtor ∧
        nextCtor.raw = next.header.raw ∧
        Nonempty (ParameterRouteOccurrence (projectionRouteSources ordered registered levelsWF field major seed)
          nextCtorOrdered nextCtor.display.node) ∧
        Nonempty (ParameterRouteLedger (projectionRouteSources ordered registered levelsWF field major seed)
          ownerInitial (index+1) (nextCtorFrame.realization.frame.dependencyEnvironment nextCtorOrdered)) ∧
        ∃ nextDomain : EndpointRef nextCtor.sourceEnv U nextCtor.source nextCtor.A (.sort nextCtor.u),
          nextCtor.domain = .ref nextDomain := by
  let left := assignedFamilyRouteSide major initial graph index (List.getElem?_eq_getElem stage.selected)
  let ctorSide := originalNativePiRouteSide ctorInitial constructor ctorBody ctorHu ctorHv ctorLocation ctorGraph
  obtain ⟨next, rawEq, nextSeed, nextRequested, ctorCapture, ⟨capturedLedger⟩⟩ :=
    stage.advanceRetainedSamePrefixes frameGenerated frameBound henv hscoped formed bank scheduled remaining sourceLength
      familySelected ctorSelected seedAt baseOrdered typesOrdered
      seedState requestedState ctorGraph constructor
      (.ofLocation (.piDomain ctorLocation) ctorInitial) ctorOrdered ctorFrame
      familyLeft familyRight ctorLeft ctorRight ctorOccurrence.piDomain ctorLedger paid
  obtain ⟨nextCtor, nextCtorOrdered, nextCtorFrame, cursorNext, ctorRaw, frameEq, nextOccurrence, nextLedger, nextDomain⟩ :=
    ctorSide.nextCapturedParameterAmbient constructor rfl left ctorOrdered ctorCapture ctorOccurrence capturedLedger
      ctorCursor ctorRemaining
  exact ⟨next, rawEq, nextSeed, nextRequested, nextCtor, nextCtorOrdered, nextCtorFrame,
    cursorNext, ctorRaw.trans rawEq.symm, nextOccurrence, nextLedger, nextDomain⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
