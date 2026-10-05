import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientFamilyApplyPiChainLedger
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientFamilyApplyPiChainReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientFamilyFirstApplyPiLedger
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyTelescopeCursor

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail OriginalEndpointFactor.Dependency
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option Elab.async false

/-- One stage of the actual family spine. Earlier arguments are represented
by the nested finite history and its selected header frame; the next source
argument always comes from the original major's assigned formation. -/
structure AmbientFamilyHistoryStage
    (major : EndpointRef sourceEnv U source majorExpression (mkApps (.const name levels) arguments))
    (field : EndpointRef sourceEnv U source fieldExpression fieldType)
    (initial : ContextDerivation sourceEnv U source)
    (graph : OriginalCaptureMap (common := common) initial raw)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (ordered : sourceEnv.Ordered) (registered : sourceEnv.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (seed : ParameterRouteHeader sourceEnv U) (ownerInitial : List Closure)
    (base : OriginalCaptureBase env U registry target) (caps : CaptureCaps)
    (domains : List VExpr) (tail : VExpr) (index : Nat) where
  selected : index < arguments.length
  header : OriginalPiTypeRouteSide U common
  history : OriginalApplyPiHistory env registry target commonLeft commonRight
    (assignedFamilyRouteSide major initial graph index (List.getElem?_eq_getElem selected)) header
  generated : history.AmbientGenerated base caps
  sourceFrameEq : history.sourceFrame =
    assignedFamilyRouteFrame major initial graph index (List.getElem?_eq_getElem selected) frame
  headerBelow : header.sourceEnv ≤ env
  telescope : FamilyTelescopeCursor domains tail index header
  charged : history.whole.Charged
    (projectionRouteSources ordered registered levelsWF field major seed) ownerInitial index
  occurrence : ParameterRouteOccurrence
    (projectionRouteSources ordered registered levelsWF field major seed) history.rightOrdered header.display.node
  ledger : ParameterRouteLedger
    (projectionRouteSources ordered registered levelsWF field major seed) ownerInitial index history.final

open private Located.dependencyEnvironment_of_prefix_nil from Lean4Lean.Theory.Typing.AnchoredOriginalFamilyArgumentPair

/-- Advance one actual source/header slot. Its baseline is computed by the
original calls, and all new comparisons return with a counted source ledger. -/
theorem AmbientFamilyHistoryStage.advance
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
    Nonempty (AmbientFamilyHistoryStage major field initial graph frame ordered registered levelsWF seed ownerInitial
      base caps domains tail (index+1)) := by
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
  obtain ⟨nextHeader, nextHistory, nextGenerated, frameEq, _, below, domainEq, bodyEq, _,
      ⟨nextCharged⟩, ⟨nextOccurrence⟩, ⟨nextLedger⟩⟩ := history.nextParameterAmbient_counted sources
    left.initial left.domain left.body left.function left.argument left.result left.hu left.hv left.location left.graph
    headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
    (assignedFamilyRouteSide_prefix major initial graph index (List.getElem?_eq_getElem selected)) ownerInitial
    sourceBound headerBelow generated replayed charged occurrence ledger
    next.domain next.body next.function next.argument next.result next.hu next.hv next.location next.graph nextFrame
    (assignedFamilyRouteFrame_ambientGenerated major initial graph (index+1) nextSelected frame frameGenerated) nextBound
    (assignedFamilyRouteSide_adjacent major initial graph index (List.getElem?_eq_getElem selected) nextSelected) headerShape
  exact ⟨⟨sourceNext, nextHeader, nextHistory, nextGenerated, frameEq, below,
    cursorNext nextHeader domainEq bodyEq, nextCharged, nextOccurrence, nextLedger⟩⟩

section Projection
variable {ownerInitial : List Closure}
variable
  (ordered : sourceEnv.Ordered) (registered : sourceEnv.projections name info)
  (levelsWF : ∀ level ∈ levels, level.WF U) (levelCount : levels.length = info.uvars)
  (parameterCount : params.length = info.nparams) (indexCount : indices.length = info.nindices)
  (selectedField : info.fieldType name levels params fieldIndex sourceMajor = some fieldType)
  (fieldWF : fieldLevel.WF U)
  (field : EndpointRef sourceEnv U source fieldType (.sort fieldLevel))
  (major : Derivation sourceEnv U source sourceMajor majorExpression
    (VExpr.mkApps (.const name levels) (params ++ indices)))
  (closedConstructor : info.ctorType.Closed)
  (allowed : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero)
  {initial : ContextDerivation sourceEnv U source}
  {graph : OriginalCaptureMap (common := common) initial raw}
  {frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight}
  {seed : ParameterRouteHeader sourceEnv U}
  (seedBound : seed.weight ≤ (major.dependencyOrigin ordered).weight)
  {base : OriginalCaptureBase env U registry target}

set_option quotPrecheck false in
local notation "projectionCost" => richSchedule RichPhase.fundamental
  (Closure.close ((EndpointState.proj registered levelsWF levelCount parameterCount indexCount
    selectedField fieldWF (EndpointState.ref field) major closedConstructor allowed).dependencyOrigin ordered) ownerInitial).cost

include seedBound in
/-- The traversal pays every dynamically selected source/header baseline
from the production projection's finite declaration reserve. -/
theorem AmbientFamilyHistoryStage.projection_schedule
    (stage : AmbientFamilyHistoryStage (.left major) field initial graph frame ordered registered levelsWF seed ownerInitial
      base caps domains tail slot)
    (frameBound : environmentCost (frame.realization.frame.dependencyEnvironment ordered) ≤ environmentCost ownerInitial)
    (slotBound : slot ≤ info.nparams + max info.nindices fieldIndex) :
    stage.history.schedule < projectionCost := by
  let left := assignedFamilyRouteSide (.left major) initial graph slot (List.getElem?_eq_getElem stage.selected)
  let sources := projectionRouteSources ordered registered levelsWF field (.left major) seed
  have sourceBound : environmentCost (stage.history.sourceFrame.realization.frame.dependencyEnvironment stage.history.leftOrdered) ≤
      environmentCost (left.location.dependencyEnvironment ordered ownerInitial) := by
    rw [stage.sourceFrameEq, assignedFamilyRouteFrame_environment,
      Located.dependencyEnvironment_of_prefix_nil ordered left.location
        (assignedFamilyRouteSide_prefix (.left major) initial graph slot (List.getElem?_eq_getElem stage.selected))]
    exact frameBound
  let charges := stage.history.reserveCharged sources ownerInitial stage.charged (.major left.location)
    sourceBound stage.occurrence stage.ledger
  exact Nat.lt_of_le_of_lt stage.history.schedule_le
    (projection_route_charges_schedule ordered registered levelsWF levelCount parameterCount indexCount
      selectedField fieldWF field major closedConstructor allowed seed seedBound ownerInitial charges slotBound)

include seedBound in
/-- Finite recursion follows both actual spines. Each iteration computes its
empty baseline replay, grows exactly one counted capture slot, and derives
its original call schedule from the enclosing projection. -/
theorem AmbientFamilyHistoryStage.advanceMany
    (stage : AmbientFamilyHistoryStage (.left major) field initial graph frame ordered registered levelsWF seed ownerInitial
      base caps domains tail slot)
    (frameGenerated : AmbientCaptureGenerated base caps commonLeft commonRight graph frame.realization.frame.raw)
    (frameBound : environmentCost (frame.realization.frame.dependencyEnvironment ordered) ≤ environmentCost ownerInitial)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (bank : OriginalLowerCallBank env U registry projectionCost)
    (domainCount : domains.length = info.nparams)
    (steps : Nat) (remaining : slot + steps < domains.length) :
    Nonempty (AmbientFamilyHistoryStage (.left major) field initial graph frame ordered registered levelsWF seed ownerInitial
      base caps domains tail (slot + steps)) := by
  induction steps generalizing slot with
  | zero => exact ⟨stage⟩
  | succ steps ih =>
    have slotBound : slot ≤ info.nparams + max info.nindices fieldIndex := by omega
    have paid := stage.projection_schedule ordered registered levelsWF levelCount parameterCount indexCount
      selectedField fieldWF field major closedConstructor allowed seedBound frameBound slotBound
    have sourceLength : domains.length ≤ (params ++ indices).length := by
      simp only [List.length_append]
      omega
    obtain ⟨next⟩ := stage.advance frameGenerated frameBound henv hscoped formed bank paid (by omega) sourceLength
    have rest := ih next (by omega : slot + 1 + steps < domains.length)
    simpa only [Nat.add_assoc, Nat.add_comm 1 steps] using rest

/-- Every parameter position is reached by finite traversal of the actual
major application spine and the selected original normalized header. The
retained declaration seed and counted histories are shared by the result. -/
theorem familyHistoryTraversalAmbient
    (below : sourceEnv ≤ env) (positive : 0 < info.nparams)
    (frameGenerated : AmbientCaptureGenerated base caps commonLeft commonRight graph frame.realization.frame.raw)
    (frameBound : environmentCost (frame.realization.frame.dependencyEnvironment ordered) ≤ environmentCost ownerInitial)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (bank : OriginalLowerCallBank env U registry projectionCost) :
    ∃ selection : RichHeaderSelection sourceEnv U name levels ordered,
      ∃ retained : FamilyParameterLedger selection,
      retained.pairWeight ≤ (major.dependencyOrigin ordered).weight ∧
      let packet := selectProjectionParameters ordered registered selection.seedWF
      ∀ slot, slot < info.nparams →
        Nonempty (AmbientFamilyHistoryStage (.left major) field initial graph frame ordered registered levelsWF
          retained.routeHeader ownerInitial base caps
          (packet.shape.familyParams.map (·.instL selection.seed))
          (packet.shape.familyTail.instL selection.seed) slot) := by
  cases params with
  | nil => simp only [List.length_nil] at parameterCount; omega
  | cons argument rest =>
    obtain ⟨selection, retained, retainedBound, history, generated, sourceFrameEq,
        ⟨charged⟩, ⟨ledger⟩, ⟨occurrence⟩, headerBelow, _⟩ :=
      firstFamilyApplyPiHistoryAmbient_counted (.left major) field initial graph frame ordered below
        registered positive levelsWF ownerInitial frameBound frameGenerated
    let packet := selectProjectionParameters ordered registered selection.seedWF
    let domains := packet.shape.familyParams.map (·.instL selection.seed)
    let tail := packet.shape.familyTail.instL selection.seed
    have domainCount : domains.length = info.nparams := by
      exact (List.length_map _).trans (takeForalls_domains_length packet.shape.familyTake)
    let first : AmbientFamilyHistoryStage (.left major) field initial graph frame ordered registered levelsWF
        retained.routeHeader ownerInitial base caps domains tail 0 := {
      selected := by simp
      header := normalizedFamilyRouteSide packet positive common
      history := history
      generated := generated
      sourceFrameEq := sourceFrameEq
      headerBelow := headerBelow
      telescope := FamilyTelescopeCursor.initial packet positive common
      charged := charged
      occurrence := occurrence
      ledger := ledger }
    refine ⟨selection, retained, retainedBound, ?_⟩
    dsimp only
    intro slot slotBound
    have bounded := Nat.le_trans retained.routeHeader_weight_le_pairWeight retainedBound
    simpa only [Nat.zero_add] using first.advanceMany ordered registered levelsWF levelCount
      parameterCount indexCount selectedField fieldWF field major closedConstructor allowed bounded
      frameGenerated frameBound henv hscoped formed bank domainCount slot (by omega)

end Projection

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
