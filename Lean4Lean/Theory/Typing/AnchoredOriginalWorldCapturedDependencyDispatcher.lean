import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCapturedDemandDispatcher
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDependencyReindexData

/-! Captured slots embed the already computed single-need answer into the
finite-trace result. The selected frame and its annotations are unchanged. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

theorem WorldGenerated.ReindexDemandAt.toDependency
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {controls : OriginalWorldControls strata sourceEnv}
    {generated : WorldGenerated strata P base caps commonLeft commonRight graph frame controls}
    (available : generated.ReindexDemandAt index) : generated.ReindexDependencyAt index := by
  intro frontier inRange replayable compatible ready hereditary valid substitutions
    destinationEnvironment destinationBaseline capacity covered
    callerSource callerExpression callerAssigned caller nextCommon nextLeft nextRight nextCaps rho insertion
    leftTail rightTail capsTail leftAssigned left leftControls sameCutoff sameFuel
    leftEnvironment leftBaseline leftLocals leftAvailable leftFrame leftData henv hscoped formed
    rank profile requestedFootprint requested requestedAvailable requestedReady sponsored bank unary
  obtain ⟨answer⟩ := available frontier replayable compatible ready hereditary valid substitutions
    destinationBaseline capacity covered caller insertion leftTail rightTail capsTail left leftControls
    sameCutoff sameFuel leftBaseline leftFrame leftData henv hscoped formed requested requestedAvailable
    requestedReady sponsored bank unary
  exact ⟨answer.toDependency⟩

theorem WorldGenerated.reindexCapturedDependency
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {controls : OriginalWorldControls strata sourceEnv}
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph frame controls)
    (captured : graph.CapturedIndex index) : generated.ReindexDependencyAt index :=
  (generated.reindexCapturedDemand captured).toDependency

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
