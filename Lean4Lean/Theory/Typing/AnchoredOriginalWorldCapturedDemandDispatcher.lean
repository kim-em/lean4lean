import Lean4Lean.Theory.Typing.AnchoredOriginalCapturedIndex
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDemandCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDemandStructural
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDemandSuffix
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDemandHistorySuffix
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldHistoryDemandDispatcher

/-! Structural variable reconstruction for every source-map slot whose path
reaches a captured owner. The IH is on the actual positive generation and is
uniform in common-scope insertion and the actual outer original caller. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000

private theorem WorldGenerated.capturedDemandInvariant
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {controls : OriginalWorldControls strata sourceEnv}
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph frame controls) :
    ∀ index, graph.CapturedIndex index → generated.ReindexDemandAt index := by
  induction generated with
  | merge _ _ first _ =>
    intro index captured
    exact (first index captured).merge
  | identity => intro index captured; exact False.elim captured
  | empty => intro index captured; exact False.elim captured
  | weaken generated insertion leftTail rightTail capsTail ih =>
    intro index captured
    exact WorldGenerated.ReindexDemandAt.weaken generated insertion leftTail rightTail capsTail (ih index captured)
  | bind generated baseline capacity domain annotation displayed certificate resources typed arguments needs bounded covered ih =>
    intro index captured
    cases index with
    | zero => exact False.elim captured
    | succ index =>
      exact WorldGenerated.ReindexDemandAt.bindTail generated baseline capacity domain annotation displayed
        certificate resources typed arguments needs bounded covered (ih index captured)
  | capture generated baseline capacity domain initial argument location lineage query queryAvailable queryBound queryAdapter
      certificate resources typed arguments needs bounded covered ih =>
    intro index captured
    cases index with
    | zero =>
      exact WorldGenerated.ReindexDemandAt.capture generated baseline capacity domain initial argument location lineage
        query queryAvailable queryBound queryAdapter certificate resources typed arguments needs bounded covered
    | succ index =>
      exact WorldGenerated.ReindexDemandAt.captureTail generated baseline capacity domain initial argument location lineage
        query queryAvailable queryBound queryAdapter certificate resources typed arguments needs bounded covered (ih index captured)
  | historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
      historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
      tailIH _ _ _ _ =>
    intro index captured
    cases index with
    | zero =>
      exact WorldGenerated.ReindexDemandAt.historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
        seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
        historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
        ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
    | succ index =>
      exact WorldGenerated.ReindexDemandAt.historyGroupTail generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
        seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
        historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
        ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
        (tailIH index captured)

/-- Execute the actual capture path at any variable index, including prefixes
of binders, captures, dormant groups, merges, and common-scope weakenings.
The computed path hypothesis distinguishes capture activation from the
separate cap-limited common-variable case; it supplies no semantic answer. -/
theorem WorldGenerated.reindexCapturedDemand
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {controls : OriginalWorldControls strata sourceEnv}
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph frame controls)
    (captured : graph.CapturedIndex index) : generated.ReindexDemandAt index :=
  generated.capturedDemandInvariant index captured

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
