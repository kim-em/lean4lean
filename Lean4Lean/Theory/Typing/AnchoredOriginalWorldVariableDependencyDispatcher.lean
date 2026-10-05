import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDependencyCommonLeaves
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCapturedDependencyDispatcher
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDependencyStructural
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDependencySuffix
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDependencyHistorySuffix

/-! Total variable reconstruction follows the actual positive generation.
Common and fresh variables use finite source-derived cap programs; capture
heads use their productive original replay; every upper frame is rebuilt
under the same immutable outer budget. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000

/-- The structural IH concerns only the actual generated child. The only
semantic recursion is already guarded inside the productive capture heads;
no completed variable reply or external demand-transfer callback is assumed. -/
theorem WorldGenerated.reindexVariableDependency
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {controls : OriginalWorldControls strata sourceEnv}
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph frame controls) :
    ∀ index, generated.ReindexDependencyAt index := by
  induction generated with
  | merge _ _ first _ =>
    intro index
    exact (first index).merge
  | identity ambient sources controls environment =>
    intro index
    exact WorldGenerated.ReindexDependencyAt.identity base ambient sources controls environment
  | empty =>
    intro index frontier inRange
    exact False.elim (Nat.not_lt_zero _ inRange)
  | weaken generated insertion leftTail rightTail capsTail ih =>
    intro index
    exact WorldGenerated.ReindexDependencyAt.weaken generated insertion leftTail rightTail capsTail (ih index)
  | bind generated baseline capacity domain annotation displayed certificate resources typed arguments needs bounded covered ih =>
    intro index
    cases index with
    | zero =>
      exact WorldGenerated.ReindexDependencyAt.bindHead generated baseline capacity domain annotation displayed
        certificate resources typed arguments needs bounded covered
    | succ index =>
      exact WorldGenerated.ReindexDependencyAt.bindTail generated baseline capacity domain annotation displayed
        certificate resources typed arguments needs bounded covered (ih index)
  | capture generated baseline capacity domain initial argument location lineage query queryAvailable queryBound queryAdapter
      certificate resources typed arguments needs bounded covered ih =>
    intro index
    cases index with
    | zero =>
      exact (WorldGenerated.ReindexDemandAt.capture generated baseline capacity domain initial argument location lineage
        query queryAvailable queryBound queryAdapter certificate resources typed arguments needs bounded covered).toDependency
    | succ index =>
      exact WorldGenerated.ReindexDependencyAt.captureTail generated baseline capacity domain initial argument location lineage
        query queryAvailable queryBound queryAdapter certificate resources typed arguments needs bounded covered (ih index)
  | historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
      historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
      tailIH _ _ _ _ =>
    intro index
    cases index with
    | zero =>
      exact (WorldGenerated.ReindexDemandAt.historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
        seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
        historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
        ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources).toDependency
    | succ index =>
      exact WorldGenerated.ReindexDependencyAt.historyGroupTail generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
        seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
        historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
        ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
        (tailIH index)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
