import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCaptureHeadReplyData
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBoundedUnaryCallBank
import Lean4Lean.Theory.Typing.AnchoredOriginalCapturedVariableDisplay

/-! The structural destination capture-head motive keeps one fixed outer
comparison budget. Selecting a branch of a merge changes the admitted
frame, not that budget or either original endpoint. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- The actual original head variable displayed by a finite source map. -/
def captureHeadDisplay
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (node : EndpointState sourceEnv U source (.bvar 0) assigned)
    (provenance : EndpointProvenance context node) :
    OriginalNestedDisplay U common (raw 0) (assigned.subst raw) where
  sourceEnv := sourceEnv
  source := source
  sourceExpression := .bvar 0
  sourceType := assigned
  context := context
  node := node
  provenance := provenance
  raw := raw
  graph := graph
  expression_eq := rfl
  type_eq := rfl

/-- Actual head reconstruction under fixed source and destination budgets.
All child calls must be derived by the constructor implementation. -/
def WorldGenerated.ReindexHeadAt
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {controls : OriginalWorldControls strata sourceEnv}
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph frame controls) : Prop :=
  ∀ (frontier : List (World strata.rules.length)),
  generated.Replayable → generated.UsesControlPrefix controls.cutoff controls.fuel →
  generated.Controlled frontier → generated.Hereditary frontier →
  frame.Valid → Ctx.SubstEq env U target σ τ source →
  ∀ {destinationEnvironment : List Closure}
    (destinationBaseline : WorldEnvironmentProvenance strata U destinationEnvironment),
    environmentCost (frame.dependencyEnvironment controls.ordered) ≤ environmentCost destinationEnvironment →
    Covered (@EquationControlMeasure.Less strata.rules.length) generated.worlds destinationBaseline.worlds →
  ∀ {assigned : VExpr} (variableNode : EndpointState sourceEnv U source (.bvar 0) assigned)
    (variableProvenance : EndpointProvenance context variableNode)
    {leftAssigned : VExpr} (left : OriginalNestedDisplay U common (raw 0) leftAssigned)
    (leftControls : OriginalWorldControls strata left.sourceEnv),
    leftControls.cutoff = controls.cutoff → leftControls.fuel = controls.fuel →
  ∀ {leftEnvironment : List Closure} (leftBaseline : WorldEnvironmentProvenance strata U leftEnvironment)
    {leftLocals : List Nat} {leftAvailable : Valuation}
    (leftFrame : OriginalCaptureRealization left.graph env registry target leftLocals commonLeft commonRight leftAvailable),
    WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := left) leftControls leftBaseline frontier leftFrame →
    env.Ordered → registry.Scoped → OnCtx target (env.IsType U) →
  ∀ {n : Nat} {profile : Profile n} {footprint : Footprint}
    (query : RichObs left.sourceEnv env U registry target left.node leftLocals
      (left.raw.comp commonLeft) profile footprint),
    footprint.Available leftAvailable → ControlledStoredQuery leftControls frontier (.observation query) →
    Sponsored frontier
      [originalCallWorld leftControls .expressionReindex left.node leftBaseline,
        originalCallWorld controls .expressionReindex variableNode destinationBaseline] →
    WorldBoundedCallBank env U registry strata P (frontier ++
      [originalCallWorld leftControls .expressionReindex left.node leftBaseline,
        originalCallWorld controls .expressionReindex variableNode destinationBaseline]) →
    WorldBoundedUnaryCallBank env U registry strata P (frontier ++
      [originalCallWorld leftControls .expressionReindex left.node leftBaseline,
        originalCallWorld controls .expressionReindex variableNode destinationBaseline]) →
    ∃ reply : AmbientBoundedGeneratedQueryReply base caps
        (captureHeadDisplay graph variableNode variableProvenance) commonLeft commonRight profile
        (environmentCost destinationEnvironment),
      Nonempty (WorldCaptureHeadReplyData (P := P) controls generated.environment destinationBaseline frontier reply)

/-- Only a capture-map head has an extensible owner. The other graph
constructors belong to the common-variable and tail-index branches. -/
def WorldGenerated.CaptureHeadReindex
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {controls : OriginalWorldControls strata sourceEnv}
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph frame controls) : Prop :=
  match graph with
  | .capture .. => generated.ReindexHeadAt
  | _ => True

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
