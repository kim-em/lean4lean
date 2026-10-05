import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDependencyData
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBoundedUnaryCallBank

/-! The variable-demand induction retains the actual outer original caller
and permits arbitrary common-scope insertion. Its answer is at the original
unweakened graph, so recursive bind and weaken cases can rebuild exact maps
without synthesizing shorter-context original nodes. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

def WorldGenerated.ReindexDependencyAt
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {controls : OriginalWorldControls strata sourceEnv}
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph frame controls) (index : Nat) : Prop :=
  ∀ (frontier : List (World strata.rules.length)), index < source.length →
  generated.Replayable → generated.UsesControlPrefix controls.cutoff controls.fuel →
  generated.Controlled frontier → generated.Hereditary frontier →
  frame.Valid → Ctx.SubstEq env U target σ τ source →
  ∀ {destinationEnvironment : List Closure}
    (destinationBaseline : WorldEnvironmentProvenance strata U destinationEnvironment),
    environmentCost (frame.dependencyEnvironment controls.ordered) ≤ environmentCost destinationEnvironment →
    Covered (@EquationControlMeasure.Less strata.rules.length) generated.worlds destinationBaseline.worlds →
  ∀ {callerSource : List VExpr} {callerExpression callerAssigned : VExpr}
    (caller : EndpointState sourceEnv U callerSource callerExpression callerAssigned)
    {nextCommon : List VExpr} {nextLeft nextRight : Subst} {nextCaps : CaptureCaps}
    {ρ : Lift} (insertion : Ctx.Lift' ρ common nextCommon),
    Subst.lift_l ρ nextLeft = commonLeft →
    Subst.lift_l ρ nextRight = commonRight →
    (fun i => nextCaps (ρ.liftVar i)) = caps →
  ∀ {leftAssigned : VExpr} (left : OriginalNestedDisplay U nextCommon ((raw index).lift' ρ) leftAssigned)
    (leftControls : OriginalWorldControls strata left.sourceEnv),
    leftControls.cutoff = controls.cutoff → leftControls.fuel = controls.fuel →
  ∀ {leftEnvironment : List Closure} (leftBaseline : WorldEnvironmentProvenance strata U leftEnvironment)
    {leftLocals : List Nat} {leftAvailable : Valuation}
    (leftFrame : OriginalCaptureRealization left.graph env registry target leftLocals nextLeft nextRight leftAvailable),
    WorldCallFrameData (P := P) (base := base) (caps := nextCaps)
      (display := left) leftControls leftBaseline frontier leftFrame →
    env.Ordered → registry.Scoped → OnCtx target (env.IsType U) →
  ∀ {n : Nat} {profile : Profile n} {footprint : Footprint}
    (query : RichObs left.sourceEnv env U registry target left.node leftLocals
      (left.raw.comp nextLeft) profile footprint),
    footprint.Available leftAvailable → ControlledStoredQuery leftControls frontier (.observation query) →
    Sponsored frontier
      [originalCallWorld leftControls .expressionReindex left.node leftBaseline,
        originalCallWorld controls .expressionReindex caller destinationBaseline] →
    WorldBoundedCallBank env U registry strata P (frontier ++
      [originalCallWorld leftControls .expressionReindex left.node leftBaseline,
        originalCallWorld controls .expressionReindex caller destinationBaseline]) →
    WorldBoundedUnaryCallBank env U registry strata P (frontier ++
      [originalCallWorld leftControls .expressionReindex left.node leftBaseline,
        originalCallWorld controls .expressionReindex caller destinationBaseline]) →
    Nonempty (WorldVariableDependencyReply P base caps graph commonLeft commonRight controls
      generated.environment frontier index profile)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
