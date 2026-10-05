import Lean4Lean.Theory.Typing.AnchoredOriginalWorldParameterReply
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldStaticCallBounds

/-! The retained-route R/C motive is quantified at fixed original budgets.
Actual selected frames may reorganize captures at equal cost. Compatible
controls are explicit; this is not a claim about arbitrary foreign fuel.
The lower bank below is exactly the well-founded induction hypothesis, not
an independently supplied semantic interpretation theorem. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

structure WorldCallFrameData
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {display : OriginalNestedDisplay U common expression assigned}
    (controls : OriginalWorldControls strata display.sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (realization : OriginalCaptureRealization display.graph env registry target
      locals commonLeft commonRight available) where
  generation : WorldGenerated strata P base caps commonLeft commonRight display.graph realization.frame.raw controls
  replayable : generation.Replayable
  controlled : generation.Controlled frontier
  compatible : generation.UsesControlPrefix controls.cutoff controls.fuel
  closed : available.AtomClosed
  capacity : environmentCost (realization.frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment
  covered : Covered (@EquationControlMeasure.Less strata.rules.length) generation.worlds baseline.worlds
  hereditary : generation.Hereditary frontier

noncomputable def WorldParameterReplyData.callFrame
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {display : OriginalNestedDisplay U common expression assigned}
    {controls : OriginalWorldControls strata display.sourceEnv}
    {baseline : WorldEnvironmentProvenance strata U baselineEnvironment}
    {frontier : List (World strata.rules.length)}
    {reply : AmbientBoundedParameterReply base caps start display commonLeft commonRight profile
      (environmentCost baselineEnvironment)}
    (data : WorldParameterReplyData (P := P) controls baseline frontier reply) :
    WorldCallFrameData (P := P) (base := base) (caps := caps) controls baseline frontier
      reply.reply.answer.reply.realization where
  generation := data.generation
  replayable := data.replayable
  controlled := data.controlled
  compatible := data.compatible
  closed := reply.reply.answer.reply.closed
  capacity := reply.reply.bounded controls.ordered
  covered := data.covered
  hereditary := data.hereditary

theorem WorldCallFrameData.callBound
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {display : OriginalNestedDisplay U common expression assigned}
    {controls : OriginalWorldControls strata display.sourceEnv}
    {baseline : WorldEnvironmentProvenance strata U baselineEnvironment}
    {frontier : List (World strata.rules.length)}
    {realization : OriginalCaptureRealization display.graph env registry target
      locals commonLeft commonRight available}
    (data : WorldCallFrameData (P := P) (base := base) (caps := caps) controls baseline frontier realization)
    (phase : RichPhase) :
    BoundedNode (@EquationControlMeasure.Less strata.rules.length)
      (originalCallWorld controls phase display.node data.generation.environment)
      (originalCallWorld controls phase display.node baseline) :=
  originalCallWorld_boundedNode controls phase display.node data.generation.environment baseline data.capacity data.covered

theorem WorldCallFrameData.nodeCallBound
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {display : OriginalNestedDisplay U common expression assigned}
    {controls : OriginalWorldControls strata display.sourceEnv}
    {baseline : WorldEnvironmentProvenance strata U baselineEnvironment}
    {frontier : List (World strata.rules.length)}
    {realization : OriginalCaptureRealization display.graph env registry target
      locals commonLeft commonRight available}
    (data : WorldCallFrameData (P := P) (base := base) (caps := caps) controls baseline frontier realization)
    (node : EndpointState display.sourceEnv U display.source expression assigned)
    (phase : RichPhase) :
    BoundedNode (@EquationControlMeasure.Less strata.rules.length)
      (originalCallWorld controls phase node data.generation.environment)
      (originalCallWorld controls phase node baseline) :=
  originalCallWorld_boundedNode controls phase node data.generation.environment baseline data.capacity data.covered

theorem WorldCallFrameData.fundamentalBelowReindex
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {display : OriginalNestedDisplay U common expression assigned}
    {controls : OriginalWorldControls strata display.sourceEnv}
    {baseline : WorldEnvironmentProvenance strata U baselineEnvironment}
    {frontier : List (World strata.rules.length)}
    {realization : OriginalCaptureRealization display.graph env registry target
      locals commonLeft commonRight available}
    (data : WorldCallFrameData (P := P) (base := base) (caps := caps) controls baseline frontier realization) :
    WorldBelow strata.rules.length
      (originalCallWorld controls .fundamental display.node data.generation.environment)
      (originalCallWorld controls .expressionReindex display.node baseline) := by
  apply BoundedNode.child (r := @EquationControlMeasure.Less strata.rules.length)
    EquationControlMeasure.less_trans (data.callBound .expressionReindex)
  apply original_child
  simp only [richSchedule, RichPhase.code]
  omega

structure WorldGeneratedQueryReplyData
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {display : OriginalNestedDisplay U common expression assigned}
    (controls : OriginalWorldControls strata display.sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (reply : AmbientBoundedGeneratedQueryReply base caps display commonLeft commonRight
      profile (environmentCost baselineEnvironment)) where
  generation : WorldGenerated strata P base caps commonLeft commonRight display.graph
    reply.answer.reply.realization.frame.raw controls
  replayable : generation.Replayable
  controlled : generation.Controlled frontier
  compatible : generation.UsesControlPrefix controls.cutoff controls.fuel
  query : ControlledStoredQuery controls frontier (.observation reply.answer.reply.query.observation)
  covered : Covered (@EquationControlMeasure.Less strata.rules.length) generation.worlds baseline.worlds
  hereditary : generation.Hereditary frontier

/-- Fixed-budget compatible-control clauses needed by retained type routes.
The output carries world evidence for exactly the selected semantic reply. -/
structure WorldBoundedReplayAt
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (strata : EquationStratification env) (P : VEnv → Prop)
    (budget : List (World strata.rules.length)) : Prop where
  observation :
    ∀ {target : List VExpr} (base : OriginalCaptureBase env U registry target) (caps : CaptureCaps),
    ∀ {common : List VExpr} {expression leftAssigned rightAssigned : VExpr},
    ∀ (left : OriginalNestedDisplay U common expression leftAssigned)
      (right : OriginalNestedDisplay U common expression rightAssigned)
      (commonLeft commonRight : Subst)
      (leftControls : OriginalWorldControls strata left.sourceEnv)
      (rightControls : OriginalWorldControls strata right.sourceEnv),
    leftControls.cutoff = rightControls.cutoff → leftControls.fuel = rightControls.fuel →
    ∀ {leftEnvironment rightEnvironment}
      (leftBaseline : WorldEnvironmentProvenance strata U leftEnvironment)
      (rightBaseline : WorldEnvironmentProvenance strata U rightEnvironment)
      (frontier : List (World strata.rules.length)),
    frontier ++ [originalCallWorld leftControls .expressionReindex left.node leftBaseline,
      originalCallWorld rightControls .expressionReindex right.node rightBaseline] = budget →
    Sponsored frontier [originalCallWorld leftControls .expressionReindex left.node leftBaseline,
      originalCallWorld rightControls .expressionReindex right.node rightBaseline] →
    ∀ {leftLocals leftAvailable}
      (leftFrame : OriginalCaptureRealization left.graph env registry target leftLocals commonLeft commonRight leftAvailable),
    WorldCallFrameData (P := P) (base := base) (caps := caps) leftControls leftBaseline frontier leftFrame →
    ∀ {rightLocals rightAvailable}
      (rightFrame : OriginalCaptureRealization right.graph env registry target rightLocals commonLeft commonRight rightAvailable),
    WorldCallFrameData (P := P) (base := base) (caps := caps) rightControls rightBaseline frontier rightFrame →
    ∀ {n : Nat} {profile : Profile n} {footprint : Footprint}
      (query : RichObs left.sourceEnv env U registry target left.node leftLocals (left.raw.comp commonLeft) profile footprint),
    footprint.Available leftAvailable → ControlledStoredQuery leftControls frontier (.observation query) →
    ∃ reply : AmbientBoundedGeneratedQueryReply base caps right commonLeft commonRight profile
        (environmentCost rightEnvironment),
      Nonempty (WorldGeneratedQueryReplyData (P := P) rightControls rightBaseline frontier reply)
  assigned :
    ∀ {target : List VExpr} (base : OriginalCaptureBase env U registry target) (caps : CaptureCaps),
    ∀ {common : List VExpr} {expression leftAssigned rightAssigned : VExpr},
    ∀ (left : OriginalNestedDisplay U common expression leftAssigned)
      (right : OriginalNestedDisplay U common expression rightAssigned)
      (commonLeft commonRight : Subst)
      (leftControls : OriginalWorldControls strata left.sourceEnv)
      (rightControls : OriginalWorldControls strata right.sourceEnv),
    leftControls.cutoff = rightControls.cutoff → leftControls.fuel = rightControls.fuel →
    ∀ {leftEnvironment rightEnvironment}
      (leftBaseline : WorldEnvironmentProvenance strata U leftEnvironment)
      (rightBaseline : WorldEnvironmentProvenance strata U rightEnvironment)
      (frontier : List (World strata.rules.length)),
    frontier ++ [originalCallWorld leftControls .assignedComparison left.node leftBaseline,
      originalCallWorld rightControls .assignedComparison right.node rightBaseline] = budget →
    Sponsored frontier [originalCallWorld leftControls .assignedComparison left.node leftBaseline,
      originalCallWorld rightControls .assignedComparison right.node rightBaseline] →
    ∀ {leftLocals leftAvailable}
      (leftFrame : OriginalCaptureRealization left.graph env registry target leftLocals commonLeft commonRight leftAvailable),
    WorldCallFrameData (P := P) (base := base) (caps := caps) leftControls leftBaseline frontier leftFrame →
    ∀ {rightLocals rightAvailable}
      (rightFrame : OriginalCaptureRealization right.graph env registry target rightLocals commonLeft commonRight rightAvailable),
    WorldCallFrameData (P := P) (base := base) (caps := caps) rightControls rightBaseline frontier rightFrame →
    ∀ {n : Nat} {profile : Profile n} {footprint : Footprint} {relevant : Bool}
      (query : RichCert left.sourceEnv env U registry target left.node.typeFormation.node leftLocals
        (left.raw.comp commonLeft) relevant profile footprint),
    footprint.Available leftAvailable → ControlledStoredQuery leftControls frontier (.certificate query) →
    ∃ reply : AmbientBoundedParameterReply base caps (leftAssigned.subst commonLeft)
        right.formationDisplay commonLeft commonRight profile (environmentCost rightEnvironment),
      Nonempty (WorldParameterReplyData (P := P) (display := right.formationDisplay) rightControls rightBaseline frontier reply)

/-- Exactly the lower induction hypothesis; no equality-cost actual-world
comparison is requested from the caller. The strict edge is on retained
budgets, and each semantic clause receives the actual admissible frames. -/
def WorldBoundedCallBank
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (strata : EquationStratification env) (P : VEnv → Prop)
    (parent : List (World strata.rules.length)) : Prop :=
  ∀ retained, CallBelow strata.rules.length retained parent →
    WorldBoundedReplayAt env U registry strata P retained

/-- Select the exact retained R budget from the genuine lower IH. -/
noncomputable def WorldBoundedCallBank.observation
    (bank : WorldBoundedCallBank env U registry strata P parent)
    (retained : List (World strata.rules.length))
    (reserved : CallBelow strata.rules.length retained parent) :=
  @WorldBoundedReplayAt.observation env U registry strata P retained (bank retained reserved)

/-- Select the exact retained assigned-comparison budget from the lower IH. -/
noncomputable def WorldBoundedCallBank.assigned
    (bank : WorldBoundedCallBank env U registry strata P parent)
    (retained : List (World strata.rules.length))
    (reserved : CallBelow strata.rules.length retained parent) :=
  @WorldBoundedReplayAt.assigned env U registry strata P retained (bank retained reserved)

/-- This is the precise outstanding mutual producer obligation, expressed
without a supplied semantic answer or a new reserve envelope. -/
theorem worldBoundedReplay_induction
    (step : ∀ retained, WorldBoundedCallBank env U registry strata P retained →
      WorldBoundedReplayAt env U registry strata P retained) :
    ∀ retained, WorldBoundedReplayAt env U registry strata P retained := by
  intro retained
  induction retained using (call_wellFounded strata.rules.length).induction with
  | h retained ih => exact step retained ih

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
