import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCaptureMergePreservation
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldControlPrefix
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientReply
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldReplayableGeneration
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBaseHistory

/-! World evidence on the exact selected parameter reply. The retained
baseline is fixed independently of query-selected frame reorganization.
Both numeric capacity and actual world coverage are required. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false

structure WorldParameterReplyData
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {strata : EquationStratification env}
    {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    (controls : OriginalWorldControls strata display.sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (reply : AmbientBoundedParameterReply base caps start display commonLeft commonRight
      profile (environmentCost baselineEnvironment)) where
  generation : WorldGenerated strata P base caps commonLeft commonRight display.graph
    reply.reply.answer.reply.realization.frame.raw controls
  replayable : generation.Replayable
  controlled : generation.Controlled frontier
  compatible : generation.UsesControlPrefix controls.cutoff controls.fuel
  query : ControlledStoredQuery controls frontier (.observation reply.reply.answer.reply.query.observation)
  covered : Covered (@EquationControlMeasure.Less strata.rules.length) generation.worlds baseline.worlds
  hereditary : generation.Hereditary frontier

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
