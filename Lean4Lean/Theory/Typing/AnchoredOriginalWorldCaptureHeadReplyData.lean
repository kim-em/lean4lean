import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBoundedCallBank

/-! A reconstructed capture head keeps its actual local output bound as
well as the outer comparison admission. This permits later prefix rebuilding
without recovering demands from arbitrary charged recipe syntax. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

structure WorldCaptureHeadReplyData
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {display : OriginalNestedDisplay U common expression assigned}
    (controls : OriginalWorldControls strata display.sourceEnv)
    (localBaseline : WorldEnvironmentProvenance strata U localEnvironment)
    (outerBaseline : WorldEnvironmentProvenance strata U outerEnvironment)
    (frontier : List (World strata.rules.length))
    (reply : AmbientBoundedGeneratedQueryReply base caps display commonLeft commonRight requested
      (environmentCost outerEnvironment))
    (index : Nat := 0)
    extends WorldGeneratedQueryReplyData (P := P) controls outerBaseline frontier reply where
  localCapacity : ∀ ordered : display.sourceEnv.Ordered,
    environmentCost (reply.answer.reply.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost localEnvironment
  localCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
    generation.worlds localBaseline.worlds
  footprint : reply.answer.reply.query.footprint =
    [(index, Need.mk reply.answer.reply.query.rank reply.answer.reply.query.raw)]

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
