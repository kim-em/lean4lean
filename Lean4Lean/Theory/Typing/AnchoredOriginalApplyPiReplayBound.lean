import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiReplayData
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientReply
import Lean4Lean.Theory.Typing.AnchoredOriginalGroupBaselineBudget

/-! The connected application replay returns its original requested profile
at a fixed, query-independent captured-frame capacity. The preceding header
capacity alone cannot pay for the newly captured head. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

variable {left : OriginalApplicationTypeRouteSide U common}
  {right : OriginalPiTypeRouteSide U common}
  {history : OriginalApplyPiHistory env registry target commonLeft commonRight left right}
  {field : EndpointRef left.sourceEnv U left.source fieldExpression fieldType}
  {major : EndpointRef left.sourceEnv U left.source majorExpression majorType}
  {base : OriginalCaptureBase env U registry target}

/-- Both owner roots remain in the fixed envelope, including empty queries. -/
noncomputable def OriginalApplyPiHistory.outputEnvironment
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight left right)
    (field : EndpointRef left.sourceEnv U left.source fieldExpression fieldType)
    (major : EndpointRef left.sourceEnv U left.source majorExpression majorType)
    (ownerInitial : List Closure) : List Closure :=
  groupCaptureHistoryReserve field major history.rightDomain history.leftOrdered history.rightOrdered
    ownerInitial history.final history.argumentSeedReserve

theorem OriginalApplyPiReplayResult.environment_bound
    (result : OriginalApplyPiReplayResult history field major ownerInitial base commonCaps profile)
    (ordered : right.sourceEnv.Ordered) :
    environmentCost (result.reply.reply.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost (history.outputEnvironment field major ownerInitial) := by
  rw [result.environment_eq ordered]
  exact Nat.le_of_eq (result.whole.reply.answer.reply.realization.frame.historyGroup_environmentCost
    history.leftOrdered ordered result.entries history.final history.argumentSeedReserve
    (result.whole.reply.bounded ordered))

private theorem capturedBody_realized
    (left : OriginalApplicationTypeRouteSide U common)
    (right : OriginalPiTypeRouteSide U common) (realization : Subst) :
    (right.B.subst (right.raw.cons (left.a.subst left.raw))).subst realization =
      right.B.subst ((right.raw.comp realization).cons (left.a.subst (left.raw.comp realization))) := by
  rw [subst_subst]
  congr 1
  funext index
  cases index <;> simp only [Subst.comp, Subst.cons, subst_subst]

/-- Query, semantic code and raw conversion refer to the same captured body
and the same selected source frame. The output capacity includes its head. -/
noncomputable def OriginalApplyPiReplayResult.boundedReply
    (result : OriginalApplyPiReplayResult history field major ownerInitial base commonCaps profile) :
    BoundedParameterReply base commonCaps ((left.B.inst left.a).subst (left.raw.comp commonLeft))
      history.destination commonLeft commonRight profile
      (environmentCost (history.outputEnvironment field major ownerInitial)) where
  reply := ⟨result.reply, result.environment_bound⟩
  related := by
    change TypeRelated _ _ _ _ _ ((right.B.subst (right.raw.cons (left.a.subst left.raw))).subst commonLeft) _
    rw [capturedBody_realized]
    exact result.related
  path := by
    change TypeConversion _ _ _ _ ((right.B.subst (right.raw.cons (left.a.subst left.raw))).subst commonLeft)
    rw [capturedBody_realized]
    exact result.path

noncomputable def AmbientApplyPiReplayResult.boundedReply
    {left : OriginalApplicationTypeRouteSide U common}
    {right : OriginalPiTypeRouteSide U common}
    {history : OriginalApplyPiHistory env registry target commonLeft commonRight left right}
    {field : EndpointRef left.sourceEnv U left.source fieldExpression fieldType}
    {major : EndpointRef left.sourceEnv U left.source majorExpression majorType}
    {base : OriginalCaptureBase env U registry target}
    (result : AmbientApplyPiReplayResult history field major ownerInitial base commonCaps profile) :
    AmbientBoundedParameterReply base commonCaps ((left.B.inst left.a).subst (left.raw.comp commonLeft))
      history.destination commonLeft commonRight profile
      (environmentCost (history.outputEnvironment field major ownerInitial)) :=
  ⟨result.toOriginalApplyPiReplayResult.boundedReply, result.generation⟩


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
