import Lean4Lean.Theory.Typing.AnchoredOriginalBoundedGeneratedReply
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFrameAmbient

/-! The concrete query-selected reply operations preserve hereditary owner
inclusion. In particular a finite union certifies its actual merged frame,
rather than substituting a separately chosen ambient answer. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

theorem GeneratedQueryReply.merge_frameAmbient
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    {p q : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (left : GeneratedQueryReply base display commonLeft commonRight p)
    (right : GeneratedQueryReply base display commonLeft commonRight q)
    (leftAmbient : left.realization.frame.Ambient)
    (rightAmbient : right.realization.frame.Ambient) :
    (left.merge henv hscoped formed right).reply.realization.frame.Ambient := by
  rcases left with ⟨leftLocals, leftAvailable, leftFrame, leftGenerated, leftQuery, leftClosed⟩
  rcases right with ⟨rightLocals, rightAvailable, rightFrame, rightGenerated, rightQuery, rightClosed⟩
  have localsEq : leftLocals = rightLocals :=
    leftGenerated.locals_eq.trans rightGenerated.locals_eq.symm
  cases localsEq
  exact leftAmbient.merge rightAmbient

theorem BoundedGeneratedQueryReply.union_frameAmbient
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    {p q : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (left : BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight p capacity)
    (right : BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight q capacity)
    (leftAmbient : left.answer.reply.realization.frame.Ambient)
    (rightAmbient : right.answer.reply.realization.frame.Ambient) :
    (left.union henv hscoped formed right).answer.reply.realization.frame.Ambient :=
  left.answer.reply.merge_frameAmbient henv hscoped formed right.answer.reply leftAmbient rightAmbient

theorem BoundedGeneratedQueryReply.mapQuery_frameAmbient
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    (reply : BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight requested capacity)
    (query : RichGradedResult display.sourceEnv env U registry target display.node reply.answer.reply.locals
      (display.raw.comp commonLeft) reply.answer.reply.available next)
    (ambient : reply.answer.reply.realization.frame.Ambient) :
    (reply.mapQuery query).answer.reply.realization.frame.Ambient := ambient

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
