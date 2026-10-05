import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedCaptureReindex

/-! The original capture graph fixes local positions independently of query
selection. Only the finite available needs change when replies are combined. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

def OriginalCaptureMap.locals
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (initial : List Nat) : List Nat :=
  match graph with
  | .empty _ => []
  | .identity _ => initial
  | .tail previous => unpushLocals (previous.locals initial)
  | .capture previous _ _ _ _ => Locals.push (previous.locals initial)
  | .bind previous _ _ _ => Locals.push (previous.locals initial)
  | .weaken previous _ => previous.locals initial

theorem OriginalCaptureGenerated.locals_eq
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := base.source) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : OriginalCaptureGenerated base graph frame) :
    locals = graph.locals base.locals := by
  induction generated with
  | identity => rfl
  | empty => rfl
  | capture _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact congrArg Locals.push ih
  | group _ _ _ _ _ _ _ _ _ ih => exact congrArg Locals.push ih

theorem ScopedCaptureGenerated.locals_eq
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : ScopedCaptureGenerated base commonLeft commonRight graph frame) :
    locals = graph.locals base.locals := by
  induction generated with
  | tail generated valid ih =>
    exact ((OriginalRichFrame.mk _ valid).fullTail_locals).trans (congrArg unpushLocals ih)
  | merge _ _ first _ => exact first
  | reserveCapture _ _ ih => exact ih
  | reserveBind _ _ ih => exact ih
  | original generated => exact generated.locals_eq
  | empty => rfl
  | bind _ _ _ _ _ _ _ _ _ _ _ ih => exact congrArg Locals.push ih
  | weaken _ _ _ _ ih => exact ih
  | capture _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact congrArg Locals.push ih
  | group _ _ _ _ _ _ _ _ _ _ _ ih _ => exact congrArg Locals.push ih
  | scopedGroup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih _ _ => exact congrArg Locals.push ih

theorem GeneratedQueryReply.locals_eq
    (reply : GeneratedQueryReply base display commonLeft commonRight requested) :
    reply.locals = display.graph.locals base.locals :=
  reply.generated.locals_eq

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
