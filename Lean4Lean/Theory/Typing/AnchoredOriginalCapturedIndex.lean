import Lean4Lean.Theory.Typing.AnchoredOriginalSourceCaptureSyntax

/-! A computed source-map path distinguishes extensible captured variables
from the common variables supplied by an identity base or fresh binder. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv OriginalEndpointFactor OriginalClosureMeasure
set_option Elab.async false

/-- This exact source slot eventually reaches a retained captured owner. -/
def OriginalCaptureMap.CapturedIndex
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw) (index : Nat) : Prop :=
  match graph with
  | .empty _ => False
  | .identity _ => False
  | .tail graph => graph.CapturedIndex (index + 1)
  | .capture graph _ _ _ _ =>
    match index with
    | 0 => True
    | index + 1 => graph.CapturedIndex index
  | .bind graph _ _ _ =>
    match index with
    | 0 => False
    | index + 1 => graph.CapturedIndex index
  | .weaken graph _ => graph.CapturedIndex index

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
