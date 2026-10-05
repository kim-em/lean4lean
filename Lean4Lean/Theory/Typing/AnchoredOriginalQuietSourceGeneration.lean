import Lean4Lean.Theory.Typing.AnchoredOriginalQuietSourceResults
import Lean4Lean.Theory.Typing.AnchoredOriginalBudgetedSourceCaptureGeneration

/-! This module is retained as an import compatibility boundary.

The former source-only quiet-depth declarations have been retired. A rich
delta observer may retain a genuine original definition body from the ambient
environment even when that body's mutual header is not included in the
observer endpoint's source environment. Source inclusion, including hereditary
frame source inclusion, therefore does not bound the depths of stored queries.

Operative replay must preserve the actual query controls and retained-query
annotations. No source-only quietness claim, nor an additional quietness
assumption on global outputs, is introduced here.
-/
