import Lean4Lean.Verify.Typing.Translation
import Lean4Lean.Verify.Inductive.Recursor.Context.ForallTelescope

/-! Applying a function to arguments along a translated forall telescope.

This module only collects imports. The de Bruijn lemmas that identify the source-side
instantiation of a forall body (`Expr.instantiateForallBody`) with `instantiateRevList` for
closed arguments, and `Expr.ForallTelescopeTypeTranslation.applyTranslatedArguments`, which
instantiates the source and abstract telescopes of a type with translated arguments in
lockstep, are in `Verify/Typing/Translation.lean`. -/
