import Lean4Lean.Verify.Expr

/-! # The safety level of an inductive declaration

`safetyOf isUnsafe` is notation for `if isUnsafe then .unsafe else .safe`, the safety level at
which a declaration with the given `isUnsafe` flag is checked and at which its model is read
(`VEnvs.venv`). It is notation, not a definition: a statement written with it is syntactically
the statement written with the conditional. -/

namespace Lean4Lean

/-- `safetyOf isUnsafe` is `if isUnsafe then .unsafe else .safe`. -/
notation:max "safetyOf " b:max =>
  (ite (b = true) Lean.DefinitionSafety.unsafe Lean.DefinitionSafety.safe)

end Lean4Lean
