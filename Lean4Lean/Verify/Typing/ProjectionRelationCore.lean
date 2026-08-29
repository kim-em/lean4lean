import Lean4Lean.Verify.Typing.Projection

namespace Lean4Lean

open Lean

/-- Environment-indexed translation of a primitive projection to the
canonical eliminator term.  `EnvTrProj` is retained as the explicit-index
spelling for clients which should display the environment boundary. -/
abbrev EnvTrProj (env : VEnv) (U : Nat) (Gamma : List VExpr)
    (structName : Name) (index : Nat) (major target : VExpr) : Prop :=
  TrProj (env := env) (U := U) Gamma structName index major target

end Lean4Lean
