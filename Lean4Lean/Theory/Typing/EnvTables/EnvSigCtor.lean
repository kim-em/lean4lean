import Lean4Lean.Theory.Typing.EnvTables.EnvSigSchema
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.VLevel
import Lean4Lean.Theory.Typing.SchemaStructCompat

/-!
# Constructors of the semantic signature of a well-formed environment
-/

namespace Lean4Lean.EnvTables
open InductiveSignature

variable {env : VEnv}

theorem ctorOf_shape' (H : env.WF) (h : ctorOf env c = some k) : CtorShape env c k :=
  ctorOf_shape H h

/-! ## The constructor lists of families -/

end Lean4Lean.EnvTables
