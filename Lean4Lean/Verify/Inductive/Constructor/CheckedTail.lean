import Lean4Lean.Verify.Inductive.Header.Installation
import Lean4Lean.Verify.Inductive.Constructor.SourceSignature

/-! # The checked tail of a constructor

`CheckedCtorTail`: a constructor type is definitionally a telescope over the common parameters
ending in a constructor tail certified by the executable check (`checkConstructors`), with the
field classification it returned. The constructor check records one per constructor
(`ConstructorCheck.tails`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The checked tail of one constructor `ctor` of `target`: its type is definitionally a
telescope over a parameter list `ps` (definitionally the common parameters `params`) ending in
a constructor tail certified by the executable check, with the field classification `classes`
the positivity check returned. -/
def CheckedCtorTail (env : VEnv) (decl : VInductDecl) (params : List VExpr)
    (target : VInductiveType) (ctor : VConstVal) (classes : List Bool) : Prop :=
  ∃ ps tail, env.IsDefEqCtx decl.uvars [] params.reverse ps.reverse ∧
    env.IsDefEqU decl.uvars [] ctor.type (VExpr.wrapForalls ps tail) ∧
    ConstructorTailCertificate env decl target ps.reverse 0 tail classes

end VerifyInductive
end Lean4Lean
