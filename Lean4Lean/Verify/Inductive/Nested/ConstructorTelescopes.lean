import Lean4Lean.Verify.Inductive.Nested.ConstructorTypeRoundTrip
import Lean4Lean.Verify.Inductive.Constructor.Telescopes

/-!
# Telescope certificates of restored nested constructors

A successful nested run stores, for every source constructor, the restoration of the lowered
constructor type, which is `Expr.eqv` to the source type
(`NestedValidatedRunResult.installedConstructorSource`). The source type itself is checked by
`validateRestoredConstructorParameters.run` in the header-only validation environment, before
any environment containing the restored constructors is used by the checker; that run certifies
its telescope (`checkType.WF_telTr`), and `Expr.eqv` transports the certificate.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Every constructor visible after a successful validated nested run, and every constructor of
its constructor-validation environment, is certified in the source header environment. -/
theorem NestedValidatedRunResult.restoredCtorTelescopes
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceVEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Howners : ConstructorOwnersPresent sourceProdEnv)
    (henv : TypeChecker.EnvGF (fun _ => True) sourceProdEnv)
    (hbase : CtorTelescopes safety sourceProdEnv sourceVEnv) :
    CtorTelescopes safety outEnv E.nativeSource.envTypes ∧
      CtorTelescopes safety E.validationEnv E.nativeSource.envTypes := by
  sorry

end VerifyInductive
end Lean4Lean
