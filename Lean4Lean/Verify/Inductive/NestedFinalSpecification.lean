import Lean4Lean.Verify.Inductive.Nested.FinalEnvironmentModels

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Proposition-facing form of `independentSpecification`, convenient at
`Except.WF` and declaration-dispatch boundaries. -/
theorem NestedFinalEnvironmentResult.hasIndependentSpecification
    (H : NestedFinalEnvironmentResult sourceEnv decl lparams nparams
      sourceTypes isUnsafe safety outEnv) :
    Nonempty (InductiveSpecificationResult sourceEnv lparams nparams
      sourceTypes isUnsafe) :=
  ⟨H.independentSpecification⟩

end VerifyInductive
end Lean4Lean
