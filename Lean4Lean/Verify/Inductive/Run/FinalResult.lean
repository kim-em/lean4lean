import Lean4Lean.Verify.Inductive.Run.SemanticSpecification

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Uniform declaration-facing result for every inductive execution path.
It records a complete model of the exact returned environment, pointwise
extension of all source observers, and the independent specification of the
exact submitted source declaration. Equality bootstrap state is deliberately
absent: it is not an inductive-soundness precondition. -/
structure InductiveFinalResult
    (outEnv : Environment) (sourceModels : VEnvs)
    (lparams : List Name) (nparams : Nat) (sourceTypes : List InductiveType)
    (isUnsafe : Bool) where
  targetModels : VEnvs
  wf : targetModels.WF outEnv
  mono : ∀ safety, sourceModels.venv safety ≤ targetModels.venv safety
  specification : Nonempty (InductiveSpecificationResult
    (sourceModels.venv (if isUnsafe then .unsafe else .safe)) lparams nparams
    sourceTypes isUnsafe)

/-- Construct the uniform result directly from the environment model and
independent source specification. -/
def InductiveFinalResult.ofModel
    (targetModels : VEnvs) (wf : targetModels.WF outEnv)
    (mono : ∀ safety, sourceModels.venv safety ≤ targetModels.venv safety)
    (specification : Nonempty (InductiveSpecificationResult
      (sourceModels.venv (if isUnsafe then .unsafe else .safe)) lparams
      nparams sourceTypes isUnsafe)) :
    InductiveFinalResult outEnv sourceModels lparams nparams sourceTypes
      isUnsafe where
  targetModels := targetModels
  wf := wf
  mono := mono
  specification := specification

/-- Forget the inductive-specific evidence and recover the traditional
environment-preservation postcondition used by `addDecl.WF`. -/
theorem InductiveFinalResult.modelExtension
    (H : InductiveFinalResult outEnv sourceModels lparams nparams sourceTypes
      isUnsafe) :
    ∃ targetModels : VEnvs, targetModels.WF outEnv ∧
      ∀ safety, sourceModels.venv safety ≤ targetModels.venv safety :=
  ⟨H.targetModels, H.wf, H.mono⟩

end VerifyInductive
end Lean4Lean
