import Lean4Lean.Verify.Inductive.Install.Ordinary

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The independent ordinary-inductive judgment produced by a successful
checker run, including the translation of the exact source syntax.  Keeping
the source translation beside `AddInduct` prevents a final-environment model
from silently being attributed to a different (for example, lowered)
declaration. -/
structure InductiveSpecificationResult
    (sourceEnv : VEnv) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe : Bool)
    (finalVEnv : VEnv) where
  decl : VInductDecl
  envTypes : VEnv
  envCtors : VEnv
  source : TrInductDeclCore sourceEnv lparams nparams sourceTypes isUnsafe
    decl envTypes envCtors
  extension : VEnv.AddInduct sourceEnv decl finalVEnv

/-- Ordinary runs and primitive-bootstrap runs share the same independent
source judgment; this alias documents the ordinary use site. -/
abbrev OrdinaryInductiveSpecificationResult := InductiveSpecificationResult

end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Uniform declaration-facing result for every inductive execution path.
It records a complete model of the exact returned environment, pointwise
extension of all source observers, and the independent specification of the
exact submitted source declaration, and preservation of the constructor
telescope certificate from the source environment to the returned one.
Equality bootstrap state is deliberately absent: it is not an
inductive-soundness precondition. -/
structure InductiveFinalResult
    (sourceEnv outEnv : Environment) (sourceModels : VEnvs)
    (lparams : List Name) (nparams : Nat) (sourceTypes : List InductiveType)
    (isUnsafe : Bool) where
  targetModels : VEnvs
  wf : targetModels.WFCore outEnv
  mono : ∀ safety, sourceModels.venv safety ≤ targetModels.venv safety
  specification : InductiveSpecificationResult
    (sourceModels.venv (if isUnsafe then .unsafe else .safe)) lparams nparams
    sourceTypes isUnsafe
    (targetModels.venv (if isUnsafe then .unsafe else .safe))
  certPres : VEnvs.CertPres sourceEnv outEnv sourceModels targetModels

/-- Construct the uniform result directly from the environment model and
independent source specification. -/
def InductiveFinalResult.ofModel
    (targetModels : VEnvs) (wf : targetModels.WFCore outEnv)
    (mono : ∀ safety, sourceModels.venv safety ≤ targetModels.venv safety)
    (specification : InductiveSpecificationResult
      (sourceModels.venv (if isUnsafe then .unsafe else .safe)) lparams
      nparams sourceTypes isUnsafe
      (targetModels.venv (if isUnsafe then .unsafe else .safe)))
    (certPres : VEnvs.CertPres sourceEnv outEnv sourceModels targetModels) :
    InductiveFinalResult sourceEnv outEnv sourceModels lparams nparams sourceTypes
      isUnsafe where
  targetModels := targetModels
  wf := wf
  mono := mono
  specification := specification
  certPres := certPres

/-- Forget the inductive-specific evidence and recover the traditional
environment-preservation postcondition used by `addDecl.WF`. -/
theorem InductiveFinalResult.modelExtension
    (H : InductiveFinalResult sourceEnv outEnv sourceModels lparams nparams sourceTypes
      isUnsafe) :
    ∃ targetModels : VEnvs, targetModels.WFCore outEnv ∧
      (∀ safety, sourceModels.venv safety ≤ targetModels.venv safety) ∧
      VEnvs.CertPres sourceEnv outEnv sourceModels targetModels :=
  ⟨H.targetModels, H.wf, H.mono, H.certPres⟩

end VerifyInductive
end Lean4Lean
