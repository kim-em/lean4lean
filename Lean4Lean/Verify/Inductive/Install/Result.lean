import Lean4Lean.Verify.Inductive.Install.Ordinary

/-! The result shared by every inductive execution path: the source-facing
`SourceAddInduct` and the declaration-level `InductiveExtension`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The independent ordinary-inductive judgment produced by a successful
checker run, including the translation of the exact source syntax.  Keeping
the source translation beside `AddInduct` prevents an installed-environment model
from silently being attributed to a different (for example, lowered)
declaration. -/
structure SourceAddInduct
    (sourceEnv : VEnv) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe : Bool)
    (installedVEnv : VEnv) where
  decl : VInductDecl
  envTypes : VEnv
  envCtors : VEnv
  source : TrInductDeclCore sourceEnv lparams nparams sourceTypes isUnsafe
    decl envTypes envCtors
  extension : VEnv.AddInduct sourceEnv decl installedVEnv

/-- Ordinary runs and primitive runs (`Bool`, `Nat`) share the same independent
source judgment; this alias documents the ordinary use site. -/
abbrev OrdinarySourceAddInduct := SourceAddInduct

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
Whether the prelude `Eq` is present is deliberately not recorded: it is not
an inductive-soundness precondition. -/
structure InductiveExtension
    (sourceEnv outEnv : Environment) (sourceModels : VEnvs)
    (lparams : List Name) (nparams : Nat) (sourceTypes : List InductiveType)
    (isUnsafe : Bool) where
  targetModels : VEnvs
  wf : targetModels.WFCore outEnv
  mono : ∀ safety, sourceModels.venv safety ≤ targetModels.venv safety
  specification : SourceAddInduct
    (sourceModels.venv (if isUnsafe then .unsafe else .safe)) lparams nparams
    sourceTypes isUnsafe
    (targetModels.venv (if isUnsafe then .unsafe else .safe))
  ctorTelescopesPreserved : VEnvs.CtorTelescopesPreserved sourceEnv outEnv sourceModels targetModels

/-- Construct the uniform result directly from the environment model and
independent source specification. -/
def InductiveExtension.ofModel
    (targetModels : VEnvs) (wf : targetModels.WFCore outEnv)
    (mono : ∀ safety, sourceModels.venv safety ≤ targetModels.venv safety)
    (specification : SourceAddInduct
      (sourceModels.venv (if isUnsafe then .unsafe else .safe)) lparams
      nparams sourceTypes isUnsafe
      (targetModels.venv (if isUnsafe then .unsafe else .safe)))
    (ctorTelescopesPreserved : VEnvs.CtorTelescopesPreserved sourceEnv outEnv sourceModels targetModels) :
    InductiveExtension sourceEnv outEnv sourceModels lparams nparams sourceTypes
      isUnsafe where
  targetModels := targetModels
  wf := wf
  mono := mono
  specification := specification
  ctorTelescopesPreserved := ctorTelescopesPreserved

/-- Forget the inductive-specific facts and recover the
environment-preservation postcondition used by `addDecl.WF`. -/
theorem InductiveExtension.modelExtension
    (H : InductiveExtension sourceEnv outEnv sourceModels lparams nparams sourceTypes
      isUnsafe) :
    ∃ targetModels : VEnvs, targetModels.WFCore outEnv ∧
      (∀ safety, sourceModels.venv safety ≤ targetModels.venv safety) ∧
      VEnvs.CtorTelescopesPreserved sourceEnv outEnv sourceModels targetModels :=
  ⟨H.targetModels, H.wf, H.mono, H.ctorTelescopesPreserved⟩

end VerifyInductive
end Lean4Lean
