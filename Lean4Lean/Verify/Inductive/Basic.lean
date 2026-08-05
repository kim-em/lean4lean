import Lean4Lean.Inductive.Add
import Lean4Lean.Verify.TypeChecker

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Production-side installation of a list of kernel constants. This small
reference function is used only to state the staging invariant; the executable
inductive checker continues to build the same environments directly. -/
def addConstants : Environment → List ConstantInfo → Environment
  | env, [] => env
  | env, ci :: cis => addConstants (env.add ci) cis

/-- A certificate that a list of production constants and abstract constants
are installed in lockstep. Each translation and typing premise is stated in
the environment at the exact point where that constant is introduced. -/
inductive AddConstants (safety : DefinitionSafety) :
    Environment → VEnv → List (ConstantInfo × VConstVal) →
      Environment → VEnv → Prop
  | nil : AddConstants safety env venv [] env venv
  | cons :
    env.find? ci.name = none →
    ¬ Kernel.Environment.primitives.contains ci.name →
    TrConstVal safety venv ci ci' →
    ci'.toVConstant.WF venv →
    venv.addConst ci.name ci'.toVConstant = some venv' →
    ci.deltaValue? = none →
    AddConstants safety (env.add ci) venv' rest outEnv outVEnv →
    AddConstants safety env venv ((ci, ci') :: rest) outEnv outVEnv

theorem AddConstants.valid
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hvalid : CheckingEnv.Valid safety env venv) :
    CheckingEnv.Valid safety outEnv outVEnv := by
  induction H with
  | nil => exact hvalid
  | cons hn hnprim htr hwf hadd hdelta _ ih =>
    exact ih (hvalid.add hn hnprim htr.1 hwf hadd hdelta)

theorem AddConstants.production
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    addConstants env (entries.map Prod.fst) = outEnv := by
  induction H with
  | nil => rfl
  | cons _ _ _ _ _ _ _ ih => simpa [addConstants] using ih

theorem AddConstants.abstract
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    venv.addConsts (entries.map Prod.snd) = some outVEnv := by
  induction H with
  | nil => simp [VEnv.addConsts]
  | cons _ _ htr _ hadd _ _ ih =>
    rw [List.map_cons, VEnv.addConsts, ← htr.2, hadd]
    exact ih

theorem AddConstants.le
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    venv ≤ outVEnv :=
  VEnv.addConsts_le H.abstract

/-- Three-stage installation certificate matching the executable order:
mutual headers, constructors, then recursors. Reduction equations are not
included here because their validity depends on the independent iota schema. -/
structure StagedBlock (safety : DefinitionSafety)
    (env : Environment) (venv : VEnv)
    (types ctors recursors : List (ConstantInfo × VConstVal))
    (outEnv : Environment) (outVEnv : VEnv) where
  envTypes : Environment
  venvTypes : VEnv
  envCtors : Environment
  venvCtors : VEnv
  typesAdded : AddConstants safety env venv types envTypes venvTypes
  ctorsAdded : AddConstants safety envTypes venvTypes ctors envCtors venvCtors
  recursorsAdded : AddConstants safety envCtors venvCtors recursors outEnv outVEnv

theorem StagedBlock.valid
    (H : StagedBlock safety env venv types ctors recursors outEnv outVEnv)
    (hvalid : CheckingEnv.Valid safety env venv) :
    CheckingEnv.Valid safety outEnv outVEnv :=
  H.recursorsAdded.valid (H.ctorsAdded.valid (H.typesAdded.valid hvalid))

theorem StagedBlock.abstract_types
    (H : StagedBlock safety env venv types ctors recursors outEnv outVEnv) :
    venv.addConsts (types.map Prod.snd) = some H.venvTypes :=
  H.typesAdded.abstract

theorem StagedBlock.abstract_ctors
    (H : StagedBlock safety env venv types ctors recursors outEnv outVEnv) :
    H.venvTypes.addConsts (ctors.map Prod.snd) = some H.venvCtors :=
  H.ctorsAdded.abstract

theorem StagedBlock.abstract_recursors
    (H : StagedBlock safety env venv types ctors recursors outEnv outVEnv) :
    H.venvCtors.addConsts (recursors.map Prod.snd) = some outVEnv :=
  H.recursorsAdded.abstract

end VerifyInductive
end Lean4Lean
