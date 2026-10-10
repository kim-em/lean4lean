import Lean4Lean.Verify.Inductive.Header.Installation
import Lean4Lean.Theory.Inductive.Signature

/-! # The checked formation

`CheckedFormation` is the data available once every constructor of a declaration is checked
(`AddInductive.checkConstructors`) and before the constructors are declared: the header
environment, the translated declaration (`TrInductDeclCore`), the formation certificate and the
field classification the executable returns. From it the constructor phase delivers a source
signature of the declaration (`CheckedFormation.signature`), which the recursor phase's generator
instantiates (section 3.2 of the design notes).

Wave 2 scaffold: owned by the `Constructor/`+`CheckedFormation` agent (source branch:
`Constructor/{CheckedFormation,CheckedConstructors,SourceSignature,Normalization,Positivity,
RawTranslation,Translation,Check}.lean`). The case eliminators of the source branch are gone. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The checked formation of a declaration: its header environment and, in it, the checked
constructor types, their translation and the formation certificate. -/
structure CheckedFormation (c : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (decl : VInductDecl) (nparams : Nat) (isUnsafe : Bool) (depth : Nat) (sourceEnv : VEnv)
    (indTypes : Array InductiveType) where
  headerEnv : Environment
  headers : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv indTypes headerEnv
  /-- The abstract constructor environment. -/
  ctorVEnv : VEnv
  core : TrInductDeclCore sourceEnv c.lparams nparams indTypes.toList isUnsafe decl
    headers.context.venv ctorVEnv
  formation : FormationCertificate sourceEnv decl
  params_eq : formation.headers.params = headers.headers.params
  checked : CheckedConstructorCertificate sourceEnv decl headers.context.venv
    formation.headers.params
  /-- The field classifications returned by the executable constructor check, family by
  family and constructor by constructor. -/
  classes : List (List (List Bool))
  classes_length : classes.length = indTypes.size

namespace CheckedFormation

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
  {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv} {indTypes : Array InductiveType}

/-- The abstract header environment. -/
abbrev headerVEnv (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    VEnv := B.headers.context.venv

theorem headerVEnv_wf (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    B.headerVEnv.WF := B.headers.context.wf

/-- The source signature of the checked formation: a signature modelling the declaration
(`InductiveSignature.Models`), whose family applications are typed in the header environment.
This is the signature the recursor generator instantiates. -/
theorem signature (B : CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes) :
    ∃ s : InductiveSignature, s.Models sourceEnv decl ∧
      s.FamilyTypesWF B.headerVEnv decl.uvars := by
  -- WAVE 2 STUB (Constructor/CheckedFormation): the source branch's
  -- `CheckedFormation.sourceSignature`, `sourceSignature_models` and
  -- `sourceSignature_familyTypesWF_header` (`Constructor/CheckedFormation.lean`), without the
  -- case schema.
  have := B; sorry

end CheckedFormation

end VerifyInductive
end Lean4Lean
