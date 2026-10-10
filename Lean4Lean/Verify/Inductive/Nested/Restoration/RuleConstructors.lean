import Lean4Lean.Verify.Inductive.Nested.Restoration.TableAgreement
import Lean4Lean.Verify.Inductive.Nested.Restoration.CompilationData

/-! # The constructors of the restored rules

The facts `NestedRun.assemblyRecursors` (`AssemblyRecursors.lean`) reads about the constructor
of every restored recursor rule: its kernel `ctorInfo` and parameter count, its constructor
shape in the source constructor stage, the source-or-container alternative, and their
distinctness within one family. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-- **Stub (restB).** The constructor of every restored rule: the restored constructor of a
generated constructor `index` of family `owner` is a kernel constructor of the output whose
parameter count is the restored family head's argument count (the source family's parameters,
or the container's specialization arguments), a constructor of the source constructor stage
with the constructor shape at that count plus the field count, and either one of the source
declaration's constructors at its parameter count or a constructor of a container installed
below at the container's.

What it needs: for a source owner, `restoredHeadName` is the identity on its constructors
(`CompilationData.restoredFamilyHead_spec`'s first alternative), and the source constructors'
`ctorInfo`s and `TrIndType`s are the base's (`RestoredBlockBase.sourceTranslations`); for an
auxiliary owner, the restored constructor is a constructor of `a.container`, whose installation
(`ContainersInstalled`, then `InstalledBlocks` of the source environment) provides its
`ctorInfo`, its translation and its `numParams = a.container.nparams = a.arguments.length`. -/
theorem NestedRun.restoredRuleConstructors
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes)
    {auxiliaries : List ContainerSpecialization} {block : VInductBlock}
    (D : RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (Hcert : ContainersInstalled (ves.venv (if isUnsafe then .unsafe else .safe)) auxiliaries)
    (Hdata : CompilationData (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
      E.lowered.loweredDecl E.lowered.signature E.lowered.generatedInstance auxiliaries block)
    (owner : Fin E.lowered.signature.families.size) {head : RestoredFamilyHead}
    (hhead : E.lowered.generatedInstance.restoredFamilyHead
      (compilationRestoration sourceDecl auxiliaries) owner = some head)
    (index : Fin E.lowered.signature.constructors.size)
    (hown : E.lowered.signature.constructors[index].owner = owner) :
    (∃ cval : ConstructorVal, outEnv.constants.find?
        ((compilationRestoration sourceDecl auxiliaries).restoredHeadName
          E.lowered.signature.constructors[index].name) = some (.ctorInfo cval) ∧
      cval.numParams = head.arguments.length) ∧
    (∃ ci, E.sourceCore.envCtors.constants
        ((compilationRestoration sourceDecl auxiliaries).restoredHeadName
          E.lowered.signature.constructors[index].name) = some ci ∧
      ci.type.CtorShape (head.arguments.length +
        E.lowered.signature.constructors[index].fields.length)) ∧
    ((∃ c ∈ sourceDecl.constructorConstants,
        (compilationRestoration sourceDecl auxiliaries).restoredHeadName
          E.lowered.signature.constructors[index].name = c.name ∧
        head.arguments.length = sourceDecl.nparams) ∨
      (∃ Dc, VEnv.InstalledBelow (ves.venv (if isUnsafe then .unsafe else .safe)) Dc ∧
        ∃ c ∈ Dc.constructorConstants,
          (compilationRestoration sourceDecl auxiliaries).restoredHeadName
            E.lowered.signature.constructors[index].name = c.name ∧
          head.arguments.length = Dc.nparams)) := by
  -- WAVE 3 STUB (restB): see the docstring.
  have := wf; have := Hsources; have := D; have := Hcert; have := Hdata; have := hhead
  have := hown; sorry

/-- **Stub (restB).** The restored constructors of one family are distinct: the identity on a
source family's constructors, and on an auxiliary family's the constructors of its container's
family (`CaseCompilationData.directFamily_restored_constructor_names`), whose names are distinct
in the installed container. -/
theorem NestedRun.restoredRuleConstructors_nodup
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    {auxiliaries : List ContainerSpecialization} {block : VInductBlock}
    (Hcert : ContainersInstalled (ves.venv (if isUnsafe then .unsafe else .safe)) auxiliaries)
    (Hdata : CompilationData (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
      E.lowered.loweredDecl E.lowered.signature E.lowered.generatedInstance auxiliaries block)
    (owner : Fin E.lowered.signature.families.size) :
    ((E.lowered.signature.ownedConstructors owner).map fun index =>
      (compilationRestoration sourceDecl auxiliaries).restoredHeadName
        E.lowered.signature.constructors[index].name).Nodup := by
  -- WAVE 3 STUB (restB): see the docstring.
  have := Hcert; have := Hdata; have := owner; sorry


end VerifyInductive
end Lean4Lean
