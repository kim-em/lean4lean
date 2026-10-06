import Lean4Lean.Verify.Inductive.Nested.RuleJunction
import Lean4Lean.Verify.Inductive.Nested.RuleShape
import Lean4Lean.Verify.Inductive.Nested.RecursorProvenance

/-! # The final assembly certificate of a validated nested run

* `NestedValidatedRunResult.assemblyNative_of_restoredWF`: the final assembly
  certificate of a nested run, modulo only the well-formedness `HrestoredWF`
  of the restored generated equations in the final abstract environment of a
  final assembly shape. It composes `hruleShape_of`, `hrules_of`,
  `hprovenance_of` and `assemblyNative_of_run`.
* `NestedValidatedRunResult.assemblyNative`: the same certificate with no
  hypothesis beyond the run being nested; this is used by
  `Nested/FinalModelDispatch.lean`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-- The final assembly certificate of a nested validated run, from the
well-formedness `HrestoredWF` of the restored generated equations (the
hypothesis of `hruleShape_of`, verbatim). -/
theorem NestedValidatedRunResult.assemblyNative_of_restoredWF
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (hnested : result.aux2nested.size ≠ 0)
    (HrestoredWF : ∀ auxiliaries : List ContainerSpecialization,
      RestorationTableData sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ C : NestedFinalAssemblyShape E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        C.production = E.production →
        CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
          (Lean4Lean.stripRecursorRules outEnv
            (Lean4Lean.restoredRecursorNames
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) C.finalBaseVEnv →
        ∀ (k : Fin E.production.production.completed.generationSignature.constructors.size)
          (rule : VDefEq),
          (compilationRestoration sourceDecl auxiliaries).equation
              (E.production.production.completed.canonicalGeneration.equation k) =
            some rule →
          rule.WF C.finalBaseVEnv) :
    Nonempty { C : NestedFinalAssemblyCertificate E.restoration
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
        nparams isUnsafe (if isUnsafe then .unsafe else .safe) //
      C.production = E.production } :=
  E.assemblyNative_of_run wf Hsources
    (E.hrules_of wf Hsources (E.hruleShape_of wf Hsources hnested HrestoredWF))
    (E.hprovenance_of wf Hsources hnested)

/-- The canonical equations and concrete recursor evidence are selected from
this complete successful run. This theorem does not upgrade arbitrary legacy
rule batches or accept a caller-supplied compilation callback.

Remaining obligation: this is `assemblyNative_of_restoredWF E wf Hsources
hnested HrestoredWF`, where `HrestoredWF` is the hypothesis of
`assemblyNative_of_restoredWF` (equivalently of `hruleShape_of`): for every
specialization list `auxiliaries` with
`RestorationTableData sourceDecl auxiliaries result E.loweredEnv
(mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams`, every final assembly
shape `C` with `C.production = E.production` in whose final abstract
environment `C.finalBaseVEnv` the stripped output environment
`stripRecursorRules outEnv (restoredRecursorNames ...)` is
`CheckingEnv.Valid`, and every constructor index `k`, each restored generated
equation `rule` with `(compilationRestoration sourceDecl auxiliaries).equation
(E.production.production.completed.canonicalGeneration.equation k) = some rule`
satisfies `rule.WF C.finalBaseVEnv`. Once that is available as
`E.hrestoredWF_of wf Hsources` (`Nested/RestoredEquationWF.lean`), the body
becomes `assemblyNative_of_restoredWF E wf Hsources hnested
(E.hrestoredWF_of wf Hsources)`. -/
theorem NestedValidatedRunResult.assemblyNative
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (hnested : result.aux2nested.size ≠ 0) :
    Nonempty { C : NestedFinalAssemblyCertificate E.restoration
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
        nparams isUnsafe (if isUnsafe then .unsafe else .safe) //
      C.production = E.production } := by
  sorry

end VerifyInductive

end Lean4Lean
