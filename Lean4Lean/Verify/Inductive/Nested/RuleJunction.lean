import Lean4Lean.Verify.Inductive.Nested.AuxRecNames

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-- **Freshness of the restorable names in a final assembly shape.** For any
final assembly shape of a validated nested run and any restoration table of
the run, the restorable names (auxiliary family and constructor names and
the lowered auxiliary recursor names) are absent from the shape's final
abstract environment. Every restorable name other than a renamed auxiliary
recursor name `Main.rec_k` is absent without any hypothesis
(`finalBaseVEnv_restorableNames_fresh_of_not_renamed`); the renamed names are
installed in the final environment, so they are excluded from the restorable
names by `HauxRecNames`. This hypothesis is necessary for the conclusion: no
recorded fact of the run excludes a source family named `_nested.i.x` whose
renamed recursor `_nested.i.x.rec_k` is an auxiliary constructor name (see
`Nested/AuxRecNames.lean`). -/
theorem NestedValidatedRunResult.finalBaseVEnv_restorableNames_fresh
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (HauxRecNames : ∀ auxiliaries : List ContainerSpecialization,
      RestorationTableData sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ p ∈ (compilationRestoration sourceDecl auxiliaries).recursors,
        p.2 ∉ (compilationRestoration sourceDecl auxiliaries).restorableNames)
    (C : NestedFinalAssemblyShape E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.production = E.production)
    {auxiliaries : List ContainerSpecialization}
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams) :
    ∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
      C.finalBaseVEnv.constants n = none := by
  intro n hn
  refine E.finalBaseVEnv_restorableNames_fresh_of_not_renamed wf Hsources C hC D n hn ?_
  intro hmem
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hmem
  exact HauxRecNames auxiliaries D p hp hn

/-- **The rule junction `Hrules` of `assemblyNative_of_run`**, from the
restored-auxiliary-recursor name hypothesis `HauxRecNames` (see
`finalBaseVEnv_restorableNames_fresh`) and the rule-realization hypothesis
`HruleShape`: some final assembly shape of the run has rule lists realizing
the executable restored rules in its final abstract environment. The
freshness conjunct is derived for that shape. -/
theorem NestedValidatedRunResult.hrules_of
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (HauxRecNames : ∀ auxiliaries : List ContainerSpecialization,
      RestorationTableData sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ p ∈ (compilationRestoration sourceDecl auxiliaries).recursors,
        p.2 ∉ (compilationRestoration sourceDecl auxiliaries).restorableNames)
    (HruleShape : ∀ auxiliaries : List ContainerSpecialization,
      RestorationTableData sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∃ C : NestedFinalAssemblyShape E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        C.production = E.production ∧
        List.Forall₂
          (E.RestoredRuleRealization (compilationRestoration sourceDecl auxiliaries)
            C.finalBaseVEnv)
          (List.finRange E.production.compilationSignature.constructors.size)
          (C.primaryRules ++ C.auxiliaryRules)) :
    ∀ auxiliaries : List ContainerSpecialization,
      RestorationTableData sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∃ C : NestedFinalAssemblyShape E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        C.production = E.production ∧
        (∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
          C.finalBaseVEnv.constants n = none) ∧
        List.Forall₂
          (E.RestoredRuleRealization (compilationRestoration sourceDecl auxiliaries)
            C.finalBaseVEnv)
          (List.finRange E.production.compilationSignature.constructors.size)
          (C.primaryRules ++ C.auxiliaryRules) := by
  intro auxiliaries D
  obtain ⟨C, hC, HC⟩ := HruleShape auxiliaries D
  exact ⟨C, hC, E.finalBaseVEnv_restorableNames_fresh wf Hsources HauxRecNames C hC D, HC⟩

end VerifyInductive
end Lean4Lean
