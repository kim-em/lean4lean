import Lean4Lean.Verify.Inductive.Nested.Restoration.RecursorAlignment
import Lean4Lean.Verify.Inductive.Nested.Restoration.Equations.RestoredRulesBase
import Lean4Lean.Verify.Inductive.Nested.Restoration.AuxiliaryProjections

/-! # The rule junction and the final assembly certificate of a validated nested run

* `NestedValidatedRunResult.hrules_of`: the rule junction `Hrules` of
  `assemblyNative_of_run` from the rule-shape hypothesis `HruleShape` alone;
  freshness is derived for the restorable names that are not renamed
  auxiliary recursor names `Main.rec_k` (a renamed name may coincide with an
  auxiliary constructor name, see `Nested/Restoration/RecursorRenaming.lean`).
* `NestedValidatedRunResult.assemblyNative_of_run`: the final assembly
  certificate from `Hrules` and the recursor provenance `Hprovenance`
  (`hprovenance_of`), using the input-side avoidance of the renamed names by
  the lowered rules (`loweredRulesAvoid_renamed`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-- **The rule junction `Hrules` of `assemblyNative_of_run`**, from the
rule-realization hypothesis `HruleShape`: some final assembly shape of the
run has rule lists realizing the executable restored rules in its final
abstract environment. The freshness conjunct (restorable names other than
the renamed recursor names) is derived for that shape. -/
theorem NestedValidatedRunResult.hrules_of
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
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
          n ∉ (compilationRestoration sourceDecl auxiliaries).recursors.map Prod.snd →
          C.finalBaseVEnv.constants n = none) ∧
        List.Forall₂
          (E.RestoredRuleRealization (compilationRestoration sourceDecl auxiliaries)
            C.finalBaseVEnv)
          (List.finRange E.production.compilationSignature.constructors.size)
          (C.primaryRules ++ C.auxiliaryRules) :=
  E.hrules_of_modulo wf Hsources HruleShape

/-- **Final assembly certificate of a validated nested run**, modulo the rule
junction `Hrules` (discharged by `hrules_of` from the rule-shape hypothesis)
and the recursor provenance `Hprovenance` (discharged by `hprovenance_of`).
Freshness of the restorable names in the shape's final environment is only
asked outside the renamed auxiliary recursor names `Main.rec_k`, which is
what holds without any naming hypothesis
(`finalBaseVEnv_restorableNames_fresh_of_not_renamed`); the input-side
avoidance of the renamed names by the lowered rules is
`loweredRulesAvoid_renamed`. -/
theorem NestedValidatedRunResult.assemblyNative_of_run
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (Hrules : ∀ auxiliaries : List ContainerSpecialization,
      RestorationTableData sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∃ C : NestedFinalAssemblyShape E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        C.production = E.production ∧
        (∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
          n ∉ (compilationRestoration sourceDecl auxiliaries).recursors.map Prod.snd →
          C.finalBaseVEnv.constants n = none) ∧
        List.Forall₂
          (E.RestoredRuleRealization (compilationRestoration sourceDecl auxiliaries)
            C.finalBaseVEnv)
          (List.finRange E.production.compilationSignature.constructors.size)
          (C.primaryRules ++ C.auxiliaryRules))
    (Hprovenance : ∀ auxiliaries : List ContainerSpecialization,
      RestorationTableData sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ C : NestedFinalAssemblyShape E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        C.production = E.production →
        (∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
          n ∉ (compilationRestoration sourceDecl auxiliaries).recursors.map Prod.snd →
          C.finalBaseVEnv.constants n = none) →
        List.Forall₂
          (E.RestoredRuleRealization (compilationRestoration sourceDecl auxiliaries)
            C.finalBaseVEnv)
          (List.finRange E.production.compilationSignature.constructors.size)
          (C.primaryRules ++ C.auxiliaryRules) →
        InductiveRecursorProvenance .unsafe sourceProdEnv.constants
          (ves.venv (if isUnsafe then .unsafe else .safe)) outEnv.constants
          (C.finalBaseVEnv.addDefEqRules (C.primaryRules ++ C.auxiliaryRules))) :
    Nonempty { C : NestedFinalAssemblyCertificate E.restoration
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
        nparams isUnsafe (if isUnsafe then .unsafe else .safe) //
      C.production = E.production } := by
  rcases E.restorationTablesRestoringAll wf Hsources with
    ⟨envTypes, generated, auxiliaries, hadded, henvTypes, Haux, Hexpansion,
      hparamsSize, D, Hrestoring, HauxRestoring⟩
  obtain ⟨C, hC, hfreshFinal, HCrules⟩ := Hrules auxiliaries D
  have Hprov := Hprovenance auxiliaries D C hC hfreshFinal HCrules
  have hnodup :
      (familyNames E.production.loweredDecl.types ++
        E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  obtain ⟨-, -, -, -, -, -, -, hscoped, -, hctorNames, -, -⟩ :=
    E.restorationPrefix_of wf hadded henvTypes Haux Hexpansion hnodup D True.intro
  -- the restored equations, modulo the renamed recursor names
  have hheads : (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
      E.auxHeads := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  have HL := E.loweredRulesAvoid_renamed wf Hsources Haux Hexpansion D
  rw [← hheads] at HL
  have hequations := E.restoredEquations_of_realizationModulo wf Hsources hheads hparamsSize
    D hscoped HL
    (RestoredRulesRealizationModulo.filter_restorable ⟨C.finalBaseVEnv, hfreshFinal, HCrules⟩)
  obtain ⟨Hcertified, ⟨Hdata⟩⟩ := E.compilationData_of_tables wf Hsources C hC hadded
    henvTypes Haux Hexpansion hparamsSize D Hrestoring HauxRestoring hequations
  have hwf : sourceProdEnv.constants.WF := (wf.tr (safety := .safe)).map_wf
  -- the constructor environment of the shape
  have htypesEq : C.canonical.venvTypes = envTypes := by
    have h := C.canonical.abstract_types
    rw [C.typeValues, hadded] at h
    exact (Option.some.inj h).symm
  have hctorsAdded : envTypes.addConstVals sourceDecl.constructorConstants =
      some C.canonical.venvCtors := by
    have h := C.canonical.abstract_ctors
    rwa [C.constructorValues, htypesEq] at h
  have hsourceCtorNames := C.sourceConstructorNames
  rw [hC] at hsourceCtorNames
  have hfresh := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hfreshCtors := E.restorableNames_fresh_ctors hadded Haux Hexpansion hnodup
    hsourceCtorNames hctorsAdded
  have hrecAdded := C.canonical.recursorsAdded.abstract
  have hle : (C.canonical.venvCtors.addEliminators C.canonical.eliminators).addProjections sourceDecl.projectionEntries ≤
      C.finalBaseVEnv := VEnv.addConstVals_le hrecAdded
  have hnames : sourceTypes.map (·.name) = sourceDecl.types.map (·.name) := by
    have Hcore := E.nativeSource.core
    rw [E.nativeSourceDecl_eq] at Hcore
    exact (forall₂_trInductiveType_names Hcore.types).symm
  have hinfos := E.restoredRecursorEntryInfos C hC wf Hsources hadded Haux Hexpansion hnodup
    hparamsSize D hscoped hwf
  have Hentries : List.Forall₂
      (RestoredRecursorEntryRealization E.production.compilationInstance
        (compilationRestoration sourceDecl auxiliaries)
        (sourceDecl.types.map (·.name)) C.finalBaseVEnv)
      (List.finRange E.production.compilationSignature.families.size)
      C.recursorEntries := by
    refine forall₂_imp_mem_right hinfos ?_
    rintro owner entry hentry ⟨s, t, Hstep, hentry1, hrec, Hw⟩
    refine ⟨Hstep.restored.newInfo, hentry1, hrec, ?_⟩
    obtain ⟨head, hhead, hheadName, hlevels, hargs, happ, Hctor⟩ :=
      Hdata.restoredFamilyHead_spec hadded hctorsAdded hfresh hfreshCtors owner
    have hinstalled : C.finalBaseVEnv.constants Hstep.restored.newInfo.name ≠ none := by
      have hget := VEnv.addConstVals_get hrecAdded (List.mem_map_of_mem hentry)
      have hname : entry.2.name = Hstep.restored.newInfo.name :=
        Hw.1.trans Hstep.restored.restoration.name.symm
      rw [← hname, hget]
      simp
    have Hrules' := E.restoredRuleRealizations D hctorNames Hdata.recursorNames
      Hdata.heads_not_recursors hfreshFinal (E.auxRecName_not_renamed wf Hsources D)
      Hdata.equations HCrules owner Hstep hinstalled head Hctor
    refine E.restoredRecursorRealization_of_step D hnames owner Hstep hle hrec Hw
      ⟨head, hhead, ?_, hlevels, hargs, happ, Hrules'⟩
    rw [E.restoredMajorInduct wf Hsources Haux Hexpansion hnodup hparamsSize D hscoped
      owner Hstep, hheadName]
  exact ⟨⟨{ toNestedFinalAssemblyShape := C
            realization := ⟨⟨_, _, _, _, Hdata, Hcertified, Hentries⟩⟩
            provenance := Hprov }, hC⟩⟩

end VerifyInductive
end Lean4Lean

/-! # The final assembly certificate of a validated nested run

* `NestedValidatedRunResult.assemblyNative_of_restoredWF`: the final assembly
  certificate of a nested run, modulo only the well-formedness `HrestoredWF`
  of the restored generated equations in the final abstract environment of a
  final assembly base. It composes `hruleShape_of_base`, `hrules_of`,
  `hprovenance_of` and `assemblyNative_of_run`.
* `NestedValidatedRunResult.assemblyNative`: the same certificate with no
  hypothesis beyond the run being nested, from `hrestoredWF_of`; this is used
  by `Nested/Install/Result.lean`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-- The final assembly certificate of a nested validated run, from the
well-formedness `HrestoredWF` of the restored generated equations (the
hypothesis of `hruleShape_of_base`, verbatim). -/
theorem NestedValidatedRunResult.assemblyNative_of_restoredWF
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (hnested : result.aux2nested.size ≠ 0) (hcorner : ∀ safety, CtorTelescopes safety sourceProdEnv (ves.venv safety))
    (HrestoredWF : ∀ auxiliaries : List ContainerSpecialization,
      RestorationTableData sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ B : NestedFinalAssemblyBase E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        B.production = E.production →
        CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
          (Lean4Lean.stripRecursorRules outEnv
            (Lean4Lean.restoredRecursorNames
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) B.finalBaseVEnv →
        ∀ (k : Fin E.production.production.generationSignature.constructors.size)
          (rule : VDefEq),
          (compilationRestoration sourceDecl auxiliaries).equation
              (E.production.production.canonicalGeneration.equation k) =
            some rule →
          rule.WF B.finalBaseVEnv) :
    Nonempty { C : NestedFinalAssemblyCertificate E.restoration
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
        nparams isUnsafe (if isUnsafe then .unsafe else .safe) //
      C.production = E.production } :=
  E.assemblyNative_of_run wf Hsources
    (E.hrules_of wf Hsources (E.hruleShape_of_base wf Hsources hnested HrestoredWF))
    (E.hprovenance_of wf Hsources hnested hcorner)

/-- The canonical equations and concrete recursor evidence are selected from
this complete successful run. This theorem does not upgrade arbitrary legacy
rule batches or accept a caller-supplied compilation callback. The
restored-equation well-formedness `HrestoredWF` of
`assemblyNative_of_restoredWF` is `NestedValidatedRunResult.hrestoredWF_of`
(`Nested/Restoration/AuxiliaryProjections.lean`). -/
theorem NestedValidatedRunResult.assemblyNative
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (hnested : result.aux2nested.size ≠ 0) (hcorner : ∀ safety, CtorTelescopes safety sourceProdEnv (ves.venv safety)) :
    Nonempty { C : NestedFinalAssemblyCertificate E.restoration
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
        nparams isUnsafe (if isUnsafe then .unsafe else .safe) //
      C.production = E.production } :=
  E.assemblyNative_of_restoredWF wf Hsources hnested hcorner (E.hrestoredWF_of wf Hsources)

end VerifyInductive

end Lean4Lean
