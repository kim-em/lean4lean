import Lean4Lean.Verify.Inductive.Nested.Restoration.LoweredRuleAvoidance
import Lean4Lean.Verify.Inductive.Nested.Restoration.Validation.Passes
import Lean4Lean.Verify.Inductive.Nested.Restoration.ViewCast
import Lean4Lean.Verify.Inductive.Nested.Restoration.RestoredShapes
import Lean4Lean.Verify.Inductive.Nested.Restoration.Certificate
import Lean4Lean.Verify.Inductive.Nested.Restoration.KernelData

/-! # The recursor and compilation half of the restored block

The fields of `RestoredBlock` (`Nested/Restoration/Certificate.lean`) about recursors and
compilation, produced from a nested run `E`, a rule-free restored block base `B` of it, and the
restoration tables of `restorationTablesRestoringAll`.

* **Rule translation** (`NestedRun.trRestoredRecursorRule_of_equation`, the source branch's
  `Equations/RestoredRules.lean` lemma): in the recursor stage of `B`, where the stripped output
  environment is a checker environment (`CheckerEnv`, the input of restA's
  `validateRestoredRecursorRules.check.WF`), the right-hand side of every executable restored
  rule translates, and its translation is the restoration of the generated right-hand side. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-- The right-hand side of a restored recursor rule translates in any model in which the
stripped output environment is a checker environment (the rule validation pass). -/
theorem NestedRun.restoredRuleRhs_translation'
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    {venv : VEnv}
    (Cstrip : CheckerEnv (if isUnsafe then .unsafe else .safe)
      (Lean4Lean.stripRecursorRules outEnv
        (Lean4Lean.restoredRecursorNames
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) venv)
    {recName : Name}
    (hrecName : recName ∈ sourceTypes.map (fun t => Lean.mkRecName t.name) ++
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)
    {s t : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
      (sourceTypes.map (·.name)) recName s t)
    (j : Nat) (hj : j < Hstep.restored.newInfo.rules.length) :
    ∃ target, TrExprS venv Hstep.restored.newInfo.levelParams []
      (Hstep.restored.newInfo.rules[j]'hj).rhs target := by
  have hcheck := validateRestoredRecursorRules.run.WF Cstrip _ _ _ _ _ _ _
    E.recursorRuleValidation recName hrecName
  obtain ⟨recInfo, hfind, hrules⟩ := validateRestoredRecursorRules.check.WF Cstrip _ _ _ _ _ _
    hcheck
  have hold : recInfo = Hstep.oldInfo := by
    have h := hfind.symm.trans Hstep.lookup
    injection h with h
    injection h
  subst hold
  have hnew : restoredRecursorOf result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 (sourceTypes.map (·.name))
      recName Hstep.oldInfo = Hstep.restored.newInfo := Hstep.restored.produced.symm
  rw [hnew] at hrules
  obtain ⟨rhs, -, Ht, -⟩ := hrules _ (List.getElem_mem hj)
  exact ⟨rhs, Ht⟩

theorem _root_.Lean4Lean.InductiveSignature.Restoration.equation_eq_some'
    {r : Restoration} {eq rule : VDefEq} (h : r.equation eq = some rule) :
    rule.uvars = eq.uvars ∧ r.expr eq.lhs = some rule.lhs ∧
      r.expr eq.rhs = some rule.rhs ∧ r.expr eq.type = some rule.type := by
  simp only [Restoration.equation, Option.bind_eq_bind, Option.pure_def] at h
  cases hl : r.expr eq.lhs with
  | none => simp [hl] at h
  | some lhs =>
    cases hr : r.expr eq.rhs with
    | none => simp [hl, hr] at h
    | some rhs =>
      cases ht : r.expr eq.type with
      | none => simp [hl, hr, ht] at h
      | some ty =>
        simp only [hl, hr, ht, Option.bind_some, Option.some.injEq] at h
        subst h
        exact ⟨rfl, rfl, rfl, rfl⟩

/-- **Translation of a restored generated equation** (the source branch's
`trRestoredRecursorRule_of_equation`, with the stripped checker environment `Cstrip` in place of
the source's validity and cache-soundness premises). In the recursor environment of a restored
block base, the abstract restoration of the `k`-th generated equation is a translation of the
executable restored rule at `k`. -/
theorem NestedRun.trRestoredRecursorRule_of_equation
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (Haux : List.Forall₂ (SpecializationGenerates
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.lowered.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedOccurrenceReplacementAbs
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.lowered.loweredDecl.types.drop sourceDecl.types.length))
    (hnodup : (familyNames E.lowered.loweredDecl.types ++
      E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup)
    (hparamsSize : result.params.size = result.nparams)
    (D : RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hscoped : (compilationRestoration sourceDecl auxiliaries).Scoped)
    (C : RestoredBlockBase E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.lowered = E.lowered)
    (hkernel : List.Perm
      ((C.typeEntries ++ C.constructorEntries ++ C.recursorEntries).map Prod.fst)
      E.restoration.entries)
    (Cstrip : CheckerEnv (if isUnsafe then .unsafe else .safe)
      (Lean4Lean.stripRecursorRules outEnv
        (Lean4Lean.restoredRecursorNames
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) C.recursorVEnv)
    {X : List Name}
    (Hfresh : ∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
      n ∉ X → C.recursorVEnv.constants n = none)
    (HL : E.LoweredRulesAvoid E.auxHeads X)
    (k : Fin E.lowered.recursors.generationSignature.constructors.size)
    {rule : VDefEq}
    (hrule : (compilationRestoration sourceDecl auxiliaries).equation
      (E.lowered.recursors.canonicalGeneration.equation k) = some rule) :
    E.TrRestoredRecursorRule (compilationRestoration sourceDecl auxiliaries)
      C.recursorVEnv k rule := by
  let P := E.lowered.recursors
  have hwf : sourceProdEnv.constants.WF := (wf.tr (safety := .safe)).map_wf
  have hinfos := E.restoredRecursorEntryInfos C hC wf Hsources hadded Haux Hexpansion
    hnodup hparamsSize D hscoped hwf hkernel
  let owner := P.generationSignature.constructors[k].owner
  obtain ⟨entry, -, s, t, Hstep, -, -, -⟩ :=
    Lean4Lean.List.Forall₂.forall_exists_l hinfos owner (List.mem_finRange owner)
  obtain ⟨hi, hinfo⟩ := E.generatedEntryOfStep owner Hstep
  have hmap := P.ownedConstructors_map_val owner hi
  have hmem : k ∈ P.generationSignature.ownedConstructors owner := by
    simp [InductiveSignature.ownedConstructors, owner]
  obtain ⟨j, hj, hjk⟩ := List.getElem_of_mem hmem
  have hval := RuleAssembly.getElem_of_map_val_eq hmap j hj
  rw [hjk] at hval
  have hlenOwned : (P.generationSignature.ownedConstructors owner).length =
      Hstep.oldInfo.rules.length := by
    have h := congrArg List.length hmap
    simp only [List.length_map, List.length_range'] at h
    rw [h, hinfo]
  have hjNew : j < Hstep.restored.newInfo.rules.length := by
    rw [Hstep.restored.restoration.rules.length, ← hlenOwned]
    exact hj
  have hnames := E.recursorNames_order C.sourceNonempty
  have hn : P.canonicalGeneration.recursorName owner ∈
      sourceTypes.map (fun t => Lean.mkRecName t.name) ++
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1 := by
    rw [← hnames]
    exact List.mem_map_of_mem (List.mem_finRange owner)
  obtain ⟨target, Ht⟩ := E.restoredRuleRhs_translation' Cstrip hn Hstep j hjNew
  have hheads : (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
      E.auxHeads := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  have hrhs := E.restoredRuleRhs_of_trail wf Hsources hheads hparamsSize D hscoped Hfresh
    owner Hstep (fun rule hrule => by
      rw [hheads]; exact HL owner Hstep.oldInfo Hstep.lookup rule hrule) j hjNew k hval Ht
  obtain ⟨huvars, hlhs, hrhs', htype⟩ := Restoration.equation_eq_some' hrule
  have htarget : target = rule.rhs := Option.some.inj (hrhs.symm.trans hrhs')
  subst htarget
  exact ⟨owner, j, s, t, Hstep, hjNew, hval, huvars, Ht, hlhs, htype⟩

/-- **The restored compilation of a nested run** (the body of the source branch's
`assemblyOfRun_of_run`, over a rule-free base `C` and the stripped checker environment): for the
specializations of `restorationTablesRestoringAll`, the restored generated equations `rules`
exist, the containers are installed, the restored block with these rules is a
`CompilationData` of the lowered run's generator, and every recursor entry of `C` translates the
restoration of the generated recursor of its owner (`TrRestoredRecursorEntry`, in the recursor
stage of `C`). -/
theorem NestedRun.restoredCompilation
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes)
    (C : RestoredBlockBase E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.lowered = E.lowered)
    (hkernel : List.Perm
      ((C.typeEntries ++ C.constructorEntries ++ C.recursorEntries).map Prod.fst)
      E.restoration.entries)
    (Cstrip : CheckerEnv (if isUnsafe then .unsafe else .safe)
      (Lean4Lean.stripRecursorRules outEnv
        (Lean4Lean.restoredRecursorNames
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) C.recursorVEnv) :
    ∃ (auxiliaries : List ContainerSpecialization) (rules : List VDefEq),
      RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams ∧
      E.lowered.generatedInstance.restoredEquations
        (compilationRestoration sourceDecl auxiliaries) = some rules ∧
      ContainersInstalled (ves.venv (if isUnsafe then .unsafe else .safe)) auxiliaries ∧
      CompilationData (ves.venv (if isUnsafe then .unsafe else .safe))
        sourceDecl E.lowered.loweredDecl E.lowered.signature
        E.lowered.generatedInstance auxiliaries
        (restoredBlock sourceDecl C.sourceRecursors C.auxiliaryRecursors rules []) ∧
      List.Forall₂
        (TrRestoredRecursorEntry E.lowered.generatedInstance
          (compilationRestoration sourceDecl auxiliaries)
          (sourceDecl.types.map (·.name)) C.recursorVEnv)
        (List.finRange E.lowered.signature.families.size)
        C.recursorEntries := by
  rcases E.restorationTablesRestoringAll wf Hsources with
    ⟨envTypes, generated, auxiliaries, hadded, henvTypes, Haux, Hexpansion,
      hparamsSize, D, Hrestoring, HauxRestoring⟩
  have hnodup :
      (familyNames E.lowered.loweredDecl.types ++
        E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  obtain ⟨-, -, -, -, -, -, -, hscoped, -, hctorNames, -, -⟩ :=
    E.restorationPrefix_of wf hadded henvTypes Haux Hexpansion hnodup D True.intro
  have hfreshFinal := E.recursorVEnv_restorableNames_fresh_of_not_renamed wf Hsources C hC
    hkernel D
  have hheads : (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
      E.auxHeads := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  have HL := E.loweredRulesAvoid_renamed wf Hsources Haux Hexpansion D
  have hfreshF : ∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
      n ∉ ((compilationRestoration sourceDecl auxiliaries).recursors.map Prod.snd).filter
        (· ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames) →
      C.recursorVEnv.constants n = none := by
    intro n hn hnot
    exact hfreshFinal n hn (fun hm => hnot (List.mem_filter.mpr ⟨hm, by simpa using hn⟩))
  -- the restored generated equations
  have hrecs := E.restoredRecursorList_of_paramUniform C hC wf Hsources hadded Haux Hexpansion
    hnodup hparamsSize D hscoped
  have hrecTypes : ∀ owner, ∃ t, (compilationRestoration sourceDecl auxiliaries).expr
      (E.lowered.generatedInstance.recursorType owner) = some t := by
    intro owner
    have Hm := List.mapM_eq_some.mp hrecs
    obtain ⟨v, -, hv⟩ := Lean4Lean.List.Forall₂.forall_exists_l Hm _
      (List.mem_map_of_mem (List.mem_finRange owner))
    simp only [Restoration.recursor, Option.bind_eq_bind, Option.pure_def] at hv
    cases ht : (compilationRestoration sourceDecl auxiliaries).expr
        (E.lowered.generatedInstance.recursor owner).type with
    | none => simp [ht] at hv
    | some t => exact ⟨t, ht⟩
  obtain ⟨rules, hrulesEq⟩ := E.lowered.generatedInstance.restoredEquations_isSome _
    hrecTypes (fun owner => E.recursorName_not_head Haux Hexpansion hnodup owner)
  have Hrules : List.Forall₂ (fun k rule => (compilationRestoration sourceDecl auxiliaries).equation
      (E.lowered.recursors.canonicalGeneration.equation k) = some rule)
      (List.finRange E.lowered.recursors.generationSignature.constructors.size)
      rules := by
    have h := List.mapM_eq_some.mp hrulesEq
    simp only [InductiveSignature.Instance.equations] at h
    exact (Lean4Lean.List.forall₂_map_left_iff).mp h
  have HCrules : List.Forall₂
      (E.TrRestoredRecursorRule (compilationRestoration sourceDecl auxiliaries)
        C.recursorVEnv)
      (List.finRange E.lowered.recursors.generationSignature.constructors.size) rules :=
    Lean4Lean.List.Forall₂.imp (fun k _ hk =>
      E.trRestoredRecursorRule_of_equation wf Hsources hadded Haux Hexpansion hnodup
        hparamsSize D hscoped C hC hkernel Cstrip hfreshF HL k hk) Hrules
  have hequations : E.lowered.generatedInstance.restoredEquations
      (compilationRestoration sourceDecl auxiliaries) = some (rules ++ []) := by
    rw [List.append_nil]; exact hrulesEq
  obtain ⟨Hcertified, ⟨Hdata⟩⟩ := E.compilationData_of_tables wf Hsources C hC rules []
    hadded henvTypes Haux Hexpansion hparamsSize D Hrestoring HauxRestoring hequations
  have hwf : sourceProdEnv.constants.WF := (wf.tr (safety := .safe)).map_wf
  have htypesEq : C.install.venvTypes = envTypes := by
    have h := C.install.abstract_types
    rw [C.typeValues, hadded] at h
    exact (Option.some.inj h).symm
  have hctorsAdded : envTypes.addConstVals sourceDecl.constructorConstants =
      some C.install.venvCtors := by
    have h := C.install.abstract_ctors
    rwa [C.constructorValues, htypesEq] at h
  have hsourceCtorNames := C.sourceConstructorNames
  rw [hC] at hsourceCtorNames
  have hfresh := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hfreshCtors := E.restorableNames_fresh_ctors hadded Haux Hexpansion hnodup
    hsourceCtorNames hctorsAdded
  have hrecAdded := C.install.recursorsAdded.abstract
  have hle : C.install.venvCtors.addProjections sourceDecl.projectionEntries ≤
      C.recursorVEnv := VEnv.addConstVals_le hrecAdded
  have hnames : sourceTypes.map (·.name) = sourceDecl.types.map (·.name) := by
    have Hcore := E.sourceCore.core
    rw [E.sourceCoreDecl_eq] at Hcore
    exact (forall₂_trInductiveType_names Hcore.types).symm
  have hinfos := E.restoredRecursorEntryInfos C hC wf Hsources hadded Haux Hexpansion hnodup
    hparamsSize D hscoped hwf hkernel
  have HCrules' : List.Forall₂
      (E.TrRestoredRecursorRule (compilationRestoration sourceDecl auxiliaries)
        C.recursorVEnv)
      (List.finRange E.lowered.signature.constructors.size) rules := HCrules
  refine ⟨auxiliaries, rules, D, hrulesEq, Hcertified, Hdata, ?_⟩
  refine forall₂_imp_mem_right hinfos ?_
  rintro owner entry hentry ⟨s, t, Hstep, hentry1, hrec, Hw⟩
  refine ⟨Hstep.restored.newInfo, hentry1, hrec, ?_⟩
  obtain ⟨head, hhead, hheadName, hlevels, hargs, happ, Hctor⟩ :=
    Hdata.restoredFamilyHead_spec hadded hctorsAdded hfresh hfreshCtors owner
  have hinstalled : C.recursorVEnv.constants Hstep.restored.newInfo.name ≠ none := by
    have hget := VEnv.addConstVals_get hrecAdded (List.mem_map_of_mem hentry)
    have hname : entry.2.name = Hstep.restored.newInfo.name :=
      Hw.1.trans Hstep.restored.restoration.name.symm
    rw [← hname, hget]
    simp
  have Hrules' := E.trRestoredRules D hctorNames Hdata.recursorNames
    Hdata.heads_not_recursors hfreshF
    (fun a ha hm => E.auxRecName_not_renamed wf Hsources D a ha (List.mem_filter.mp hm).1)
    (by rw [List.append_nil] at hequations; exact hequations) HCrules' owner Hstep hinstalled
    head Hctor
  refine E.trRestoredRecursorVal_of_step D hnames owner Hstep hle hrec Hw
    ⟨head, hhead, ?_, hlevels, hargs, happ, Hrules'⟩
  rw [E.restoredMajorInduct wf Hsources Haux Hexpansion hnodup hparamsSize D hscoped
    owner Hstep, hheadName]

/-! ### The kernel recursors of the run in fold order -/

section Folds

variable {result : Lean4Lean.ElimNestedInductive.Result} {loweredEnv : Environment}
  {auxRec : NameMap Name} {allIndNames : List Name}

/-- The source recursors of the family fold are the restoration steps at the source families'
recursor names. -/
theorem FoldSteps.inductiveRecs_steps :
    ∀ {types : List InductiveType} {sourceEnv targetEnv : Environment}
      (H : FoldSteps (RestoredInductiveStep result loweredEnv auxRec allIndNames) types
        sourceEnv targetEnv),
      List.Forall₂ (fun (n : Name) (rv : RecursorVal) => ∃ (s t : Environment)
          (Hs : RestoredRecursorStep result loweredEnv auxRec allIndNames n s t),
          Hs.restored.newInfo = rv)
        (types.map (fun t => Lean.mkRecName t.name)) H.inductiveRecs
  | _, _, _, .nil => .nil
  | _, _, _, .cons h t => .cons ⟨_, _, h.restored.recursor, rfl⟩ (FoldSteps.inductiveRecs_steps t)

/-- The auxiliary recursors of the recursor fold are the restoration steps at their names. -/
theorem FoldSteps.recursorInfos_steps :
    ∀ {names : List Name} {sourceEnv targetEnv : Environment}
      (H : FoldSteps (RestoredRecursorStep result loweredEnv auxRec allIndNames) names
        sourceEnv targetEnv),
      List.Forall₂ (fun (n : Name) (rv : RecursorVal) => ∃ (s t : Environment)
          (Hs : RestoredRecursorStep result loweredEnv auxRec allIndNames n s t),
          Hs.restored.newInfo = rv)
        names H.recursorInfos
  | _, _, _, .nil => .nil
  | _, _, _, .cons h t => .cons ⟨_, _, h, rfl⟩ (FoldSteps.recursorInfos_steps t)

/-- The restored recursors of a run are the restoration steps at the recursor names, in order. -/
theorem NestedRestorationFolds.rvals_steps {sourceEnv : Environment}
    {types : List InductiveType} {auxRecNames : List Name} {out : Unit × Environment}
    (H : NestedRestorationFolds result loweredEnv sourceEnv auxRec allIndNames types auxRecNames
      out) :
    List.Forall₂ (fun (n : Name) (rv : RecursorVal) => ∃ (s t : Environment)
        (Hs : RestoredRecursorStep result loweredEnv auxRec allIndNames n s t),
        Hs.restored.newInfo = rv)
      (types.map (fun t => Lean.mkRecName t.name) ++ auxRecNames) H.rvals :=
  Lean4Lean.List.Forall₂.append (FoldSteps.inductiveRecs_steps H.inductives)
    (FoldSteps.recursorInfos_steps H.auxiliaries)

/-- The translation of a restored source recursor, in the form of a `recInfo`. -/
theorem SourceRecursorTranslation.trConstVal {decl : VInductDecl} {owner : VInductiveType}
    {safety : DefinitionSafety} {oldRecName : Name} {s t : Environment} {venv : VEnv}
    {Hs : RestoredRecursorStep result loweredEnv auxRec allIndNames oldRecName s t}
    (H : SourceRecursorTranslation decl owner safety Hs venv) :
    TrConstVal safety venv (.recInfo Hs.restored.newInfo) H.recursor := by
  have R := Hs.restored.restoration
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · have h := H.safety_le
    simpa [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, R.isUnsafe]
      using h
  · show Hs.restored.newInfo.levelParams.length = _
    rw [R.levelParams]; exact H.uvars
  · show TrExprS venv Hs.restored.newInfo.levelParams [] Hs.restored.newInfo.type _
    rw [R.levelParams]; exact H.type
  · show Hs.restored.newInfo.name = _
    rw [R.name, H.name]

theorem SourceFamilyTranslations.rvalsTranslated {decl : VInductDecl} {lparams : List Name}
    {safety : DefinitionSafety} {sourceVEnv envTypes envCtors : VEnv} :
    ∀ {types : List InductiveType} {sourceProdEnv targetProdEnv : Environment}
      {Htrace : FoldSteps (RestoredInductiveStep result loweredEnv auxRec allIndNames)
        types sourceProdEnv targetProdEnv} {owners : List VInductiveType}
      {recursors : List VConstVal},
      SourceFamilyTranslations decl lparams safety sourceVEnv envTypes envCtors Htrace owners
        recursors →
      List.Forall₂ (fun (rv : RecursorVal) (v : VConstVal) =>
          TrConstVal safety envCtors (.recInfo rv) v ∧ v.toVConstant.WF envCtors)
        Htrace.inductiveRecs recursors := by
  intro types sourceProdEnv targetProdEnv Htrace owners recursors H
  induction H with
  | nil => exact .nil
  | cons Hstep Htail Hheader Hconstructors Hrecursor Hrest ih =>
    exact .cons ⟨Hrecursor.trConstVal, Hrecursor.wf⟩ ih

theorem AuxiliaryRecursorTranslations.rvalsTranslated {safety : DefinitionSafety}
    {trEnv recursorEnv : VEnv} :
    ∀ {names : List Name} {sourceEnv targetEnv : Environment}
      {Htrace : FoldSteps (RestoredRecursorStep result loweredEnv auxRec allIndNames)
        names sourceEnv targetEnv} {prior final : List VConstVal},
      AuxiliaryRecursorTranslations safety trEnv recursorEnv Htrace prior final →
      ∃ added, final = prior ++ added ∧
        List.Forall₂ (fun (rv : RecursorVal) (v : VConstVal) =>
          TrConstVal safety trEnv (.recInfo rv) v ∧ v.toVConstant.WF recursorEnv)
        Htrace.recursorInfos added := by
  intro names sourceEnv targetEnv Htrace prior final H
  induction H with
  | nil => exact ⟨[], by simp, .nil⟩
  | cons Hstep Htail Hhead Hrest ih =>
    obtain ⟨added, hfinal, hadded⟩ := ih
    exact ⟨Hhead.recursor :: added, by rw [hfinal]; simp,
      .cons ⟨Hhead.translated, Hhead.wf⟩ hadded⟩

end Folds

/-- The restored kernel recursors of the run against the base's abstract recursors, in fold
order: translated, and well formed, in the projection stage of the base. -/
theorem RestoredBlockBase.rvalsTranslated
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    (B : RestoredBlockBase H sourceEnv decl lparams nparams isUnsafe safety) :
    List.Forall₂ (fun (rv : RecursorVal) (v : VConstVal) =>
        TrConstVal safety (B.install.venvCtors.addProjections decl.projectionEntries)
          (.recInfo rv) v ∧
        v.toVConstant.WF (B.install.venvCtors.addProjections decl.projectionEntries))
      H.rvals (B.sourceRecursors ++ B.auxiliaryRecursors) := by
  obtain ⟨added, hfinal, hadded⟩ := B.auxiliaryRecursorTrace.rvalsTranslated
  simp only [List.nil_append] at hfinal
  rw [hfinal]
  exact Lean4Lean.List.Forall₂.append B.sourceTranslations.rvalsTranslated hadded

theorem forall₂_through_map {α β γ δ : Type _} {f : α → β} {R : α → γ → Prop}
    {S : β → δ → Prop} {T : δ → γ → Prop} (h : ∀ a c d, R a c → S (f a) d → T d c) :
    ∀ {l : List α} {lc : List γ} {ld : List δ},
      List.Forall₂ R l lc → List.Forall₂ S (l.map f) ld → List.Forall₂ T ld lc
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h1 t1, .cons h2 t2 => .cons (h _ _ _ h1 h2) (forall₂_through_map h t1 t2)

/-- **The kernel recursors of the run are those of the base's recursor entries, in order**:
both are the restoration steps at the generated recursor names. -/
theorem NestedRun.rvals_recursorEntries
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (hnonempty : sourceTypes ≠ [])
    {entries : List (ConstantInfo × VConstVal)}
    (hinfos : List.Forall₂ (fun owner (entry : ConstantInfo × VConstVal) =>
        ∃ (s t : Environment) (Hstep : RestoredRecursorStep result E.loweredEnv
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
          (sourceTypes.map (·.name))
          (E.lowered.recursors.canonicalGeneration.recursorName owner) s t),
          entry.1 = .recInfo Hstep.restored.newInfo)
      (List.finRange E.lowered.recursors.generationSignature.families.size) entries) :
    List.Forall₂ (fun (rv : RecursorVal) (entry : ConstantInfo × VConstVal) =>
      entry.1 = .recInfo rv) E.restoration.rvals entries := by
  have hsteps := E.restoration.rvals_steps
  rw [← E.recursorNames_order hnonempty] at hsteps
  refine forall₂_through_map ?_ hinfos hsteps
  rintro owner entry rv ⟨s, t, Hs, he⟩ ⟨s', t', Hs', rfl⟩
  rw [he, (Hs.info_eq Hs').2]

end VerifyInductive
end Lean4Lean
