import Lean4Lean.Verify.Inductive.Nested.ConstructorParameterNativePrefix
import Lean4Lean.Verify.Inductive.Nested.Lowering
import Lean4Lean.Verify.Inductive.Nested.CheckedGuardedIota

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- Every member of a successfully traversed list has itself completed
successfully.  This is the small executable inversion needed to select one
constructor from the retained whole-block validation run. -/
private theorem listForM_eq_ok_of_mem
    (step : α → Except ε Unit) :
    ∀ {items : List α}, items.forM step = .ok () →
      ∀ {item}, item ∈ items → step item = .ok () := by
  intro items hrun item hitem
  induction items with
  | nil => simp at hitem
  | cons head tail ih =>
    simp only [List.forM] at hrun
    cases hhead : step head with
    | error err =>
      rw [hhead] at hrun
      simp only [bind, Except.bind] at hrun
      cases hrun
    | ok value =>
      rcases value with ⟨⟩
      rw [hhead] at hrun
      simp only [bind, Except.bind] at hrun
      rcases List.mem_cons.mp hitem with rfl | htail
      · exact hhead
      · exact ih hrun htail

private theorem except_bind_right_of_ok
    {result : Except error alpha} {next : alpha → Except error beta}
    (H : result >>= next = .ok value) :
    ∃ intermediate, result = .ok intermediate ∧
      next intermediate = .ok value := by
  cases result with
  | error err => cases H
  | ok intermediate => exact ⟨intermediate, rfl, H⟩

/-- If a unit-returning first phase and a following phase both succeeded,
then the first phase itself succeeded.  This is used to keep the original
rule-validation projections stable when the executable checker gains an
additional retained-evidence phase. -/
private theorem except_bind_unit_left_of_ok
    {first : Except error Unit} {next : Unit → Except error alpha}
    (H : first >>= next = .ok value) : first = .ok () := by
  cases hfirst : first with
  | error err =>
    rw [hfirst] at H
    cases H
  | ok unit =>
    simpa using hfirst

private theorem forallExists_to_forall₂
    (H : ∀ item ∈ items, ∃ target, relation item target) :
    ∃ targets, List.Forall₂ relation items targets := by
  induction items with
  | nil => exact ⟨[], .nil⟩
  | cons head tail ih =>
    rcases H head (by simp) with ⟨target, Htarget⟩
    rcases ih (fun item hitem => H item (by simp [hitem])) with
      ⟨targets, Htargets⟩
    exact ⟨target :: targets, .cons Htarget Htargets⟩

private theorem validateRestoredConstructorParameters.constructorStep_eq_ok_of_run
    (hrun : Lean4Lean.validateRestoredConstructorParameters.run env lparams
      safety fuel types result = .ok ())
    (htype : indType ∈ types) (hctor : ctor ∈ indType.ctors) :
    (do
      _ ← TypeChecker.M.run env (safety := safety) (lctx := {})
        (lparams := lparams) (fuel := fuel) do
          let type ← TypeChecker.checkType ctor.type
          TypeChecker.ensureSort type ctor.type
      Lean4Lean.validateRestoredConstructorParameters.loop env lparams safety
        fuel result.lctx {} ctor.name result.params ctor.type 0
          fuel.inductiveFuel) = .ok () := by
  unfold Lean4Lean.validateRestoredConstructorParameters.run at hrun
  have hfamily := listForM_eq_ok_of_mem
    (fun type : InductiveType => type.ctors.forM fun ctor => do
      _ ← TypeChecker.M.run env (safety := safety) (lctx := {})
        (lparams := lparams) (fuel := fuel) do
          let type ← TypeChecker.checkType ctor.type
          TypeChecker.ensureSort type ctor.type
      Lean4Lean.validateRestoredConstructorParameters.loop env lparams safety
        fuel result.lctx {} ctor.name result.params ctor.type 0
          fuel.inductiveFuel)
    hrun htype
  have hconstructor := listForM_eq_ok_of_mem
    (fun ctor : Constructor => do
      _ ← TypeChecker.M.run env (safety := safety) (lctx := {})
        (lparams := lparams) (fuel := fuel) do
          let type ← TypeChecker.checkType ctor.type
          TypeChecker.ensureSort type ctor.type
      Lean4Lean.validateRestoredConstructorParameters.loop env lparams safety
        fuel result.lctx {} ctor.name result.params ctor.type 0
          fuel.inductiveFuel)
    hfamily hctor
  exact hconstructor

/-- Select the exact successful source-type certification run for one
constructor from the retained whole-block validation trace. -/
theorem validateRestoredConstructorParameters.typeCheck_eq_ok_of_run
    (hrun : Lean4Lean.validateRestoredConstructorParameters.run env lparams
      safety fuel types result = .ok ())
    (htype : indType ∈ types) (hctor : ctor ∈ indType.ctors) :
    ∃ checked, TypeChecker.M.run env (safety := safety) (lctx := {})
      (lparams := lparams) (fuel := fuel) (do
        let type ← TypeChecker.checkType ctor.type
        TypeChecker.ensureSort type ctor.type) = .ok checked := by
  have hconstructor :=
    validateRestoredConstructorParameters.constructorStep_eq_ok_of_run
      hrun htype hctor
  cases hcheck : TypeChecker.M.run env (safety := safety) (lctx := {})
      (lparams := lparams) (fuel := fuel)
      (do
        let type ← TypeChecker.checkType ctor.type
        TypeChecker.ensureSort type ctor.type) with
  | error err =>
    rw [hcheck] at hconstructor
    cases hconstructor
  | ok checked =>
    exact ⟨checked, rfl⟩

/-- Select the exact common-parameter-prefix run for one source constructor
from the successful native validation of the complete mutual block. -/
theorem validateRestoredConstructorParameters.loop_eq_ok_of_run
    (hrun : Lean4Lean.validateRestoredConstructorParameters.run env lparams
      safety fuel types result = .ok ())
    (htype : indType ∈ types) (hctor : ctor ∈ indType.ctors) :
    Lean4Lean.validateRestoredConstructorParameters.loop env lparams safety
      fuel result.lctx {} ctor.name result.params ctor.type 0
        fuel.inductiveFuel = .ok () := by
  have hconstructor :=
    validateRestoredConstructorParameters.constructorStep_eq_ok_of_run
      hrun htype hctor
  cases hcheck : TypeChecker.M.run env (safety := safety) (lctx := {})
      (lparams := lparams) (fuel := fuel)
      (do
        let type ← TypeChecker.checkType ctor.type
        TypeChecker.ensureSort type ctor.type) with
  | error err =>
    rw [hcheck] at hconstructor
    cases hconstructor
  | ok checked =>
    rw [hcheck] at hconstructor
    simpa only [bind, Except.bind] using hconstructor

/-- The executable source-type check constructs the abstract source constant
needed by constructor restoration.  This is derived from the successful
runtime trace, rather than supplied as final-assembly evidence. -/
theorem validateRestoredConstructorParameters.sourceConst_of_run
    (hvalid : CheckingEnv.Valid safety env venv)
    (Hsources : SourceSyntaxChecks types)
    (hrun : Lean4Lean.validateRestoredConstructorParameters.run env lparams
      safety fuel types result = .ok ())
    (htype : indType ∈ types) (hctor : ctor ∈ indType.ctors) :
    ∃ constructor : VConstVal,
      TrSourceConst venv lparams ctor.name ctor.type constructor := by
  rcases validateRestoredConstructorParameters.typeCheck_eq_ok_of_run
      hrun htype hctor with ⟨checked, hcheck⟩
  have hclosed := Hsources.constructorsClosed htype ctor hctor
  have hfvars : ctor.type.FVarsIn fun fv => fv ∈
      (TypeChecker.VContext.mkCheckingValid hvalid lparams fuel).vlctx.fvars := by
    simpa [TypeChecker.VContext.mkCheckingValid,
      TypeChecker.VContext.mkChecking] using hclosed
  have Hcheck : (do
      let type ← TypeChecker.checkType ctor.type
      TypeChecker.ensureSort type ctor.type).WF
      (TypeChecker.VContext.mkCheckingValid hvalid lparams fuel) {}
      fun _ _ => ∃ type', TrExprS venv lparams [] ctor.type type' ∧
        venv.IsType lparams.length [] type' := by
    refine (TypeChecker.checkType.WF (e := ctor.type) hfvars).bind
      fun _ _ _ ⟨type', sort', _, htype, hsort, hhasType⟩ => ?_
    refine (TypeChecker.ensureSort.WF hsort).mono
      fun _ _ _ ⟨⟨_, hsort', hdefeq⟩, hsortEq⟩ => ?_
    obtain ⟨u, rfl⟩ := hsortEq
    cases hsort' with
    | sort hu =>
      exact ⟨type', htype,
        ⟨_, hhasType.defeqU_r hvalid.tr.wf (by trivial) hdefeq.symm⟩⟩
  have Hrun := TypeChecker.M.WF.runCheckingValid Hcheck
  rcases Hrun checked hcheck with ⟨type', Htype, HtypeWF⟩
  let constructor : VConstVal := {
    uvars := lparams.length
    name := ctor.name
    type := type' }
  exact ⟨constructor, ⟨rfl, rfl, Htype, HtypeWF⟩⟩

/-- Pointwise source-type certification for a family, packaged in the exact
constructor-list shape consumed by the nested restoration semantics. -/
theorem validateRestoredConstructorParameters.sourceConsts_of_run
    (hvalid : CheckingEnv.Valid safety env venv)
    (Hsources : SourceSyntaxChecks types)
    (hrun : Lean4Lean.validateRestoredConstructorParameters.run env lparams
      safety fuel types result = .ok ())
    (htype : indType ∈ types) :
    ∃ constructors : List VConstVal,
      List.Forall₂ (fun source constructor =>
        TrSourceConst venv lparams source.name source.type constructor)
        indType.ctors constructors := by
  apply forallExists_to_forall₂
  intro ctor hctor
  exact validateRestoredConstructorParameters.sourceConst_of_run hvalid
    Hsources hrun htype hctor

private theorem validateRestoredRecursorTypes.primaryCheck_eq_ok_of_run
    (hrun : Lean4Lean.validateRestoredRecursorTypes.run env loweredEnv lparams
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (htype : indType ∈ types) :
    Lean4Lean.validateRestoredRecursorTypes.check env loweredEnv lparams
      safety fuel result recNameMap allIndNames (Lean.mkRecName indType.name) =
        .ok () := by
  unfold Lean4Lean.validateRestoredRecursorTypes.run at hrun
  cases hprimary : types.forM fun type =>
      Lean4Lean.validateRestoredRecursorTypes.check env loweredEnv lparams
        safety fuel result recNameMap allIndNames
          (Lean.mkRecName type.name) with
  | error err =>
      rw [hprimary] at hrun
      simp only [bind, Except.bind] at hrun
      cases hrun
  | ok unit =>
      rcases unit with ⟨⟩
      exact listForM_eq_ok_of_mem
        (fun type : InductiveType =>
          Lean4Lean.validateRestoredRecursorTypes.check env loweredEnv lparams
            safety fuel result recNameMap allIndNames
              (Lean.mkRecName type.name)) hprimary htype

/-- Select the exact successful source-side type-checking run for one primary
restored recursor from the retained whole-block validation pass. -/
theorem validateRestoredRecursorTypes.typeCheck_eq_ok_of_run
    (hrun : Lean4Lean.validateRestoredRecursorTypes.run env loweredEnv lparams
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (htype : indType ∈ types)
    (hlookup : loweredEnv.find? (Lean.mkRecName indType.name) =
      some (.recInfo oldInfo)) :
    let newRecName := recNameMap.getD (Lean.mkRecName indType.name)
      (Lean.mkRecName indType.name)
    let restored := result.restoreRecursor loweredEnv recNameMap allIndNames
      (Lean.mkRecName indType.name) newRecName oldInfo
    ∃ checked,
      env.checkNoMVarNoFVar restored.name restored.type = .ok () ∧
      TypeChecker.M.run env (safety := safety) (lctx := {})
        (lparams := restored.levelParams) (fuel := fuel) (do
          let type ← TypeChecker.checkType restored.type
          TypeChecker.ensureSort type restored.type) = .ok checked := by
  dsimp only
  have hcheck :=
    validateRestoredRecursorTypes.primaryCheck_eq_ok_of_run hrun htype
  unfold Lean4Lean.validateRestoredRecursorTypes.check at hcheck
  rw [hlookup] at hcheck
  simp only at hcheck
  cases hclosed : env.checkNoMVarNoFVar
      (result.restoreRecursor loweredEnv recNameMap allIndNames
        (Lean.mkRecName indType.name)
        (recNameMap.getD (Lean.mkRecName indType.name)
          (Lean.mkRecName indType.name)) oldInfo).name
      (result.restoreRecursor loweredEnv recNameMap allIndNames
        (Lean.mkRecName indType.name)
        (recNameMap.getD (Lean.mkRecName indType.name)
          (Lean.mkRecName indType.name)) oldInfo).type with
  | error err =>
      rw [hclosed] at hcheck
      simp only [bind, Except.bind] at hcheck
      cases hcheck
  | ok unit =>
      rcases unit with ⟨⟩
      cases htypecheck : TypeChecker.M.run env (safety := safety) (lctx := {})
          (lparams := (result.restoreRecursor loweredEnv recNameMap allIndNames
            (Lean.mkRecName indType.name)
            (recNameMap.getD (Lean.mkRecName indType.name)
              (Lean.mkRecName indType.name)) oldInfo).levelParams)
          (fuel := fuel) (do
            let type ← TypeChecker.checkType
              (result.restoreRecursor loweredEnv recNameMap allIndNames
                (Lean.mkRecName indType.name)
                (recNameMap.getD (Lean.mkRecName indType.name)
                  (Lean.mkRecName indType.name)) oldInfo).type
            TypeChecker.ensureSort type
              (result.restoreRecursor loweredEnv recNameMap allIndNames
                (Lean.mkRecName indType.name)
                (recNameMap.getD (Lean.mkRecName indType.name)
                  (Lean.mkRecName indType.name)) oldInfo).type) with
      | error err =>
          rw [hclosed, htypecheck] at hcheck
          simp only [bind, Except.bind] at hcheck
          cases hcheck
      | ok checked => exact ⟨checked, by simpa using hclosed, rfl⟩

/-- The executable recursor-type pass yields a source-environment
translation and typehood certificate for the exact restored primary type. -/
theorem validateRestoredRecursorTypes.translation_of_run
    (hvalid : CheckingEnv.Valid safety env venv)
    (hrun : Lean4Lean.validateRestoredRecursorTypes.run env loweredEnv lparams
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (htype : indType ∈ types)
    (hlookup : loweredEnv.find? (Lean.mkRecName indType.name) =
      some (.recInfo oldInfo)) :
    let newRecName := recNameMap.getD (Lean.mkRecName indType.name)
      (Lean.mkRecName indType.name)
    let restored := result.restoreRecursor loweredEnv recNameMap allIndNames
      (Lean.mkRecName indType.name) newRecName oldInfo
    ∃ target, TrExprS venv restored.levelParams [] restored.type target ∧
      venv.IsType restored.levelParams.length [] target := by
  dsimp only
  let restored := result.restoreRecursor loweredEnv recNameMap allIndNames
    (Lean.mkRecName indType.name)
    (recNameMap.getD (Lean.mkRecName indType.name)
      (Lean.mkRecName indType.name)) oldInfo
  rcases validateRestoredRecursorTypes.typeCheck_eq_ok_of_run hrun htype
      hlookup with ⟨checked, hclosedRunFull, hcheck⟩
  have hclosedRun : env.checkNoMVarNoFVar restored.name restored.type =
      .ok () := by
    simpa only [restored] using hclosedRunFull
  have hclosed : restored.type.FVarsIn fun _ => False :=
    checkNoMVarNoFVar.closed hclosedRun
  have hfvars : restored.type.FVarsIn fun fv => fv ∈
      (TypeChecker.VContext.mkCheckingValid hvalid restored.levelParams
        fuel).vlctx.fvars := by
    simpa [TypeChecker.VContext.mkCheckingValid,
      TypeChecker.VContext.mkChecking] using hclosed
  have Hcheck : (do
      let type ← TypeChecker.checkType restored.type
      TypeChecker.ensureSort type restored.type).WF
      (TypeChecker.VContext.mkCheckingValid hvalid restored.levelParams fuel) {}
      fun _ _ => ∃ type', TrExprS venv restored.levelParams []
          restored.type type' ∧
        venv.IsType restored.levelParams.length [] type' := by
    refine (TypeChecker.checkType.WF (e := restored.type) hfvars).bind
      fun _ _ _ ⟨type', sort', _, htype, hsort, hhasType⟩ => ?_
    refine (TypeChecker.ensureSort.WF hsort).mono
      fun _ _ _ ⟨⟨_, hsort', hdefeq⟩, hsortEq⟩ => ?_
    obtain ⟨u, rfl⟩ := hsortEq
    cases hsort' with
    | sort hu =>
      exact ⟨type', htype,
        ⟨_, hhasType.defeqU_r hvalid.tr.wf (by trivial) hdefeq.symm⟩⟩
  have Hrun := TypeChecker.M.WF.runCheckingValid Hcheck
  exact Hrun checked hcheck

private theorem validateRestoredRecursorTypes.auxiliaryCheck_eq_ok_of_run
    (hrun : Lean4Lean.validateRestoredRecursorTypes.run env loweredEnv lparams
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (hrec : recName ∈ auxRecNames) :
    Lean4Lean.validateRestoredRecursorTypes.check env loweredEnv lparams
      safety fuel result recNameMap allIndNames recName = .ok () := by
  unfold Lean4Lean.validateRestoredRecursorTypes.run at hrun
  cases hprimary : types.forM fun type =>
      Lean4Lean.validateRestoredRecursorTypes.check env loweredEnv lparams
        safety fuel result recNameMap allIndNames
          (Lean.mkRecName type.name) with
  | error err =>
      rw [hprimary] at hrun
      simp only [bind, Except.bind] at hrun
      cases hrun
  | ok unit =>
      rcases unit with ⟨⟩
      rw [hprimary] at hrun
      simp only [bind, Except.bind] at hrun
      exact listForM_eq_ok_of_mem
        (Lean4Lean.validateRestoredRecursorTypes.check env loweredEnv lparams
          safety fuel result recNameMap allIndNames) hrun hrec

/-- A successful exact check of any restored recursor (primary or auxiliary)
yields translation and typehood for the concrete value produced by
`restoreRecursor`. -/
theorem validateRestoredRecursorTypes.translation_of_check
    (hvalid : CheckingEnv.Valid safety env venv)
    (hstep : Lean4Lean.validateRestoredRecursorTypes.check env loweredEnv
      lparams safety fuel result recNameMap allIndNames recName = .ok ())
    (hlookup : loweredEnv.find? recName = some (.recInfo oldInfo)) :
    let newRecName := recNameMap.getD recName recName
    let restored := result.restoreRecursor loweredEnv recNameMap allIndNames
      recName newRecName oldInfo
    ∃ target, TrExprS venv restored.levelParams [] restored.type target ∧
      venv.IsType restored.levelParams.length [] target := by
  dsimp only
  let restored := result.restoreRecursor loweredEnv recNameMap allIndNames
    recName (recNameMap.getD recName recName) oldInfo
  unfold Lean4Lean.validateRestoredRecursorTypes.check at hstep
  rw [hlookup] at hstep
  simp only at hstep
  have hclosedRun : env.checkNoMVarNoFVar restored.name restored.type =
      .ok () := by
    cases hclosed : env.checkNoMVarNoFVar restored.name restored.type with
    | error err =>
        rw [hclosed] at hstep
        simp only [bind, Except.bind] at hstep
        cases hstep
    | ok unit =>
        rcases unit with ⟨⟩
        simpa using hclosed
  have hclosed : restored.type.FVarsIn fun _ => False :=
    checkNoMVarNoFVar.closed hclosedRun
  have hfvars : restored.type.FVarsIn fun fv => fv ∈
      (TypeChecker.VContext.mkCheckingValid hvalid restored.levelParams
        fuel).vlctx.fvars := by
    simpa [TypeChecker.VContext.mkCheckingValid,
      TypeChecker.VContext.mkChecking] using hclosed
  have Hcheck : (do
      let type ← TypeChecker.checkType restored.type
      TypeChecker.ensureSort type restored.type).WF
      (TypeChecker.VContext.mkCheckingValid hvalid restored.levelParams fuel) {}
      fun _ _ => ∃ type', TrExprS venv restored.levelParams []
          restored.type type' ∧
        venv.IsType restored.levelParams.length [] type' := by
    refine (TypeChecker.checkType.WF (e := restored.type) hfvars).bind
      fun _ _ _ ⟨type', sort', _, htype, hsort, hhasType⟩ => ?_
    refine (TypeChecker.ensureSort.WF hsort).mono
      fun _ _ _ ⟨⟨_, hsort', hdefeq⟩, hsortEq⟩ => ?_
    obtain ⟨u, rfl⟩ := hsortEq
    cases hsort' with
    | sort hu =>
      exact ⟨type', htype,
        ⟨_, hhasType.defeqU_r hvalid.tr.wf (by trivial) hdefeq.symm⟩⟩
  have Hrun := TypeChecker.M.WF.runCheckingValid Hcheck
  cases htypecheck : TypeChecker.M.run env (safety := safety) (lctx := {})
      (lparams := restored.levelParams) (fuel := fuel) (do
        let type ← TypeChecker.checkType restored.type
        TypeChecker.ensureSort type restored.type) with
  | error err =>
      rw [hclosedRun, htypecheck] at hstep
      simp only [bind, Except.bind] at hstep
      cases hstep
  | ok checked => exact Hrun checked htypecheck

/-- Select and certify one auxiliary restored recursor from the successful
whole-block validation pass. -/
theorem validateRestoredRecursorTypes.auxiliaryTranslation_of_run
    (hvalid : CheckingEnv.Valid safety env venv)
    (hrun : Lean4Lean.validateRestoredRecursorTypes.run env loweredEnv lparams
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (hrec : recName ∈ auxRecNames)
    (hlookup : loweredEnv.find? recName = some (.recInfo oldInfo)) :
    let newRecName := recNameMap.getD recName recName
    let restored := result.restoreRecursor loweredEnv recNameMap allIndNames
      recName newRecName oldInfo
    ∃ target, TrExprS venv restored.levelParams [] restored.type target ∧
      venv.IsType restored.levelParams.length [] target := by
  exact validateRestoredRecursorTypes.translation_of_check hvalid
    (validateRestoredRecursorTypes.auxiliaryCheck_eq_ok_of_run hrun hrec)
      hlookup

private theorem validateRestoredRecursorRules.primaryFullCheck_eq_ok_of_run
    (hrun : Lean4Lean.validateRestoredRecursorRules.run env loweredEnv lparams
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (htype : indType ∈ types) :
    Lean4Lean.validateRestoredRecursorRules.checkPrimary env loweredEnv lparams
      safety fuel result recNameMap allIndNames auxRecNames
        (Lean.mkRecName indType.name) = .ok () := by
  unfold Lean4Lean.validateRestoredRecursorRules.run at hrun
  cases hprimary : types.forM fun type =>
      Lean4Lean.validateRestoredRecursorRules.checkPrimary env loweredEnv lparams
        safety fuel result recNameMap allIndNames auxRecNames
          (Lean.mkRecName type.name) with
  | error err =>
      rw [hprimary] at hrun
      simp only [bind, Except.bind] at hrun
      cases hrun
  | ok unit =>
      rcases unit with ⟨⟩
      exact listForM_eq_ok_of_mem
        (fun type : InductiveType =>
          Lean4Lean.validateRestoredRecursorRules.checkPrimary env loweredEnv lparams
            safety fuel result recNameMap allIndNames auxRecNames
              (Lean.mkRecName type.name)) hprimary htype

private theorem validateRestoredRecursorRules.primaryCheck_eq_ok_of_run
    (hrun : Lean4Lean.validateRestoredRecursorRules.run env loweredEnv lparams
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (htype : indType ∈ types) :
    Lean4Lean.validateRestoredRecursorRules.check env loweredEnv lparams
      safety fuel result recNameMap allIndNames auxRecNames
        (Lean.mkRecName indType.name) = .ok () := by
  have hfull :=
    validateRestoredRecursorRules.primaryFullCheck_eq_ok_of_run hrun htype
  unfold Lean4Lean.validateRestoredRecursorRules.checkPrimary at hfull
  cases hcommon : Lean4Lean.validateRestoredRecursorRules.check env loweredEnv
      lparams safety fuel result recNameMap allIndNames auxRecNames
        (Lean.mkRecName indType.name) with
  | error err => simp [hcommon, bind, Except.bind] at hfull
  | ok unit =>
      cases unit
      simpa using hcommon

private theorem validateRestoredRecursorRules.auxiliaryCheck_eq_ok_of_run
    (hrun : Lean4Lean.validateRestoredRecursorRules.run env loweredEnv lparams
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (hrec : recName ∈ auxRecNames) :
    Lean4Lean.validateRestoredRecursorRules.check env loweredEnv lparams
      safety fuel result recNameMap allIndNames auxRecNames recName = .ok () := by
  unfold Lean4Lean.validateRestoredRecursorRules.run at hrun
  cases hprimary : types.forM fun type =>
      Lean4Lean.validateRestoredRecursorRules.checkPrimary env loweredEnv lparams
        safety fuel result recNameMap allIndNames auxRecNames
          (Lean.mkRecName type.name) with
  | error err =>
      rw [hprimary] at hrun
      simp only [bind, Except.bind] at hrun
      cases hrun
  | ok unit =>
      rcases unit with ⟨⟩
      rw [hprimary] at hrun
      simp only [bind, Except.bind] at hrun
      exact listForM_eq_ok_of_mem
        (Lean4Lean.validateRestoredRecursorRules.check env loweredEnv lparams
          safety fuel result recNameMap allIndNames auxRecNames) hrun hrec

/-- Select the literal equation-validation execution for one restored rule
from the successful per-recursor validation pass.  The preceding closure and
ordinary RHS type checks are eliminated from the same monadic trace; no
equation evidence is supplied independently. -/
theorem validateRestoredRecursorRules.equationCheck_eq_ok_of_check
    (hstep : Lean4Lean.validateRestoredRecursorRules.check env loweredEnv
      lparams safety fuel result recNameMap allIndNames auxRecNames recName =
        .ok ())
    (hlookup : loweredEnv.find? recName = some (.recInfo oldInfo))
    (hrule : rule ∈
      (result.restoreRecursor loweredEnv recNameMap allIndNames recName
        (recNameMap.getD recName recName) oldInfo).rules) :
    TypeChecker.M.run env (safety := safety) (lctx := {})
      (lparams :=
        (result.restoreRecursor loweredEnv recNameMap allIndNames recName
          (recNameMap.getD recName recName) oldInfo).levelParams)
      (fuel := fuel)
      (Lean4Lean.validateRestoredRecursorRules.checkEquation
        (result.restoreRecursor loweredEnv recNameMap allIndNames recName
          (recNameMap.getD recName recName) oldInfo) rule) = .ok () := by
  let restored := result.restoreRecursor loweredEnv recNameMap allIndNames
    recName (recNameMap.getD recName recName) oldInfo
  let restoredRecursorNames :=
    allIndNames.map (fun name =>
      let oldName := Lean.mkRecName name
      recNameMap.getD oldName oldName) ++
    auxRecNames.map fun oldName => recNameMap.getD oldName oldName
  unfold Lean4Lean.validateRestoredRecursorRules.check at hstep
  rw [hlookup] at hstep
  simp only at hstep
  have hvalidated := except_bind_unit_left_of_ok hstep
  have hruleFull : (do
      env.checkNoMVarNoFVar restored.name rule.rhs
      _ ← TypeChecker.M.run env (safety := safety) (lctx := {})
        (lparams := restored.levelParams) (fuel := fuel) do
          TypeChecker.checkType rule.rhs
      _ ← TypeChecker.M.run env (safety := safety) (lctx := {})
        (lparams := restored.levelParams) (fuel := fuel) do
          Lean4Lean.validateRestoredRecursorRules.checkEquation restored rule
      Lean4Lean.validateRestoredRecursorRules.checkGuarded
        restoredRecursorNames rule.rhs) =
        .ok () := by
    apply listForM_eq_ok_of_mem
      (fun candidate : RecursorRule => do
        env.checkNoMVarNoFVar restored.name candidate.rhs
        _ ← TypeChecker.M.run env (safety := safety) (lctx := {})
          (lparams := restored.levelParams) (fuel := fuel) do
            TypeChecker.checkType candidate.rhs
        _ ← TypeChecker.M.run env (safety := safety) (lctx := {})
          (lparams := restored.levelParams) (fuel := fuel) do
            Lean4Lean.validateRestoredRecursorRules.checkEquation restored
              candidate
        Lean4Lean.validateRestoredRecursorRules.checkGuarded
          restoredRecursorNames candidate.rhs)
    · simpa only [restored] using hvalidated
    · simpa only [restored] using hrule
  cases hclosed : env.checkNoMVarNoFVar restored.name rule.rhs with
  | error err =>
      rw [hclosed] at hruleFull
      cases hruleFull
  | ok unit =>
      rcases unit with ⟨⟩
      rw [hclosed] at hruleFull
      cases htype : TypeChecker.M.run env (safety := safety) (lctx := {})
          (lparams := restored.levelParams) (fuel := fuel)
          (TypeChecker.checkType rule.rhs) with
      | error err =>
          rw [htype] at hruleFull
          cases hruleFull
      | ok inferred =>
          rw [htype] at hruleFull
          simp only [bind, Except.bind] at hruleFull
          cases hequation : TypeChecker.M.run env (safety := safety)
              (lctx := {}) (lparams := restored.levelParams) (fuel := fuel)
              (Lean4Lean.validateRestoredRecursorRules.checkEquation restored
                rule) with
          | error err =>
              rw [hequation] at hruleFull
              cases hruleFull
          | ok unit =>
              rcases unit with ⟨⟩
              simpa only [restored] using hequation

/-- Select the literal guardedness validation for one restored rule from the
same successful per-recursor pass.  The recursor-name set is computed by the
implementation from the source family names and the actual auxiliary rename
map. -/
theorem validateRestoredRecursorRules.guardCheck_eq_ok_of_check
    (hstep : Lean4Lean.validateRestoredRecursorRules.check env loweredEnv
      lparams safety fuel result recNameMap allIndNames auxRecNames recName =
        .ok ())
    (hlookup : loweredEnv.find? recName = some (.recInfo oldInfo))
    (hrule : rule ∈
      (result.restoreRecursor loweredEnv recNameMap allIndNames recName
        (recNameMap.getD recName recName) oldInfo).rules) :
    let restoredRecursorNames :=
      allIndNames.map (fun name =>
        let oldName := Lean.mkRecName name
        recNameMap.getD oldName oldName) ++
      auxRecNames.map fun oldName => recNameMap.getD oldName oldName
    Lean4Lean.validateRestoredRecursorRules.checkGuarded
      restoredRecursorNames rule.rhs = .ok () := by
  dsimp only
  let restored := result.restoreRecursor loweredEnv recNameMap allIndNames
    recName (recNameMap.getD recName recName) oldInfo
  let restoredRecursorNames :=
    allIndNames.map (fun name =>
      let oldName := Lean.mkRecName name
      recNameMap.getD oldName oldName) ++
    auxRecNames.map fun oldName => recNameMap.getD oldName oldName
  unfold Lean4Lean.validateRestoredRecursorRules.check at hstep
  rw [hlookup] at hstep
  simp only at hstep
  have hvalidated := except_bind_unit_left_of_ok hstep
  have hruleFull : (do
      env.checkNoMVarNoFVar restored.name rule.rhs
      _ ← TypeChecker.M.run env (safety := safety) (lctx := {})
        (lparams := restored.levelParams) (fuel := fuel) do
          TypeChecker.checkType rule.rhs
      _ ← TypeChecker.M.run env (safety := safety) (lctx := {})
        (lparams := restored.levelParams) (fuel := fuel) do
          Lean4Lean.validateRestoredRecursorRules.checkEquation restored rule
      Lean4Lean.validateRestoredRecursorRules.checkGuarded
        restoredRecursorNames rule.rhs) = .ok () := by
    apply listForM_eq_ok_of_mem
      (fun candidate : RecursorRule => do
        env.checkNoMVarNoFVar restored.name candidate.rhs
        _ ← TypeChecker.M.run env (safety := safety) (lctx := {})
          (lparams := restored.levelParams) (fuel := fuel) do
            TypeChecker.checkType candidate.rhs
        _ ← TypeChecker.M.run env (safety := safety) (lctx := {})
          (lparams := restored.levelParams) (fuel := fuel) do
            Lean4Lean.validateRestoredRecursorRules.checkEquation restored
              candidate
        Lean4Lean.validateRestoredRecursorRules.checkGuarded
          restoredRecursorNames candidate.rhs)
    · simpa only [restored, restoredRecursorNames] using hvalidated
    · simpa only [restored] using hrule
  rcases except_bind_right_of_ok hruleFull with
    ⟨_, _hclosed, hafterClosed⟩
  rcases except_bind_right_of_ok hafterClosed with
    ⟨_, _htyped, hafterTyped⟩
  rcases except_bind_right_of_ok hafterTyped with
    ⟨_, _hequation, hguarded⟩
  simpa only [restoredRecursorNames] using hguarded

/-- Select the producer-derived exact-field guard pass for one source rule.
The restored expression is definitionally the output of the same
`restoreRule` call used to build the restored recursor, and the field list is
computed only from majors of source recursor calls. -/
theorem validateRestoredRecursorRules.exactGuardCheck_eq_ok_of_check
    (hstep : Lean4Lean.validateRestoredRecursorRules.checkPrimary env loweredEnv
      lparams safety fuel result recNameMap allIndNames auxRecNames recName =
        .ok ())
    (hlookup : loweredEnv.find? recName = some (.recInfo oldInfo))
    (hsource : sourceRule ∈ oldInfo.rules) :
    let newRecName := recNameMap.getD recName recName
    let restoredRecursorNames :=
      allIndNames.map (fun name =>
        let oldName := Lean.mkRecName name
        recNameMap.getD oldName oldName) ++
      auxRecNames.map fun oldName => recNameMap.getD oldName oldName
    let sourceRecursorNames := allIndNames.map Lean.mkRecName ++ auxRecNames
    Lean4Lean.validateRestoredRecursorRules.checkGuardedWithFieldsAtArity
      restoredRecursorNames
      (Lean4Lean.validateRestoredRecursorRules.recursiveFieldVars
        sourceRecursorNames sourceRule.rhs)
      sourceRule.rhs.getNumHeadLambdas
      (result.restoreRule loweredEnv recNameMap recName newRecName
        sourceRule).rhs = .ok () := by
  dsimp only
  let newRecName := recNameMap.getD recName recName
  let restored := result.restoreRecursor loweredEnv recNameMap allIndNames
    recName newRecName oldInfo
  let restoredRecursorNames :=
    allIndNames.map (fun name =>
      let oldName := Lean.mkRecName name
      recNameMap.getD oldName oldName) ++
    auxRecNames.map fun oldName => recNameMap.getD oldName oldName
  let sourceRecursorNames := allIndNames.map Lean.mkRecName ++ auxRecNames
  unfold Lean4Lean.validateRestoredRecursorRules.checkPrimary at hstep
  have hcommonOk : Lean4Lean.validateRestoredRecursorRules.check env loweredEnv
      lparams safety fuel result recNameMap allIndNames auxRecNames recName =
        .ok () := by
    cases hcommon : Lean4Lean.validateRestoredRecursorRules.check env loweredEnv
        lparams safety fuel result recNameMap allIndNames auxRecNames recName with
    | error err => simp [hcommon, bind, Except.bind] at hstep
    | ok unit => cases unit; rfl
  rw [hcommonOk] at hstep
  simp only [bind, Except.bind] at hstep
  rw [hlookup] at hstep
  simp only at hstep
  rcases except_bind_right_of_ok hstep with
    ⟨primaryUnit, hprimaryLoop, _hshapeLoop⟩
  rcases primaryUnit with ⟨⟩
  apply listForM_eq_ok_of_mem
    (fun candidate : RecursorRule =>
      Lean4Lean.validateRestoredRecursorRules.checkGuardedWithFieldsAtArity
        restoredRecursorNames
        (Lean4Lean.validateRestoredRecursorRules.recursiveFieldVars
          sourceRecursorNames candidate.rhs)
        candidate.rhs.getNumHeadLambdas
        (result.restoreRule loweredEnv recNameMap recName newRecName
          candidate).rhs)
  · simpa only [restored, restoredRecursorNames, sourceRecursorNames,
      newRecName] using hprimaryLoop
  · exact hsource

/-- Whole-run primary specialization of the exact producer-field guard
pass.  The source rule is selected from the lowered recursor metadata; its
restored endpoint is therefore the literal rule installed by the same
restoration trace. -/
theorem validateRestoredRecursorRules.primaryExactGuardCheck_of_run
    (hrun : Lean4Lean.validateRestoredRecursorRules.run env loweredEnv lparams
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (htype : indType ∈ types)
    (hlookup : loweredEnv.find? (Lean.mkRecName indType.name) =
      some (.recInfo oldInfo))
    (hsource : sourceRule ∈ oldInfo.rules) :
    let oldRecName := Lean.mkRecName indType.name
    let newRecName := recNameMap.getD oldRecName oldRecName
    let restoredRecursorNames :=
      allIndNames.map (fun name =>
        let oldName := Lean.mkRecName name
        recNameMap.getD oldName oldName) ++
      auxRecNames.map fun oldName => recNameMap.getD oldName oldName
    let sourceRecursorNames := allIndNames.map Lean.mkRecName ++ auxRecNames
    Lean4Lean.validateRestoredRecursorRules.checkGuardedWithFieldsAtArity
      restoredRecursorNames
      (Lean4Lean.validateRestoredRecursorRules.recursiveFieldVars
        sourceRecursorNames sourceRule.rhs)
      sourceRule.rhs.getNumHeadLambdas
      (result.restoreRule loweredEnv recNameMap oldRecName newRecName
        sourceRule).rhs = .ok () := by
  dsimp only
  exact validateRestoredRecursorRules.exactGuardCheck_eq_ok_of_check
    (validateRestoredRecursorRules.primaryFullCheck_eq_ok_of_run hrun htype)
      hlookup hsource

/-- Select the exact primary spine/field validation from the same successful
per-recursor pass. -/
theorem validateRestoredRecursorRules.primaryShapeCheck_eq_ok_of_check
    (hstep : Lean4Lean.validateRestoredRecursorRules.checkPrimary env loweredEnv
      lparams safety fuel result recNameMap allIndNames auxRecNames recName =
        .ok ())
    (hlookup : loweredEnv.find? recName = some (.recInfo oldInfo))
    (hsource : sourceRule ∈ oldInfo.rules) :
    let newRecName := recNameMap.getD recName recName
    let restored := result.restoreRecursor loweredEnv recNameMap allIndNames
      recName newRecName oldInfo
    let sourceRecursorNames := allIndNames.map Lean.mkRecName ++ auxRecNames
    Lean4Lean.validateRestoredRecursorRules.checkPrimaryRuleShape restored
      sourceRecursorNames sourceRule
        (result.restoreRule loweredEnv recNameMap recName newRecName
          sourceRule) = .ok () := by
  dsimp only
  let newRecName := recNameMap.getD recName recName
  let restored := result.restoreRecursor loweredEnv recNameMap allIndNames
    recName newRecName oldInfo
  let restoredRecursorNames :=
    allIndNames.map (fun name =>
      let oldName := Lean.mkRecName name
      recNameMap.getD oldName oldName) ++
    auxRecNames.map fun oldName => recNameMap.getD oldName oldName
  let sourceRecursorNames := allIndNames.map Lean.mkRecName ++ auxRecNames
  unfold Lean4Lean.validateRestoredRecursorRules.checkPrimary at hstep
  have hcommonOk : Lean4Lean.validateRestoredRecursorRules.check env loweredEnv
      lparams safety fuel result recNameMap allIndNames auxRecNames recName =
        .ok () := by
    cases hcommon : Lean4Lean.validateRestoredRecursorRules.check env loweredEnv
        lparams safety fuel result recNameMap allIndNames auxRecNames recName with
    | error err => simp [hcommon, bind, Except.bind] at hstep
    | ok unit => cases unit; rfl
  rw [hcommonOk] at hstep
  simp only [bind, Except.bind] at hstep
  rw [hlookup] at hstep
  simp only at hstep
  rcases except_bind_right_of_ok hstep with
    ⟨guardUnit, _hguardLoop, hafterGuard⟩
  rcases guardUnit with ⟨⟩
  rcases except_bind_right_of_ok hafterGuard with
    ⟨shapeUnit, hshapeLoop, _hreturn⟩
  rcases shapeUnit with ⟨⟩
  apply listForM_eq_ok_of_mem
    (fun candidate : RecursorRule =>
      Lean4Lean.validateRestoredRecursorRules.checkPrimaryRuleShape
        restored sourceRecursorNames candidate
          (result.restoreRule loweredEnv recNameMap recName newRecName
            candidate))
  · simpa only [restored, restoredRecursorNames, sourceRecursorNames,
      newRecName] using hshapeLoop
  · exact hsource

/-- Whole-run primary specialization of the exact spine/field pass. -/
theorem validateRestoredRecursorRules.primaryShapeCheck_of_run
    (hrun : Lean4Lean.validateRestoredRecursorRules.run env loweredEnv lparams
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (htype : indType ∈ types)
    (hlookup : loweredEnv.find? (Lean.mkRecName indType.name) =
      some (.recInfo oldInfo))
    (hsource : sourceRule ∈ oldInfo.rules) :
    let oldRecName := Lean.mkRecName indType.name
    let newRecName := recNameMap.getD oldRecName oldRecName
    let restored := result.restoreRecursor loweredEnv recNameMap allIndNames
      oldRecName newRecName oldInfo
    let sourceRecursorNames := allIndNames.map Lean.mkRecName ++ auxRecNames
    Lean4Lean.validateRestoredRecursorRules.checkPrimaryRuleShape restored
      sourceRecursorNames sourceRule
        (result.restoreRule loweredEnv recNameMap oldRecName newRecName
          sourceRule) = .ok () := by
  dsimp only
  exact validateRestoredRecursorRules.primaryShapeCheck_eq_ok_of_check
    (validateRestoredRecursorRules.primaryFullCheck_eq_ok_of_run hrun htype)
      hlookup hsource

/-- Select the canonical source-facing primary equation check from the final
loop of the exact primary validation trace. -/
theorem validateRestoredRecursorRules.primaryCanonicalEquationCheck_of_run
    (hrun : Lean4Lean.validateRestoredRecursorRules.run env loweredEnv lparams
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (htype : indType ∈ types)
    (hlookup : loweredEnv.find? (Lean.mkRecName indType.name) =
      some (.recInfo oldInfo))
    (hsource : sourceRule ∈ oldInfo.rules) :
    let oldRecName := Lean.mkRecName indType.name
    let newRecName := recNameMap.getD oldRecName oldRecName
    let restored := result.restoreRecursor loweredEnv recNameMap allIndNames
      oldRecName newRecName oldInfo
    let restoredRule := result.restoreRule loweredEnv recNameMap oldRecName
      newRecName sourceRule
    TypeChecker.M.run env (safety := safety) (lctx := {})
      (lparams := restored.levelParams) (fuel := fuel)
      (Lean4Lean.validateRestoredRecursorRules.checkPrimaryEquation
        lparams.length
        (result.nparams + result.types.length +
          (result.types.flatMap (·.ctors)).length)
        restored restoredRule) = .ok () := by
  dsimp only
  have hstep :=
    validateRestoredRecursorRules.primaryFullCheck_eq_ok_of_run hrun htype
  unfold Lean4Lean.validateRestoredRecursorRules.checkPrimary at hstep
  have hcommonOk : Lean4Lean.validateRestoredRecursorRules.check env loweredEnv
      lparams safety fuel result recNameMap allIndNames auxRecNames
        (Lean.mkRecName indType.name) = .ok () :=
    validateRestoredRecursorRules.primaryCheck_eq_ok_of_run hrun htype
  rw [hcommonOk] at hstep
  simp only [bind, Except.bind] at hstep
  rw [hlookup] at hstep
  simp only at hstep
  rcases except_bind_right_of_ok hstep with
    ⟨guardUnit, _hguard, hafterGuard⟩
  rcases guardUnit with ⟨⟩
  rcases except_bind_right_of_ok hafterGuard with
    ⟨shapeUnit, _hshape, hafterShape⟩
  rcases shapeUnit with ⟨⟩
  let validatePrimaryEquation := fun candidate : RecursorRule =>
      TypeChecker.M.run env (safety := safety) (lctx := {})
        (lparams :=
          (result.restoreRecursor loweredEnv recNameMap allIndNames
            (Lean.mkRecName indType.name)
            (recNameMap.getD (Lean.mkRecName indType.name)
              (Lean.mkRecName indType.name)) oldInfo).levelParams)
        (fuel := fuel)
        (Lean4Lean.validateRestoredRecursorRules.checkPrimaryEquation
          lparams.length
          (result.nparams + result.types.length +
            (result.types.flatMap (·.ctors)).length)
          (result.restoreRecursor loweredEnv recNameMap allIndNames
            (Lean.mkRecName indType.name)
            (recNameMap.getD (Lean.mkRecName indType.name)
              (Lean.mkRecName indType.name)) oldInfo)
          (result.restoreRule loweredEnv recNameMap
            (Lean.mkRecName indType.name)
            (recNameMap.getD (Lean.mkRecName indType.name)
              (Lean.mkRecName indType.name)) candidate))
  have hloop : oldInfo.rules.forM validatePrimaryEquation = .ok () := by
    cases hfinal : oldInfo.rules.forM validatePrimaryEquation with
    | error err =>
        rw [hfinal] at hafterShape
        simp [validatePrimaryEquation, bind, Except.bind] at hafterShape
    | ok unit =>
        cases unit
        simpa using hfinal
  have hone := listForM_eq_ok_of_mem validatePrimaryEquation hloop hsource
  unfold validatePrimaryEquation at hone
  exact hone

/-- Primary restored-rule specialization of
`equationCheck_eq_ok_of_check`, selected from the whole-block run. -/
theorem validateRestoredRecursorRules.primaryEquationCheck_of_run
    (hrun : Lean4Lean.validateRestoredRecursorRules.run env loweredEnv lparams
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (htype : indType ∈ types)
    (hlookup : loweredEnv.find? (Lean.mkRecName indType.name) =
      some (.recInfo oldInfo))
    (hrule : rule ∈
      (result.restoreRecursor loweredEnv recNameMap allIndNames
        (Lean.mkRecName indType.name)
        (recNameMap.getD (Lean.mkRecName indType.name)
          (Lean.mkRecName indType.name)) oldInfo).rules) :
    TypeChecker.M.run env (safety := safety) (lctx := {})
      (lparams :=
        (result.restoreRecursor loweredEnv recNameMap allIndNames
          (Lean.mkRecName indType.name)
          (recNameMap.getD (Lean.mkRecName indType.name)
            (Lean.mkRecName indType.name)) oldInfo).levelParams)
      (fuel := fuel)
      (Lean4Lean.validateRestoredRecursorRules.checkEquation
        (result.restoreRecursor loweredEnv recNameMap allIndNames
          (Lean.mkRecName indType.name)
          (recNameMap.getD (Lean.mkRecName indType.name)
            (Lean.mkRecName indType.name)) oldInfo) rule) = .ok () := by
  exact validateRestoredRecursorRules.equationCheck_eq_ok_of_check
    (validateRestoredRecursorRules.primaryCheck_eq_ok_of_run hrun htype)
      hlookup hrule

/-- Auxiliary restored-rule specialization of
`equationCheck_eq_ok_of_check`, selected from the whole-block run. -/
theorem validateRestoredRecursorRules.auxiliaryEquationCheck_of_run
    (hrun : Lean4Lean.validateRestoredRecursorRules.run env loweredEnv lparams
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (hrec : recName ∈ auxRecNames)
    (hlookup : loweredEnv.find? recName = some (.recInfo oldInfo))
    (hrule : rule ∈
      (result.restoreRecursor loweredEnv recNameMap allIndNames recName
        (recNameMap.getD recName recName) oldInfo).rules) :
    TypeChecker.M.run env (safety := safety) (lctx := {})
      (lparams :=
        (result.restoreRecursor loweredEnv recNameMap allIndNames recName
          (recNameMap.getD recName recName) oldInfo).levelParams)
      (fuel := fuel)
      (Lean4Lean.validateRestoredRecursorRules.checkEquation
        (result.restoreRecursor loweredEnv recNameMap allIndNames recName
          (recNameMap.getD recName recName) oldInfo) rule) = .ok () := by
  exact validateRestoredRecursorRules.equationCheck_eq_ok_of_check
    (validateRestoredRecursorRules.auxiliaryCheck_eq_ok_of_run hrun hrec)
      hlookup hrule

/-- Soundness of the closed equation-validation pass.  The literal LHS is
selected by the executable builder, both closed sides are interpreted by the
ordinary checker soundness theorem, and the successful final comparison
relates their inferred abstract types. -/
theorem validateRestoredRecursorRules.equationTyping_of_checkEquation
    (hvalid : CheckingEnv.Valid safety env venv)
    (hrun : TypeChecker.M.run env (safety := safety) (lctx := {})
      (lparams := recInfo.levelParams) (fuel := fuel)
      (Lean4Lean.validateRestoredRecursorRules.checkEquation recInfo rule) =
        .ok ()) :
    ∃ equationLevel lhs lhsInferred rhsInferred lhsTarget
        lhsTypeTarget rhsTarget rhsTypeTarget shared sharedInferred sharedTarget
        sharedTypeTarget,
      Lean4Lean.validateRestoredRecursorRules.buildEquationLhs env recInfo
        rule = .ok lhs ∧
      TrTyping venv recInfo.levelParams [] lhs lhsInferred lhsTarget
        lhsTypeTarget ∧
      TrTyping venv recInfo.levelParams [] rule.rhs rhsInferred rhsTarget
        rhsTypeTarget ∧
      venv.IsDefEqU recInfo.levelParams.length [] lhsTypeTarget
        rhsTypeTarget ∧
      Lean4Lean.validateRestoredRecursorRules.buildEquationSharedWitness
        recInfo rule lhs lhsInferred equationLevel = .ok shared ∧
      TrTyping venv recInfo.levelParams [] shared sharedInferred sharedTarget
        sharedTypeTarget := by
  let c := TypeChecker.VContext.mkCheckingValid hvalid recInfo.levelParams fuel
  have Hwf :
      (Lean4Lean.validateRestoredRecursorRules.checkEquation recInfo rule).WF
        c {} fun _ _ =>
          ∃ equationLevel lhs lhsInferred rhsInferred lhsTarget
              lhsTypeTarget rhsTarget rhsTypeTarget shared sharedInferred sharedTarget
              sharedTypeTarget,
            Lean4Lean.validateRestoredRecursorRules.buildEquationLhs env
              recInfo rule = .ok lhs ∧
            TrTyping venv recInfo.levelParams [] lhs lhsInferred lhsTarget
              lhsTypeTarget ∧
            TrTyping venv recInfo.levelParams [] rule.rhs rhsInferred rhsTarget
              rhsTypeTarget ∧
            venv.IsDefEqU recInfo.levelParams.length [] lhsTypeTarget
              rhsTypeTarget ∧
            Lean4Lean.validateRestoredRecursorRules.buildEquationSharedWitness
              recInfo rule lhs lhsInferred equationLevel = .ok shared ∧
            TrTyping venv recInfo.levelParams [] shared sharedInferred
              sharedTarget sharedTypeTarget := by
    unfold Lean4Lean.validateRestoredRecursorRules.checkEquation
    refine TypeChecker.getEnv.WF.bind fun found _ _ hfound => ?_
    rcases hfound with ⟨rfl, rfl⟩
    refine (TypeChecker.M.WF.liftExcept (Q := fun lhs =>
      Lean4Lean.validateRestoredRecursorRules.buildEquationLhs env recInfo
        rule = .ok lhs) ?_).bind fun lhs _ _ hbuild => ?_
    · exact fun _ h => h
    refine (TypeChecker.M.WF.liftExcept
      (checkNoMVarNoFVar.WF env recInfo.name lhs)).bind
        fun _ _ _ hlhsClosed => ?_
    refine (TypeChecker.M.WF.liftExcept
      (checkNoMVarNoFVar.WF env recInfo.name rule.rhs)).bind
        fun _ _ _ hrhsClosed => ?_
    have hlhsFVars : lhs.FVarsIn (· ∈ c.vlctx.fvars) :=
      hlhsClosed.mono fun _ h => False.elim h
    have hrhsFVars : rule.rhs.FVarsIn (· ∈ c.vlctx.fvars) :=
      hrhsClosed.mono fun _ h => False.elim h
    refine (TypeChecker.checkType.WF hlhsFVars).bind
      fun lhsInferred _ _ Hlhs => ?_
    refine (TypeChecker.checkType.WF hrhsFVars).bind
      fun rhsInferred _ _ Hrhs => ?_
    rcases Hlhs with ⟨lhsTarget, lhsTypeTarget, Hlhs⟩
    rcases Hrhs with ⟨rhsTarget, rhsTypeTarget, Hrhs⟩
    refine (TypeChecker.isDefEq.WF Hlhs.2.2.1 Hrhs.2.2.1).bind
      fun equal _ _ Hequal => ?_
    cases equal with
    | false => exact .throw
    | true =>
        refine (TypeChecker.M.WF.liftExcept (Q := fun bodyTypeWitness =>
          Lean4Lean.validateRestoredRecursorRules.buildEquationBodyTypeWitness
            recInfo rule lhsInferred = .ok bodyTypeWitness) ?_).bind
              fun bodyTypeWitness _ _ hbodyTypeWitness => ?_
        · exact fun _ h => h
        refine (TypeChecker.M.WF.liftExcept
          (checkNoMVarNoFVar.WF env recInfo.name bodyTypeWitness)).bind
            fun _ _ _ hbodyTypeWitnessClosed => ?_
        have hbodyTypeWitnessFVars :
            bodyTypeWitness.FVarsIn (· ∈ c.vlctx.fvars) :=
          hbodyTypeWitnessClosed.mono fun _ h => False.elim h
        refine (TypeChecker.checkType.WF hbodyTypeWitnessFVars).bind
          fun bodyTypeWitnessType _ _ _HbodyTypeWitness => ?_
        refine (TypeChecker.M.WF.liftExcept (Q := fun equationLevel =>
          Lean4Lean.validateRestoredRecursorRules.equationBodySortLevel
            recInfo rule bodyTypeWitnessType = .ok equationLevel) ?_).bind
              fun equationLevel _ _ _hequationLevel => ?_
        · exact fun _ h => h
        refine (TypeChecker.M.WF.liftExcept (Q := fun shared =>
          Lean4Lean.validateRestoredRecursorRules.buildEquationSharedWitness
            recInfo rule lhs lhsInferred equationLevel = .ok shared) ?_).bind
              fun shared _ _ hshared => ?_
        · exact fun _ h => h
        refine (TypeChecker.M.WF.liftExcept
          (checkNoMVarNoFVar.WF env recInfo.name shared)).bind
            fun _ _ _ hsharedClosed => ?_
        have hsharedFVars : shared.FVarsIn (· ∈ c.vlctx.fvars) :=
          hsharedClosed.mono fun _ h => False.elim h
        refine (TypeChecker.checkType.WF hsharedFVars).bind
          fun sharedInferred _ _ Hshared => ?_
        rcases Hshared with ⟨sharedTarget, sharedTypeTarget, Hshared⟩
        exact .pure ⟨equationLevel, lhs, lhsInferred, rhsInferred, lhsTarget,
          lhsTypeTarget, rhsTarget, rhsTypeTarget, shared, sharedInferred,
          sharedTarget, sharedTypeTarget, hbuild, Hlhs, Hrhs, Hequal rfl,
          hshared, Hshared⟩
  have Hrun := TypeChecker.M.WF.runCheckingValid
    (wf := hvalid) (lparams := recInfo.levelParams) (fuel := fuel) Hwf
  exact Hrun () hrun

/-- Soundness of the canonical source-facing primary equation check. -/
theorem validateRestoredRecursorRules.equationTyping_of_checkPrimaryEquation
    (hvalid : CheckingEnv.Valid safety env venv)
    (hrun : TypeChecker.M.run env (safety := safety) (lctx := {})
      (lparams := recInfo.levelParams) (fuel := fuel)
      (Lean4Lean.validateRestoredRecursorRules.checkPrimaryEquation
        expectedCtorUvars expectedPrefix recInfo rule) =
        .ok ()) :
    ∃ equationLevel lhs lhsInferred rhsInferred lhsTarget
        lhsTypeTarget rhsTarget rhsTypeTarget shared sharedInferred sharedTarget
        sharedTypeTarget,
      Lean4Lean.validateRestoredRecursorRules.buildPrimaryEquationLhs env
        expectedCtorUvars expectedPrefix recInfo rule = .ok lhs ∧
      TrTyping venv recInfo.levelParams [] lhs lhsInferred lhsTarget
        lhsTypeTarget ∧
      TrTyping venv recInfo.levelParams [] rule.rhs rhsInferred rhsTarget
        rhsTypeTarget ∧
      venv.IsDefEqU recInfo.levelParams.length [] lhsTypeTarget
        rhsTypeTarget ∧
      Lean4Lean.validateRestoredRecursorRules.buildEquationSharedWitness
        recInfo rule lhs lhsInferred equationLevel = .ok shared ∧
      TrTyping venv recInfo.levelParams [] shared sharedInferred sharedTarget
        sharedTypeTarget := by
  let c := TypeChecker.VContext.mkCheckingValid hvalid recInfo.levelParams fuel
  have Hwf :
      (Lean4Lean.validateRestoredRecursorRules.checkPrimaryEquation
        expectedCtorUvars expectedPrefix recInfo rule).WF
        c {} fun _ _ =>
          ∃ equationLevel lhs lhsInferred rhsInferred lhsTarget
              lhsTypeTarget rhsTarget rhsTypeTarget shared sharedInferred sharedTarget
              sharedTypeTarget,
            Lean4Lean.validateRestoredRecursorRules.buildPrimaryEquationLhs env
              expectedCtorUvars expectedPrefix recInfo rule = .ok lhs ∧
            TrTyping venv recInfo.levelParams [] lhs lhsInferred lhsTarget
              lhsTypeTarget ∧
            TrTyping venv recInfo.levelParams [] rule.rhs rhsInferred rhsTarget
              rhsTypeTarget ∧
            venv.IsDefEqU recInfo.levelParams.length [] lhsTypeTarget
              rhsTypeTarget ∧
            Lean4Lean.validateRestoredRecursorRules.buildEquationSharedWitness
              recInfo rule lhs lhsInferred equationLevel = .ok shared ∧
            TrTyping venv recInfo.levelParams [] shared sharedInferred
              sharedTarget sharedTypeTarget := by
    unfold Lean4Lean.validateRestoredRecursorRules.checkPrimaryEquation
    refine TypeChecker.getEnv.WF.bind fun found _ _ hfound => ?_
    rcases hfound with ⟨rfl, rfl⟩
    refine (TypeChecker.M.WF.liftExcept (Q := fun lhs =>
      Lean4Lean.validateRestoredRecursorRules.buildPrimaryEquationLhs env
        expectedCtorUvars expectedPrefix recInfo rule = .ok lhs) ?_).bind
          fun lhs _ _ hbuild => ?_
    · exact fun _ h => h
    refine (TypeChecker.M.WF.liftExcept
      (checkNoMVarNoFVar.WF env recInfo.name lhs)).bind
        fun _ _ _ hlhsClosed => ?_
    refine (TypeChecker.M.WF.liftExcept
      (checkNoMVarNoFVar.WF env recInfo.name rule.rhs)).bind
        fun _ _ _ hrhsClosed => ?_
    have hlhsFVars : lhs.FVarsIn (· ∈ c.vlctx.fvars) :=
      hlhsClosed.mono fun _ h => False.elim h
    have hrhsFVars : rule.rhs.FVarsIn (· ∈ c.vlctx.fvars) :=
      hrhsClosed.mono fun _ h => False.elim h
    refine (TypeChecker.checkType.WF hlhsFVars).bind
      fun lhsInferred _ _ Hlhs => ?_
    refine (TypeChecker.checkType.WF hrhsFVars).bind
      fun rhsInferred _ _ Hrhs => ?_
    rcases Hlhs with ⟨lhsTarget, lhsTypeTarget, Hlhs⟩
    rcases Hrhs with ⟨rhsTarget, rhsTypeTarget, Hrhs⟩
    refine (TypeChecker.isDefEq.WF Hlhs.2.2.1 Hrhs.2.2.1).bind
      fun equal _ _ Hequal => ?_
    cases equal with
    | false => exact .throw
    | true =>
        refine (TypeChecker.M.WF.liftExcept (Q := fun bodyTypeWitness =>
          Lean4Lean.validateRestoredRecursorRules.buildEquationBodyTypeWitness
            recInfo rule lhsInferred = .ok bodyTypeWitness) ?_).bind
              fun bodyTypeWitness _ _ hbodyTypeWitness => ?_
        · exact fun _ h => h
        refine (TypeChecker.M.WF.liftExcept
          (checkNoMVarNoFVar.WF env recInfo.name bodyTypeWitness)).bind
            fun _ _ _ hbodyTypeWitnessClosed => ?_
        have hbodyTypeWitnessFVars :
            bodyTypeWitness.FVarsIn (· ∈ c.vlctx.fvars) :=
          hbodyTypeWitnessClosed.mono fun _ h => False.elim h
        refine (TypeChecker.checkType.WF hbodyTypeWitnessFVars).bind
          fun bodyTypeWitnessType _ _ _HbodyTypeWitness => ?_
        refine (TypeChecker.M.WF.liftExcept (Q := fun equationLevel =>
          Lean4Lean.validateRestoredRecursorRules.equationBodySortLevel
            recInfo rule bodyTypeWitnessType = .ok equationLevel) ?_).bind
              fun equationLevel _ _ _hequationLevel => ?_
        · exact fun _ h => h
        refine (TypeChecker.M.WF.liftExcept (Q := fun shared =>
          Lean4Lean.validateRestoredRecursorRules.buildEquationSharedWitness
            recInfo rule lhs lhsInferred equationLevel = .ok shared) ?_).bind
              fun shared _ _ hshared => ?_
        · exact fun _ h => h
        refine (TypeChecker.M.WF.liftExcept
          (checkNoMVarNoFVar.WF env recInfo.name shared)).bind
            fun _ _ _ hsharedClosed => ?_
        have hsharedFVars : shared.FVarsIn (· ∈ c.vlctx.fvars) :=
          hsharedClosed.mono fun _ h => False.elim h
        refine (TypeChecker.checkType.WF hsharedFVars).bind
          fun sharedInferred _ _ Hshared => ?_
        rcases Hshared with ⟨sharedTarget, sharedTypeTarget, Hshared⟩
        exact .pure ⟨equationLevel, lhs, lhsInferred, rhsInferred, lhsTarget,
          lhsTypeTarget, rhsTarget, rhsTypeTarget, shared, sharedInferred,
          sharedTarget, sharedTypeTarget, hbuild, Hlhs, Hrhs, Hequal rfl,
          hshared, Hshared⟩
  have Hrun := TypeChecker.M.WF.runCheckingValid
    (wf := hvalid) (lparams := recInfo.levelParams) (fuel := fuel) Hwf
  exact Hrun () hrun

/-- The local-let witness checked by `checkEquation` forces both equation
bodies to be translated in one literal target binder context and checked
against one literal target type.  This is the projection-safe replacement
for attempting to identify two independently chosen `TrExprS` derivations.
-/
theorem validateRestoredRecursorRules.sharedAbstractRuleWF_of_checkEquation
    (hvalid : CheckingEnv.Valid safety env venv)
    (hrun : TypeChecker.M.run env (safety := safety) (lctx := {})
      (lparams := recInfo.levelParams) (fuel := fuel)
      (Lean4Lean.validateRestoredRecursorRules.checkEquation recInfo rule) =
        .ok ()) :
    let arity := recInfo.numParams + recInfo.numMotives +
      recInfo.numMinors + rule.nfields
    ∃ (lhs lhsInferred lhsBodySource rhsBodySource : Expr)
        (domains : List VExpr) (lhsBody rhsBody typeBody : VExpr),
      Lean4Lean.validateRestoredRecursorRules.buildEquationLhs env recInfo
        rule = .ok lhs ∧
      Expr.LambdaTelescope lhs arity lhsBodySource ∧
      Expr.LambdaTelescope rule.rhs arity rhsBodySource ∧
      domains.length = arity ∧
      TrExprS venv recInfo.levelParams [] lhs
        (VExpr.wrapLams domains lhsBody) ∧
      TrExprS venv recInfo.levelParams [] rule.rhs
        (VExpr.wrapLams domains rhsBody) ∧
      Nonempty (({
        uvars := recInfo.levelParams.length
        lhs := VExpr.wrapLams domains lhsBody
        rhs := VExpr.wrapLams domains rhsBody
        type := VExpr.wrapForalls domains typeBody } : VDefEq).WF venv) := by
  dsimp only
  rcases validateRestoredRecursorRules.equationTyping_of_checkEquation
      hvalid hrun with
    ⟨equationLevel, lhs, lhsInferred, _rhsInferred, _lhsTarget,
      _lhsTypeTarget, _rhsTarget, _rhsTypeTarget, shared, _sharedInferred,
      sharedTarget, _sharedTypeTarget, hbuild, _Hlhs, _Hrhs, _Htypes,
      hshared, Hshared⟩
  rcases validateRestoredRecursorRules.buildEquationSharedWitness_success
      hshared with
    ⟨lhsBodySource, rhsBodySource, bodyTypeSource, HlhsTelescope,
      HrhsTelescope, _HtypeTelescope, HsharedTelescope,
      HrhsSharedPrefix⟩
  rcases TrExprS.lambdaTelescope_shape_with_context HsharedTelescope
      Hshared.2.1 with
    ⟨domains, sharedResidualTarget, hdomains, hsharedTarget,
      HsharedResidual⟩
  cases HsharedResidual with
  | letE HbodyTypeTyping _HsortTranslation HbodyTypeTranslation HlhsLet =>
    rename_i bodyTypeTarget bodyTypeSortTarget
    cases HlhsLet with
    | letE HlhsTyping HlhsTypeBVar HshiftLhsTranslation HrhsLet =>
      rename_i lhsBodyTarget lhsTypeTarget
      cases HrhsLet with
      | letE HrhsTyping HrhsTypeBVar HshiftRhsTranslation HfinalBVar =>
        rename_i rhsBodyTarget rhsTypeTarget
        have hlhsType := TrExprS.vletBVarZero_eq HlhsTypeBVar
        have hrhsType := TrExprS.vletBVarOne_eq HrhsTypeBVar
        have _hfinal := TrExprS.vletBVarZero_eq HfinalBVar
        have HlhsBody := HshiftLhsTranslation.inst_let
          hvalid.tr.wf.ordered HbodyTypeTranslation
        rw [validateRestoredRecursorRules.instantiate_shiftEquationBody] at HlhsBody
        have HrhsOnce := HshiftRhsTranslation.inst_let
          hvalid.tr.wf.ordered HshiftLhsTranslation
        rw [validateRestoredRecursorRules.instantiate_shiftEquationBody_succ
          (amount := 1)] at HrhsOnce
        have HrhsBody := HrhsOnce.inst_let hvalid.tr.wf.ordered
          HbodyTypeTranslation
        rw [validateRestoredRecursorRules.instantiate_shiftEquationBody] at HrhsBody
        have HsharedExact : TrExprS venv recInfo.levelParams [] shared
            (VExpr.wrapLams domains sharedResidualTarget) := by
          rw [← hsharedTarget]
          exact Hshared.2.1
        have HrhsFull : TrExprS venv recInfo.levelParams [] rule.rhs
            (VExpr.wrapLams domains rhsBodyTarget) :=
          HrhsSharedPrefix.symm.replaceTranslatedResidual HsharedTelescope
            HrhsTelescope hdomains HsharedExact HrhsBody
        rcases validateRestoredRecursorRules.buildEquationLhs_success hbuild
            with ⟨plan, _hplan, hlhsReplace⟩
        rcases validateRestoredRecursorRules.replaceEquationBody_sound
            hlhsReplace with
          ⟨_rhsResidual, _HrhsTelescope', HlhsTelescope', HrhsLhsPrefix⟩
        have hlhsResidual : lhsBodySource = plan.body recInfo rule :=
          HlhsTelescope.result_eq HlhsTelescope'
        subst lhsBodySource
        have HlhsFull : TrExprS venv recInfo.levelParams [] lhs
            (VExpr.wrapLams domains lhsBodyTarget) :=
          HrhsLhsPrefix.replaceTranslatedResidual HrhsTelescope
            HlhsTelescope' hdomains HrhsFull HlhsBody
        have HsharedContextWF := TrExprS.lambdaTelescope_contextWF
          HsharedTelescope hdomains HsharedExact
          (show VLCtx.WF venv recInfo.levelParams.length [] from trivial)
        have hctx : OnCtx domains.reverse
            (venv.IsType recInfo.levelParams.length) := by
          simpa [abstractForallContext_toCtx, VLCtx.toCtx] using
            HsharedContextWF.toCtx
        have HlhsTyped : venv.HasType recInfo.levelParams.length
            domains.reverse lhsBodyTarget bodyTypeTarget := by
          rw [hlhsType] at HlhsTyping
          simpa [abstractForallContext_toCtx, VLCtx.toCtx] using HlhsTyping
        have HrhsTyped : venv.HasType recInfo.levelParams.length
            domains.reverse rhsBodyTarget bodyTypeTarget := by
          rw [hrhsType] at HrhsTyping
          simpa [abstractForallContext_toCtx, VLCtx.toCtx] using HrhsTyping
        exact ⟨lhs, lhsInferred, plan.body recInfo rule, rhsBodySource, domains,
          lhsBodyTarget, rhsBodyTarget, bodyTypeTarget, hbuild, HlhsTelescope',
          HrhsTelescope, hdomains, HlhsFull, HrhsFull,
          ⟨VDefEq.wf_of_wrappedBodies hctx HlhsTyped HrhsTyped⟩⟩

/-- Canonical-primary specialization of the shared local-let certificate.
The returned LHS residual is the source-facing canonicalized equation plan,
not the lowering-specific major-domain application. -/
theorem validateRestoredRecursorRules.sharedAbstractRuleWF_of_checkPrimaryEquation
    (hvalid : CheckingEnv.Valid safety env venv)
    (hrun : TypeChecker.M.run env (safety := safety) (lctx := {})
      (lparams := recInfo.levelParams) (fuel := fuel)
      (Lean4Lean.validateRestoredRecursorRules.checkPrimaryEquation
        expectedCtorUvars expectedPrefix recInfo rule) =
        .ok ()) :
    let arity := recInfo.numParams + recInfo.numMotives +
      recInfo.numMinors + rule.nfields
    ∃ (lhs lhsInferred lhsBodySource rhsBodySource : Expr)
        (plan canonicalPlan :
          Lean4Lean.validateRestoredRecursorRules.EquationLhsPlan)
        (domains : List VExpr) (lhsBody rhsBody typeBody : VExpr),
      Lean4Lean.validateRestoredRecursorRules.buildPrimaryEquationLhs env
        expectedCtorUvars expectedPrefix recInfo rule = .ok lhs ∧
      Lean4Lean.validateRestoredRecursorRules.buildEquationLhsPlan env recInfo
        rule = .ok plan ∧
      plan.indices.size = recInfo.numIndices ∧
      plan.ctorLevels.length = expectedCtorUvars ∧
      recInfo.numParams + recInfo.numMotives + recInfo.numMinors =
        expectedPrefix ∧
      (let binderCount := recInfo.numParams + recInfo.numMotives +
          recInfo.numMinors + rule.nfields
        let binders := (List.range binderCount).toArray.map fun i =>
          Expr.bvar (binderCount - 1 - i)
        let params := binders.extract 0 recInfo.numParams
        canonicalPlan = { plan with ctorParams := params }) ∧
      Expr.LambdaTelescope lhs arity lhsBodySource ∧
      Expr.LambdaTelescope rule.rhs arity rhsBodySource ∧
      domains.length = arity ∧
      TrExprS venv recInfo.levelParams
        (abstractForallContext domains [])
        (canonicalPlan.body recInfo rule) lhsBody ∧
      TrExprS venv recInfo.levelParams
        (abstractForallContext domains []) rhsBodySource rhsBody ∧
      TrExprS venv recInfo.levelParams [] lhs
        (VExpr.wrapLams domains lhsBody) ∧
      TrExprS venv recInfo.levelParams [] rule.rhs
        (VExpr.wrapLams domains rhsBody) ∧
      Nonempty (({
        uvars := recInfo.levelParams.length
        lhs := VExpr.wrapLams domains lhsBody
        rhs := VExpr.wrapLams domains rhsBody
        type := VExpr.wrapForalls domains typeBody } : VDefEq).WF venv) := by
  dsimp only
  rcases validateRestoredRecursorRules.equationTyping_of_checkPrimaryEquation
      hvalid hrun with
    ⟨equationLevel, lhs, lhsInferred, _rhsInferred, _lhsTarget,
      _lhsTypeTarget, _rhsTarget, _rhsTypeTarget, shared, _sharedInferred,
      sharedTarget, _sharedTypeTarget, hbuild, _Hlhs, _Hrhs, _Htypes,
      hshared, Hshared⟩
  rcases validateRestoredRecursorRules.buildEquationSharedWitness_success
      hshared with
    ⟨lhsBodySource, rhsBodySource, bodyTypeSource, HlhsTelescope,
      HrhsTelescope, _HtypeTelescope, HsharedTelescope,
      HrhsSharedPrefix⟩
  rcases TrExprS.lambdaTelescope_shape_with_context HsharedTelescope
      Hshared.2.1 with
    ⟨domains, sharedResidualTarget, hdomains, hsharedTarget,
      HsharedResidual⟩
  cases HsharedResidual with
  | letE HbodyTypeTyping _HsortTranslation HbodyTypeTranslation HlhsLet =>
    rename_i bodyTypeTarget bodyTypeSortTarget
    cases HlhsLet with
    | letE HlhsTyping HlhsTypeBVar HshiftLhsTranslation HrhsLet =>
      rename_i lhsBodyTarget lhsTypeTarget
      cases HrhsLet with
      | letE HrhsTyping HrhsTypeBVar HshiftRhsTranslation HfinalBVar =>
        rename_i rhsBodyTarget rhsTypeTarget
        have hlhsType := TrExprS.vletBVarZero_eq HlhsTypeBVar
        have hrhsType := TrExprS.vletBVarOne_eq HrhsTypeBVar
        have _hfinal := TrExprS.vletBVarZero_eq HfinalBVar
        have HlhsBody := HshiftLhsTranslation.inst_let
          hvalid.tr.wf.ordered HbodyTypeTranslation
        rw [validateRestoredRecursorRules.instantiate_shiftEquationBody] at HlhsBody
        have HrhsOnce := HshiftRhsTranslation.inst_let
          hvalid.tr.wf.ordered HshiftLhsTranslation
        rw [validateRestoredRecursorRules.instantiate_shiftEquationBody_succ
          (amount := 1)] at HrhsOnce
        have HrhsBody := HrhsOnce.inst_let hvalid.tr.wf.ordered
          HbodyTypeTranslation
        rw [validateRestoredRecursorRules.instantiate_shiftEquationBody] at HrhsBody
        have HsharedExact : TrExprS venv recInfo.levelParams [] shared
            (VExpr.wrapLams domains sharedResidualTarget) := by
          rw [← hsharedTarget]
          exact Hshared.2.1
        have HrhsFull : TrExprS venv recInfo.levelParams [] rule.rhs
            (VExpr.wrapLams domains rhsBodyTarget) :=
          HrhsSharedPrefix.symm.replaceTranslatedResidual HsharedTelescope
            HrhsTelescope hdomains HsharedExact HrhsBody
        rcases validateRestoredRecursorRules.buildPrimaryEquationLhs_success
            hbuild with
          ⟨plan, canonicalPlan, _hplan, _hindices, _huvars, _hprefix,
            _hcanonical, hlhsReplace⟩
        rcases validateRestoredRecursorRules.replaceEquationBody_sound
            hlhsReplace with
          ⟨_rhsResidual, _HrhsTelescope', HlhsTelescope', HrhsLhsPrefix⟩
        have hlhsResidual : lhsBodySource = canonicalPlan.body recInfo rule :=
          HlhsTelescope.result_eq HlhsTelescope'
        subst lhsBodySource
        have HlhsFull : TrExprS venv recInfo.levelParams [] lhs
            (VExpr.wrapLams domains lhsBodyTarget) :=
          HrhsLhsPrefix.replaceTranslatedResidual HrhsTelescope
            HlhsTelescope' hdomains HrhsFull HlhsBody
        have HsharedContextWF := TrExprS.lambdaTelescope_contextWF
          HsharedTelescope hdomains HsharedExact
          (show VLCtx.WF venv recInfo.levelParams.length [] from trivial)
        have hctx : OnCtx domains.reverse
            (venv.IsType recInfo.levelParams.length) := by
          simpa [abstractForallContext_toCtx, VLCtx.toCtx] using
            HsharedContextWF.toCtx
        have HlhsTyped : venv.HasType recInfo.levelParams.length
            domains.reverse lhsBodyTarget bodyTypeTarget := by
          rw [hlhsType] at HlhsTyping
          simpa [abstractForallContext_toCtx, VLCtx.toCtx] using HlhsTyping
        have HrhsTyped : venv.HasType recInfo.levelParams.length
            domains.reverse rhsBodyTarget bodyTypeTarget := by
          rw [hrhsType] at HrhsTyping
          simpa [abstractForallContext_toCtx, VLCtx.toCtx] using HrhsTyping
        exact ⟨lhs, lhsInferred, canonicalPlan.body recInfo rule,
          rhsBodySource, plan, canonicalPlan, domains, lhsBodyTarget,
          rhsBodyTarget, bodyTypeTarget, hbuild, _hplan, _hindices, _huvars,
          _hprefix, _hcanonical, HlhsTelescope', HrhsTelescope, hdomains,
          HlhsBody, HrhsBody,
          HlhsFull, HrhsFull,
          ⟨VDefEq.wf_of_wrappedBodies hctx HlhsTyped HrhsTyped⟩⟩

/-- Package the preceding checker result as an actual well-formed abstract
equation.  All three expressions are the translations selected by the
checker run; the RHS is converted to the LHS's inferred type using the
successful comparison. -/
theorem validateRestoredRecursorRules.abstractRuleWF_of_checkEquation
    (hvalid : CheckingEnv.Valid safety env venv)
    (hrun : TypeChecker.M.run env (safety := safety) (lctx := {})
      (lparams := recInfo.levelParams) (fuel := fuel)
      (Lean4Lean.validateRestoredRecursorRules.checkEquation recInfo rule) =
        .ok ()) :
    ∃ (lhs lhsInferred rhsInferred : Expr)
        (lhsTarget rhsTarget targetType : VExpr),
      Lean4Lean.validateRestoredRecursorRules.buildEquationLhs env recInfo
        rule = .ok lhs ∧
      TrExprS venv recInfo.levelParams [] lhs lhsTarget ∧
      TrExprS venv recInfo.levelParams [] rule.rhs rhsTarget ∧
      TrExprS venv recInfo.levelParams [] lhsInferred targetType ∧
      Nonempty (({
        uvars := recInfo.levelParams.length
        lhs := lhsTarget
        rhs := rhsTarget
        type := targetType } : VDefEq).WF venv) := by
  rcases validateRestoredRecursorRules.equationTyping_of_checkEquation
      hvalid hrun with
    ⟨_equationLevel, lhs, lhsInferred, rhsInferred, lhsTarget, lhsTypeTarget,
      rhsTarget, rhsTypeTarget, _shared, _sharedInferred, _sharedTarget,
      _sharedTypeTarget, hbuild, Hlhs, Hrhs, Htypes, _hshared,
      _Hshared⟩
  have HrhsAtLhsType : venv.HasType recInfo.levelParams.length [] rhsTarget
      lhsTypeTarget :=
    Hrhs.2.2.2.defeqU_r hvalid.tr.wf (by trivial) Htypes.symm
  exact ⟨lhs, lhsInferred, rhsInferred, lhsTarget, rhsTarget,
    lhsTypeTarget, hbuild, Hlhs.2.1, Hrhs.2.1, Hlhs.2.2.1,
    ⟨Hlhs.2.2.2, HrhsAtLhsType⟩⟩

/-- Primary restored-rule specialization of the exact equation-WF result.
The abstract equation is selected by the checker run itself: neither its
left-hand side, right-hand side, nor common type is supplied by a caller. -/
theorem validateRestoredRecursorRules.primaryAbstractRuleWF_of_run
    (hvalid : CheckingEnv.Valid safety env venv)
    (hrun : Lean4Lean.validateRestoredRecursorRules.run env loweredEnv lparams
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (htype : indType ∈ types)
    (hlookup : loweredEnv.find? (Lean.mkRecName indType.name) =
      some (.recInfo oldInfo))
    (hrule : rule ∈
      (result.restoreRecursor loweredEnv recNameMap allIndNames
        (Lean.mkRecName indType.name)
        (recNameMap.getD (Lean.mkRecName indType.name)
          (Lean.mkRecName indType.name)) oldInfo).rules) :
    ∃ (lhs lhsInferred rhsInferred : Expr)
        (lhsTarget rhsTarget targetType : VExpr),
      Lean4Lean.validateRestoredRecursorRules.buildEquationLhs env
        (result.restoreRecursor loweredEnv recNameMap allIndNames
          (Lean.mkRecName indType.name)
          (recNameMap.getD (Lean.mkRecName indType.name)
            (Lean.mkRecName indType.name)) oldInfo) rule = .ok lhs ∧
      TrExprS venv
        (result.restoreRecursor loweredEnv recNameMap allIndNames
          (Lean.mkRecName indType.name)
          (recNameMap.getD (Lean.mkRecName indType.name)
            (Lean.mkRecName indType.name)) oldInfo).levelParams [] lhs
        lhsTarget ∧
      TrExprS venv
        (result.restoreRecursor loweredEnv recNameMap allIndNames
          (Lean.mkRecName indType.name)
          (recNameMap.getD (Lean.mkRecName indType.name)
            (Lean.mkRecName indType.name)) oldInfo).levelParams [] rule.rhs
        rhsTarget ∧
      TrExprS venv
        (result.restoreRecursor loweredEnv recNameMap allIndNames
          (Lean.mkRecName indType.name)
          (recNameMap.getD (Lean.mkRecName indType.name)
            (Lean.mkRecName indType.name)) oldInfo).levelParams [] lhsInferred
        targetType ∧
      Nonempty (({
        uvars :=
          (result.restoreRecursor loweredEnv recNameMap allIndNames
            (Lean.mkRecName indType.name)
            (recNameMap.getD (Lean.mkRecName indType.name)
              (Lean.mkRecName indType.name)) oldInfo).levelParams.length
        lhs := lhsTarget
        rhs := rhsTarget
        type := targetType } : VDefEq).WF venv) := by
  exact validateRestoredRecursorRules.abstractRuleWF_of_checkEquation hvalid
    (validateRestoredRecursorRules.primaryEquationCheck_of_run hrun htype
      hlookup hrule)

/-- Auxiliary restored-rule specialization of the exact equation-WF result.
As in the primary case, the successful executable run fixes the entire
abstract equation and proves its well-formedness internally. -/
theorem validateRestoredRecursorRules.auxiliaryAbstractRuleWF_of_run
    (hvalid : CheckingEnv.Valid safety env venv)
    (hrun : Lean4Lean.validateRestoredRecursorRules.run env loweredEnv lparams
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (hrec : recName ∈ auxRecNames)
    (hlookup : loweredEnv.find? recName = some (.recInfo oldInfo))
    (hrule : rule ∈
      (result.restoreRecursor loweredEnv recNameMap allIndNames recName
        (recNameMap.getD recName recName) oldInfo).rules) :
    ∃ (lhs lhsInferred rhsInferred : Expr)
        (lhsTarget rhsTarget targetType : VExpr),
      Lean4Lean.validateRestoredRecursorRules.buildEquationLhs env
        (result.restoreRecursor loweredEnv recNameMap allIndNames recName
          (recNameMap.getD recName recName) oldInfo) rule = .ok lhs ∧
      TrExprS venv
        (result.restoreRecursor loweredEnv recNameMap allIndNames recName
          (recNameMap.getD recName recName) oldInfo).levelParams [] lhs
        lhsTarget ∧
      TrExprS venv
        (result.restoreRecursor loweredEnv recNameMap allIndNames recName
          (recNameMap.getD recName recName) oldInfo).levelParams [] rule.rhs
        rhsTarget ∧
      TrExprS venv
        (result.restoreRecursor loweredEnv recNameMap allIndNames recName
          (recNameMap.getD recName recName) oldInfo).levelParams [] lhsInferred
        targetType ∧
      Nonempty (({
        uvars :=
          (result.restoreRecursor loweredEnv recNameMap allIndNames recName
            (recNameMap.getD recName recName) oldInfo).levelParams.length
        lhs := lhsTarget
        rhs := rhsTarget
        type := targetType } : VDefEq).WF venv) := by
  exact validateRestoredRecursorRules.abstractRuleWF_of_checkEquation hvalid
    (validateRestoredRecursorRules.auxiliaryEquationCheck_of_run hrun hrec
      hlookup hrule)

/-- A successful exact restored-rule check supplies translated typing for
the literal RHS selected from the restored recursor metadata.  This is the
target-side semantic fact retained by the executable post-installation pass;
it is not a caller-provided rule certificate. -/
theorem validateRestoredRecursorRules.translation_of_check
    (hvalid : CheckingEnv.Valid safety env venv)
    (hstep : Lean4Lean.validateRestoredRecursorRules.check env loweredEnv
      lparams safety fuel result recNameMap allIndNames auxRecNames recName =
        .ok ())
    (hlookup : loweredEnv.find? recName = some (.recInfo oldInfo))
    (hrule : rule ∈
      (result.restoreRecursor loweredEnv recNameMap allIndNames recName
        (recNameMap.getD recName recName) oldInfo).rules) :
    ∃ inferred target targetType,
      TrTyping venv
        (result.restoreRecursor loweredEnv recNameMap allIndNames recName
          (recNameMap.getD recName recName) oldInfo).levelParams []
        rule.rhs inferred target targetType := by
  let restored := result.restoreRecursor loweredEnv recNameMap allIndNames
    recName (recNameMap.getD recName recName) oldInfo
  let restoredRecursorNames :=
    allIndNames.map (fun name =>
      let oldName := Lean.mkRecName name
      recNameMap.getD oldName oldName) ++
    auxRecNames.map fun oldName => recNameMap.getD oldName oldName
  unfold Lean4Lean.validateRestoredRecursorRules.check at hstep
  rw [hlookup] at hstep
  simp only at hstep
  have hvalidated := except_bind_unit_left_of_ok hstep
  have hruleFull : (do
      env.checkNoMVarNoFVar restored.name rule.rhs
      _ ← TypeChecker.M.run env (safety := safety) (lctx := {})
        (lparams := restored.levelParams) (fuel := fuel) do
          TypeChecker.checkType rule.rhs
      _ ← TypeChecker.M.run env (safety := safety) (lctx := {})
        (lparams := restored.levelParams) (fuel := fuel) do
          Lean4Lean.validateRestoredRecursorRules.checkEquation restored rule
      Lean4Lean.validateRestoredRecursorRules.checkGuarded
        restoredRecursorNames rule.rhs) =
        .ok () := by
    apply listForM_eq_ok_of_mem
      (fun candidate : RecursorRule => do
        env.checkNoMVarNoFVar restored.name candidate.rhs
        _ ← TypeChecker.M.run env (safety := safety) (lctx := {})
          (lparams := restored.levelParams) (fuel := fuel) do
            TypeChecker.checkType candidate.rhs
        _ ← TypeChecker.M.run env (safety := safety) (lctx := {})
          (lparams := restored.levelParams) (fuel := fuel) do
            Lean4Lean.validateRestoredRecursorRules.checkEquation restored
              candidate
        Lean4Lean.validateRestoredRecursorRules.checkGuarded
          restoredRecursorNames candidate.rhs)
    · simpa only [restored] using hvalidated
    · simpa only [restored] using hrule
  have hruleStep : (do
      env.checkNoMVarNoFVar restored.name rule.rhs
      _ ← TypeChecker.M.run env (safety := safety) (lctx := {})
        (lparams := restored.levelParams) (fuel := fuel) do
          TypeChecker.checkType rule.rhs) = .ok () := by
    cases hclosed : env.checkNoMVarNoFVar restored.name rule.rhs with
    | error err =>
        rw [hclosed] at hruleFull
        cases hruleFull
    | ok unit =>
        rcases unit with ⟨⟩
        rw [hclosed] at hruleFull
        cases htype : TypeChecker.M.run env (safety := safety) (lctx := {})
            (lparams := restored.levelParams) (fuel := fuel)
            (TypeChecker.checkType rule.rhs) with
        | error err =>
            rw [htype] at hruleFull
            cases hruleFull
        | ok inferred => rfl
  have hclosedRun : env.checkNoMVarNoFVar restored.name rule.rhs = .ok () := by
    cases hclosed : env.checkNoMVarNoFVar restored.name rule.rhs with
    | error err =>
        rw [hclosed] at hruleStep
        simp only [bind, Except.bind] at hruleStep
        cases hruleStep
    | ok unit =>
        rcases unit with ⟨⟩
        simpa using hclosed
  have hclosed : rule.rhs.FVarsIn fun _ => False :=
    checkNoMVarNoFVar.closed hclosedRun
  have hfvars : rule.rhs.FVarsIn fun fv => fv ∈
      (TypeChecker.VContext.mkCheckingValid hvalid restored.levelParams
        fuel).vlctx.fvars := by
    simpa [TypeChecker.VContext.mkCheckingValid,
      TypeChecker.VContext.mkChecking] using hclosed
  have Hcheck := TypeChecker.M.WF.runCheckingValid
    (wf := hvalid) (lparams := restored.levelParams) (fuel := fuel)
    (TypeChecker.checkType.WF (e := rule.rhs) hfvars)
  cases htypecheck : TypeChecker.M.run env (safety := safety) (lctx := {})
      (lparams := restored.levelParams) (fuel := fuel)
      (TypeChecker.checkType rule.rhs) with
  | error err =>
      rw [hclosedRun, htypecheck] at hruleStep
      simp only [bind, Except.bind] at hruleStep
      cases hruleStep
  | ok inferred =>
      rcases Hcheck inferred htypecheck with ⟨target, targetType, Htyping⟩
      exact ⟨inferred, target, targetType, Htyping⟩

/-- The exact per-recursor pass supplies both typing and guardedness for the
same checker-selected translation of a literal restored RHS.  In particular,
the guarded target cannot be substituted by a caller-chosen abstract term. -/
theorem validateRestoredRecursorRules.guardedTranslation_of_check
    (hvalid : CheckingEnv.Valid safety env venv)
    (hstep : Lean4Lean.validateRestoredRecursorRules.check env loweredEnv
      lparams safety fuel result recNameMap allIndNames auxRecNames recName =
        .ok ())
    (hlookup : loweredEnv.find? recName = some (.recInfo oldInfo))
    (hrule : rule ∈
      (result.restoreRecursor loweredEnv recNameMap allIndNames recName
        (recNameMap.getD recName recName) oldInfo).rules) :
    let restoredRecursorNames :=
      allIndNames.map (fun name =>
        let oldName := Lean.mkRecName name
        recNameMap.getD oldName oldName) ++
      auxRecNames.map fun oldName => recNameMap.getD oldName oldName
    ∃ inferred target targetType,
      TrTyping venv
        (result.restoreRecursor loweredEnv recNameMap allIndNames recName
          (recNameMap.getD recName recName) oldInfo).levelParams []
        rule.rhs inferred target targetType ∧
      target.GuardedRuleRhs restoredRecursorNames := by
  dsimp only
  rcases validateRestoredRecursorRules.translation_of_check hvalid hstep
      hlookup hrule with ⟨inferred, target, targetType, Htyping⟩
  have HguardRun := validateRestoredRecursorRules.guardCheck_eq_ok_of_check
    hstep hlookup hrule
  exact ⟨inferred, target, targetType, Htyping,
    validateRestoredRecursorRules.guarded_of_checkGuarded HguardRun
      Htyping.2.1⟩

/-- The complete abstract rule selected by one successful literal validation
step.  Equation typing and structural guardedness are deliberately joined
here, before either target expression is hidden behind an existential.  Thus
the guarded RHS is definitionally the RHS occurring in the well-formed
`VDefEq`; no translation-uniqueness principle (and in particular no global
projection-preservation claim) is needed. -/
theorem validateRestoredRecursorRules.validatedAbstractRule_of_check
    (hvalid : CheckingEnv.Valid safety env venv)
    (hstep : Lean4Lean.validateRestoredRecursorRules.check env loweredEnv
      lparams safety fuel result recNameMap allIndNames auxRecNames recName =
        .ok ())
    (hlookup : loweredEnv.find? recName = some (.recInfo oldInfo))
    (hrule : rule ∈
      (result.restoreRecursor loweredEnv recNameMap allIndNames recName
        (recNameMap.getD recName recName) oldInfo).rules) :
    let restored := result.restoreRecursor loweredEnv recNameMap allIndNames
      recName (recNameMap.getD recName recName) oldInfo
    let restoredRecursorNames :=
      allIndNames.map (fun name =>
        let oldName := Lean.mkRecName name
        recNameMap.getD oldName oldName) ++
      auxRecNames.map fun oldName => recNameMap.getD oldName oldName
    ∃ (lhs lhsInferred rhsInferred : Expr)
        (lhsTarget rhsTarget targetType : VExpr),
      Lean4Lean.validateRestoredRecursorRules.buildEquationLhs env restored
        rule = .ok lhs ∧
      TrExprS venv restored.levelParams [] lhs lhsTarget ∧
      TrExprS venv restored.levelParams [] rule.rhs rhsTarget ∧
      TrExprS venv restored.levelParams [] lhsInferred targetType ∧
      Nonempty (({
        uvars := restored.levelParams.length
        lhs := lhsTarget
        rhs := rhsTarget
        type := targetType } : VDefEq).WF venv) ∧
      rhsTarget.GuardedRuleRhs restoredRecursorNames := by
  dsimp only
  have Hequation :=
    validateRestoredRecursorRules.equationCheck_eq_ok_of_check hstep hlookup
      hrule
  rcases validateRestoredRecursorRules.abstractRuleWF_of_checkEquation hvalid
      Hequation with
    ⟨lhs, lhsInferred, rhsInferred, lhsTarget, rhsTarget, targetType,
      Hbuild, Hlhs, Hrhs, Htype, Hwf⟩
  have HguardRun := validateRestoredRecursorRules.guardCheck_eq_ok_of_check
    hstep hlookup hrule
  exact ⟨lhs, lhsInferred, rhsInferred, lhsTarget, rhsTarget, targetType,
    Hbuild, Hlhs, Hrhs, Htype, Hwf,
    validateRestoredRecursorRules.guarded_of_checkGuarded HguardRun Hrhs⟩

/-- Complete primary rule certificate selected from the successful
whole-block validation.  It joins equation WF with the exact source-rule
arity and exact producer-field guardedness on one literal restored RHS. -/
theorem validateRestoredRecursorRules.primaryValidatedExactRule_of_run
    (hvalid : CheckingEnv.Valid safety env venv)
    (hrun : Lean4Lean.validateRestoredRecursorRules.run env loweredEnv lparams
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (htype : indType ∈ types)
    (hlookup : loweredEnv.find? (Lean.mkRecName indType.name) =
      some (.recInfo oldInfo))
    (hsource : sourceRule ∈ oldInfo.rules) :
    let oldRecName := Lean.mkRecName indType.name
    let newRecName := recNameMap.getD oldRecName oldRecName
    let restored := result.restoreRecursor loweredEnv recNameMap allIndNames
      oldRecName newRecName oldInfo
    let restoredRule := result.restoreRule loweredEnv recNameMap oldRecName
      newRecName sourceRule
    let restoredRecursorNames :=
      allIndNames.map (fun name =>
        let oldName := Lean.mkRecName name
        recNameMap.getD oldName oldName) ++
      auxRecNames.map fun oldName => recNameMap.getD oldName oldName
    let sourceRecursorNames := allIndNames.map Lean.mkRecName ++ auxRecNames
    ∃ (lhs lhsInferred residual : Expr)
        (plan canonicalPlan :
          Lean4Lean.validateRestoredRecursorRules.EquationLhsPlan)
        (domains : List VExpr) (lhsBody rhsBody typeBody : VExpr)
        (abstractRule : VDefEq),
      Lean4Lean.validateRestoredRecursorRules.buildPrimaryEquationLhs env
        lparams.length
        (result.nparams + result.types.length +
          (result.types.flatMap (·.ctors)).length)
        restored restoredRule = .ok lhs ∧
      Lean4Lean.validateRestoredRecursorRules.buildEquationLhsPlan env restored
        restoredRule = .ok plan ∧
      plan.indices.size = restored.numIndices ∧
      plan.ctorLevels.length = lparams.length ∧
      restored.numParams + restored.numMotives + restored.numMinors =
        result.nparams + result.types.length +
          (result.types.flatMap (·.ctors)).length ∧
      (let binderCount := restored.numParams + restored.numMotives +
          restored.numMinors + restoredRule.nfields
        let binders := (List.range binderCount).toArray.map fun i =>
          Expr.bvar (binderCount - 1 - i)
        let params := binders.extract 0 restored.numParams
        canonicalPlan = { plan with ctorParams := params }) ∧
      TrExprS venv restored.levelParams [] restoredRule.rhs abstractRule.rhs ∧
      TrExprS venv restored.levelParams [] lhs abstractRule.lhs ∧
      abstractRule.uvars = restored.levelParams.length ∧
      Nonempty (abstractRule.WF venv) ∧
      Expr.LambdaTelescope restoredRule.rhs
        sourceRule.rhs.getNumHeadLambdas residual ∧
      residual.isLambda = false ∧
      domains.length = sourceRule.rhs.getNumHeadLambdas ∧
      abstractRule.lhs = VExpr.wrapLams domains lhsBody ∧
      abstractRule.rhs = VExpr.wrapLams domains rhsBody ∧
      abstractRule.type = VExpr.wrapForalls domains typeBody ∧
      rhsBody.GuardedIota restoredRecursorNames
        (Lean4Lean.validateRestoredRecursorRules.recursiveFieldVars
          sourceRecursorNames sourceRule.rhs) 0 ∧
      Nonempty
        (validateRestoredRecursorRules.CanonicalPrimaryLhsSpine restored
          restoredRule plan domains lhsBody) ∧
      ∃ shape : validateRestoredRecursorRules.PrimaryRuleShapeCertificate
          restored sourceRecursorNames sourceRule restoredRule,
        Nonempty (validateRestoredRecursorRules.CanonicalPrimaryRhsSpine shape
          domains rhsBody) := by
  dsimp only
  have Hprimary := validateRestoredRecursorRules.primaryCheck_eq_ok_of_run
    hrun htype
  have hrestoredRule :
      result.restoreRule loweredEnv recNameMap (Lean.mkRecName indType.name)
          (recNameMap.getD (Lean.mkRecName indType.name)
            (Lean.mkRecName indType.name)) sourceRule ∈
        (result.restoreRecursor loweredEnv recNameMap allIndNames
          (Lean.mkRecName indType.name)
          (recNameMap.getD (Lean.mkRecName indType.name)
            (Lean.mkRecName indType.name)) oldInfo).rules := by
    simp only [Lean4Lean.ElimNestedInductive.Result.restoreRecursor]
    exact List.mem_map.mpr ⟨sourceRule, hsource, rfl⟩
  have Hequation :=
    validateRestoredRecursorRules.primaryCanonicalEquationCheck_of_run hrun
      htype hlookup hsource
  rcases validateRestoredRecursorRules.sharedAbstractRuleWF_of_checkPrimaryEquation
      hvalid Hequation with
    ⟨lhs, lhsInferred, _lhsBodySource, rhsBodySource, plan, canonicalPlan,
      domains, lhsBody, rhsBody, typeBody, Hbuild, Hplan, Hindices, Huvars,
      Hprefix, Hcanonical, _HlhsTelescope, HrhsTelescope, hdomains, HlhsBody,
      HrhsBody, Hlhs,
      Hrhs, Hwf⟩
  have Hexact := validateRestoredRecursorRules.primaryExactGuardCheck_of_run
    hrun htype hlookup hsource
  have HshapeCheck :=
    validateRestoredRecursorRules.primaryShapeCheck_of_run hrun htype hlookup
      hsource
  have Hshape :=
    validateRestoredRecursorRules.primaryRuleShape_of_check HshapeCheck
  rcases Hshape with ⟨Hshape⟩
  rcases validateRestoredRecursorRules.of_checkGuardedWithFieldsAtArity
      Hexact with ⟨Harity, HguardCheck⟩
  have harityEq : sourceRule.rhs.getNumHeadLambdas =
      (result.restoreRecursor loweredEnv recNameMap allIndNames
          (Lean.mkRecName indType.name)
          (recNameMap.getD (Lean.mkRecName indType.name)
            (Lean.mkRecName indType.name)) oldInfo).numParams +
        (result.restoreRecursor loweredEnv recNameMap allIndNames
          (Lean.mkRecName indType.name)
          (recNameMap.getD (Lean.mkRecName indType.name)
            (Lean.mkRecName indType.name)) oldInfo).numMotives +
        (result.restoreRecursor loweredEnv recNameMap allIndNames
          (Lean.mkRecName indType.name)
          (recNameMap.getD (Lean.mkRecName indType.name)
            (Lean.mkRecName indType.name)) oldInfo).numMinors +
        (result.restoreRule loweredEnv recNameMap (Lean.mkRecName indType.name)
          (recNameMap.getD (Lean.mkRecName indType.name)
            (Lean.mkRecName indType.name)) sourceRule).nfields :=
    Hshape.arity_eq ▸ Hshape.source_arity
  have HrhsTelescopeExact : Expr.LambdaTelescope
      (result.restoreRule loweredEnv recNameMap (Lean.mkRecName indType.name)
        (recNameMap.getD (Lean.mkRecName indType.name)
          (Lean.mkRecName indType.name)) sourceRule).rhs
      sourceRule.rhs.getNumHeadLambdas rhsBodySource := by
    rw [harityEq]
    exact HrhsTelescope
  rcases validateRestoredRecursorRules.exactLambdaArity_sound Harity with
    ⟨residual, Htelescope, hresidual⟩
  have hresidualEq : residual = rhsBodySource :=
    Htelescope.result_eq HrhsTelescopeExact
  subst residual
  have Hguard :=
    validateRestoredRecursorRules.guardedResidual_of_checkGuardedWithFields
      HguardCheck HrhsTelescopeExact hresidual (by
        rw [harityEq]
        exact hdomains) Hrhs
  have Hspine :=
    validateRestoredRecursorRules.canonicalPrimaryLhsSpine_of_translation
      Hcanonical HlhsBody hdomains
  have HshapeTelescope : Expr.LambdaTelescope
      (result.restoreRule loweredEnv recNameMap (Lean.mkRecName indType.name)
        (recNameMap.getD (Lean.mkRecName indType.name)
          (Lean.mkRecName indType.name)) sourceRule).rhs
      ((result.restoreRecursor loweredEnv recNameMap allIndNames
          (Lean.mkRecName indType.name)
          (recNameMap.getD (Lean.mkRecName indType.name)
            (Lean.mkRecName indType.name)) oldInfo).numParams +
        (result.restoreRecursor loweredEnv recNameMap allIndNames
          (Lean.mkRecName indType.name)
          (recNameMap.getD (Lean.mkRecName indType.name)
            (Lean.mkRecName indType.name)) oldInfo).numMotives +
        (result.restoreRecursor loweredEnv recNameMap allIndNames
          (Lean.mkRecName indType.name)
          (recNameMap.getD (Lean.mkRecName indType.name)
            (Lean.mkRecName indType.name)) oldInfo).numMinors +
        (result.restoreRule loweredEnv recNameMap (Lean.mkRecName indType.name)
          (recNameMap.getD (Lean.mkRecName indType.name)
            (Lean.mkRecName indType.name)) sourceRule).nfields)
      Hshape.residual := by
    rw [← Hshape.arity_eq]
    exact Hshape.telescope
  have hshapeResidual : Hshape.residual = rhsBodySource :=
    HshapeTelescope.result_eq HrhsTelescope
  have HrhsSpine :=
    validateRestoredRecursorRules.canonicalPrimaryRhsSpine_of_translation
      Hshape (by rw [hshapeResidual]; exact HrhsBody) (by
        rw [Hshape.arity_eq]
        exact hdomains)
  exact ⟨lhs, lhsInferred, rhsBodySource, plan, canonicalPlan, domains,
    lhsBody, rhsBody, typeBody, {
      uvars := (result.restoreRecursor loweredEnv recNameMap allIndNames
        (Lean.mkRecName indType.name)
        (recNameMap.getD (Lean.mkRecName indType.name)
          (Lean.mkRecName indType.name)) oldInfo).levelParams.length
      lhs := VExpr.wrapLams domains lhsBody
      rhs := VExpr.wrapLams domains rhsBody
      type := VExpr.wrapForalls domains typeBody },
    Hbuild, Hplan, Hindices, Huvars, Hprefix, Hcanonical, Hrhs, Hlhs, rfl, Hwf,
    HrhsTelescopeExact,
    hresidual, by rw [harityEq]; exact hdomains,
    rfl, rfl, rfl, Hguard, Hspine, Hshape, HrhsSpine⟩

/-- Primary specialization of `translation_of_check`, selected from the
successful whole-block rule-validation pass. -/
theorem validateRestoredRecursorRules.primaryTranslation_of_run
    (hvalid : CheckingEnv.Valid safety env venv)
    (hrun : Lean4Lean.validateRestoredRecursorRules.run env loweredEnv lparams
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (htype : indType ∈ types)
    (hlookup : loweredEnv.find? (Lean.mkRecName indType.name) =
      some (.recInfo oldInfo))
    (hrule : rule ∈
      (result.restoreRecursor loweredEnv recNameMap allIndNames
        (Lean.mkRecName indType.name)
        (recNameMap.getD (Lean.mkRecName indType.name)
          (Lean.mkRecName indType.name)) oldInfo).rules) :
    ∃ inferred target targetType,
      TrTyping venv
        (result.restoreRecursor loweredEnv recNameMap allIndNames
          (Lean.mkRecName indType.name)
          (recNameMap.getD (Lean.mkRecName indType.name)
            (Lean.mkRecName indType.name)) oldInfo).levelParams []
        rule.rhs inferred target targetType := by
  exact validateRestoredRecursorRules.translation_of_check hvalid
    (validateRestoredRecursorRules.primaryCheck_eq_ok_of_run hrun htype)
      hlookup hrule

/-- Auxiliary specialization of `translation_of_check`, selected from the
successful whole-block rule-validation pass. -/
theorem validateRestoredRecursorRules.auxiliaryTranslation_of_run
    (hvalid : CheckingEnv.Valid safety env venv)
    (hrun : Lean4Lean.validateRestoredRecursorRules.run env loweredEnv lparams
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (hrec : recName ∈ auxRecNames)
    (hlookup : loweredEnv.find? recName = some (.recInfo oldInfo))
    (hrule : rule ∈
      (result.restoreRecursor loweredEnv recNameMap allIndNames recName
        (recNameMap.getD recName recName) oldInfo).rules) :
    ∃ inferred target targetType,
      TrTyping venv
        (result.restoreRecursor loweredEnv recNameMap allIndNames recName
          (recNameMap.getD recName recName) oldInfo).levelParams []
        rule.rhs inferred target targetType := by
  exact validateRestoredRecursorRules.translation_of_check hvalid
    (validateRestoredRecursorRules.auxiliaryCheck_eq_ok_of_run hrun hrec)
      hlookup hrule

/-- Whole-run auxiliary specialization of the joined equation/guard
certificate.  The returned `VDefEq` is assembled from the literal LHS, RHS,
and inferred type chosen by the checker for this exact restored rule. -/
theorem validateRestoredRecursorRules.auxiliaryValidatedAbstractRule_of_run
    (hvalid : CheckingEnv.Valid safety env venv)
    (hrun : Lean4Lean.validateRestoredRecursorRules.run env loweredEnv lparams
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (hrec : recName ∈ auxRecNames)
    (hlookup : loweredEnv.find? recName = some (.recInfo oldInfo))
    (hrule : rule ∈
      (result.restoreRecursor loweredEnv recNameMap allIndNames recName
        (recNameMap.getD recName recName) oldInfo).rules) :
    let restored := result.restoreRecursor loweredEnv recNameMap allIndNames
      recName (recNameMap.getD recName recName) oldInfo
    let restoredRecursorNames :=
      allIndNames.map (fun name =>
        let oldName := Lean.mkRecName name
        recNameMap.getD oldName oldName) ++
      auxRecNames.map fun oldName => recNameMap.getD oldName oldName
    ∃ (lhs lhsInferred : Expr) (abstractRule : VDefEq),
      Lean4Lean.validateRestoredRecursorRules.buildEquationLhs env restored
        rule = .ok lhs ∧
      TrExprS venv restored.levelParams [] rule.rhs abstractRule.rhs ∧
      TrExprS venv restored.levelParams [] lhs abstractRule.lhs ∧
      TrExprS venv restored.levelParams [] lhsInferred abstractRule.type ∧
      abstractRule.uvars = restored.levelParams.length ∧
      Nonempty (abstractRule.WF venv) ∧
      abstractRule.rhs.GuardedRuleRhs restoredRecursorNames := by
  dsimp only
  have Hcheck := validateRestoredRecursorRules.auxiliaryCheck_eq_ok_of_run
    hrun hrec
  rcases validateRestoredRecursorRules.validatedAbstractRule_of_check hvalid
      Hcheck hlookup hrule with
    ⟨lhs, lhsInferred, _rhsInferred, lhsTarget, rhsTarget, targetType,
      Hbuild, Hlhs, Hrhs, Htype, Hwf, Hguard⟩
  exact ⟨lhs, lhsInferred, {
      uvars := (result.restoreRecursor loweredEnv recNameMap allIndNames
        recName (recNameMap.getD recName recName) oldInfo).levelParams.length
      lhs := lhsTarget
      rhs := rhsTarget
      type := targetType },
    Hbuild, Hrhs, Hlhs, Htype, rfl, Hwf, Hguard⟩

end VerifyInductive
end Lean4Lean
