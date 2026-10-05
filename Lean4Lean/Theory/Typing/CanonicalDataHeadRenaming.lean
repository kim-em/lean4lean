import Lean4Lean.Theory.Typing.CanonicalDataHead

/-! Total renaming of ordinary iota/projection head dispatch, including
failure and the fresh proof binders introduced while reducing a major. -/

namespace Lean4Lean.CanonicalDataHead
open VExpr InductiveSignature
set_option backward.isDefEq.respectTransparency false

theorem Registry.Scoped.rule (scope : registry.Scoped)
    (function selected) (chosen : select registry function = some selected)
    (rule) (member : rule ∈ selected.rules) : rule.equation.rhs.Closed := by
  cases select_origin chosen member with
  | native lookup named index owned generated =>
    exact scope.nativeEquation _ _ lookup index _ generated
  | caseRule lookup owned generated =>
    exact scope.caseEquation _ _ _ lookup _ generated
  | quotient => decide

def Selected.rename (selected : Selected) (ρ : Lift) : Selected :=
  { selected with arguments := selected.arguments.map (·.lift' ρ) }

private theorem spine_rename (expression : VExpr) (ρ : Lift) :
    (expression.lift' ρ).getAppFnArgs =
      (expression.getAppFnArgs.1.lift' ρ, expression.getAppFnArgs.2.map (·.lift' ρ)) := by
  suffices ∀ args, getAppFnArgs.go (expression.lift' ρ) (args.map (·.lift' ρ)) =
      ((getAppFnArgs.go expression args).1.lift' ρ,
        (getAppFnArgs.go expression args).2.map (·.lift' ρ)) from this []
  induction expression with
  | app fn arg ih _ => intro args; exact ih (arg :: args)
  | _ => intro args; rfl

private theorem mkApps_rename (head : VExpr) (arguments : List VExpr) (ρ : Lift) :
    (mkApps head arguments).lift' ρ = mkApps (head.lift' ρ) (arguments.map (·.lift' ρ)) := by
  induction arguments generalizing head with
  | nil => rfl
  | cons arg rest ih => exact ih (.app head arg)

theorem select_rename (registry : Registry) (function : VExpr) (ρ : Lift) :
    select registry (function.lift' ρ) = (select registry function).map (·.rename ρ) := by
  unfold select
  rw [spine_rename]
  cases spine : function.getAppFnArgs with
  | mk head arguments =>
    cases head <;> simp only [lift'] <;> try rfl
    case const name levels =>
      cases lookup : registry.natives name with
      | none => simp only; split <;> rfl
      | some data => simp only; split <;> rfl
    case elim block owner levels =>
      cases lookup : registry.cases block owner with
      | none => rfl
      | some entry => simp only; split <;> rfl

@[simp] theorem Selected.isMajor_rename (selected : Selected) (ρ : Lift) :
    (selected.rename ρ).isMajor = selected.isMajor := by
  simp [Selected.isMajor, Selected.rename]

theorem Rule.run_rename (rule : Rule) (closed : rule.equation.rhs.Closed)
    (selected : Selected) (major : VExpr) (ρ : Lift) :
    rule.run (selected.rename ρ) (major.lift' ρ) =
      (rule.run selected major).map (·.lift' ρ) := by
  unfold Rule.run
  rw [spine_rename]
  cases spine : major.getAppFnArgs with
  | mk head arguments =>
    cases head <;> simp only [lift'] <;> try rfl
    case const name levels =>
      simp only [Selected.rename, List.length_map]
      split
      · simp only [Option.map_some, mkApps_rename,
          (closed.instL (ls := selected.levels)).lift'_eq Lift.Fixes.zero,
          Rule.captures, List.map_append, List.map_take, List.map_drop, List.length_map]
      · rfl

theorem directIota_rename (selected : Selected)
    (closed : ∀ rule ∈ selected.rules, rule.equation.rhs.Closed)
    (major : VExpr) (ρ : Lift) :
    directIota (selected.rename ρ) (major.lift' ρ) =
      (directIota selected major).map (·.lift' ρ) := by
  unfold directIota
  change selected.rules.findSome? (fun rule => rule.run (selected.rename ρ) (major.lift' ρ)) = _
  have mapped : ∀ rules : List Rule, (∀ rule ∈ rules, rule.equation.rhs.Closed) →
      rules.findSome? (fun rule => rule.run (selected.rename ρ) (major.lift' ρ)) =
        (rules.findSome? (fun rule => rule.run selected major)).map (·.lift' ρ) := by
    intro rules hscope
    induction rules with
    | nil => rfl
    | cons rule rest ih =>
      simp only [List.findSome?]
      rw [rule.run_rename (hscope rule List.mem_cons_self)]
      cases result : rule.run selected major with
      | some result => rfl
      | none => exact ih (fun rule member => hscope rule (List.mem_cons_of_mem _ member))
  exact mapped selected.rules closed

theorem project_rename (registry : Registry) (typeName : Name) (index : Nat)
    (major : VExpr) (ρ : Lift) :
    project registry typeName index (major.lift' ρ) =
      (project registry typeName index major).map (·.lift' ρ) := by
  unfold project
  cases lookup : registry.projections typeName with
  | none => rfl
  | some info =>
    simp only [bind, Option.bind_some, spine_rename]
    cases spine : major.getAppFnArgs with
    | mk head arguments =>
      cases head <;> simp only [lift'] <;> try rfl
      case const name levels =>
        split
        · exact List.getElem?_map ..
        · rfl

theorem etaIota_rename (registry : Registry) (selected : Selected)
    (closed : ∀ rule ∈ selected.rules, rule.equation.rhs.Closed)
    (major : VExpr) (ρ : Lift) :
    etaIota registry (selected.rename ρ) (major.lift' ρ) =
      (etaIota registry selected major).map (·.lift' ρ) := by
  cases rules : selected.rules with
  | nil => simp [etaIota, Selected.rename, rules]
  | cons rule rest =>
    cases rest with
    | cons next rest => simp [etaIota, Selected.rename, rules]
    | nil =>
      have rhsClosed := (closed rule (rules ▸ List.mem_singleton_self _)).instL
        (ls := selected.levels)
      simp only [etaIota, Selected.rename, rules, List.length_map]
      cases reverse : registry.structureConstructors rule.constructor with
      | none => rfl
      | some entry =>
        simp only [bind, Option.bind_some]
        cases lookup : registry.projections entry.typeName with
        | none => rfl
        | some info =>
          simp only [Option.bind_some]
          split
          · simp only [Option.map_some, mkApps_rename,
              rhsClosed.lift'_eq Lift.Fixes.zero, List.map_append, List.map_take,
              List.map_map, Function.comp_def, lift']
          · rfl

private theorem liftedArgument (argument : VExpr) (added : List VExpr) (ρ : Lift) :
    (argument.lift' ρ).lift' (.skipN .refl (NativeRecursorData.renameAdded ρ added).length) =
      (argument.lift' (.skipN .refl added.length)).lift' (ρ.consN added.length) := by
  rw [NativeRecursorData.renameAdded_length, ← lift'_comp, ← lift'_comp,
    Lift.skipN_comp_consN, Lift.refl_comp, Lift.comp_skipN]
  rfl

theorem appFunction_rename (out : CanonicalHead.Output) (argument : VExpr) (ρ : Lift) :
    appFunction (out.rename ρ) (argument.lift' ρ) = (appFunction out argument).rename ρ := by
  simp only [appFunction, CanonicalHead.Output.rename, lift', liftedArgument]

theorem appMajor_rename (function : VExpr) (out : CanonicalHead.Output) (ρ : Lift) :
    appMajor (function.lift' ρ) (out.rename ρ) = (appMajor function out).rename ρ := by
  simp only [appMajor, CanonicalHead.Output.rename, lift', liftedArgument]

theorem projMajor_rename (typeName : Name) (index : Nat) (out : CanonicalHead.Output) (ρ : Lift) :
    projMajor typeName index (out.rename ρ) = (projMajor typeName index out).rename ρ := rfl

theorem step_rename (registry : Registry) (hscope : registry.Scoped)
    (expression : VExpr) (ρ : Lift) :
    step registry (expression.lift' ρ) = (step registry expression).map (·.rename ρ) := by
  induction expression with
  | app function argument functionIH argumentIH =>
    change step registry (.app (function.lift' ρ) (argument.lift' ρ)) = _
    conv => lhs; rw [step]
    conv => rhs; rw [step]
    have oldRename := CanonicalHead.step_rename hscope.base (.app function argument) ρ
    simp only [lift'] at oldRename
    rw [oldRename]
    cases old : CanonicalHead.step registry.toRegistry (.app function argument) with
    | some out => rfl
    | none =>
      simp only [Option.map_none]
      rw [select_rename]
      cases selected : select registry function with
      | none =>
        simp only [Option.map_none]
        rw [functionIH]
        cases step registry function with
        | none => rfl
        | some out => exact congrArg some (appFunction_rename out argument ρ)
      | some chosen =>
        simp only [Option.map_some, Selected.isMajor_rename]
        split
        · rw [etaIota_rename registry chosen (hscope.rule function chosen selected)]
          cases reduced : etaIota registry chosen argument with
          | some result => rfl
          | none =>
            simp only [Option.map_none]
            rw [directIota_rename chosen (hscope.rule function chosen selected)]
            cases reduced : directIota chosen argument with
            | some result => rfl
            | none =>
              simp only [Option.map_none]
              rw [argumentIH]
              cases child : step registry argument with
              | none => rfl
              | some out => exact congrArg some (appMajor_rename function out ρ)
        · rw [functionIH]
          cases step registry function with
          | none => rfl
          | some out => exact congrArg some (appFunction_rename out argument ρ)
  | proj typeName index major majorIH =>
    change step registry (.proj typeName index (major.lift' ρ)) = _
    conv => lhs; rw [step]
    conv => rhs; rw [step]
    have oldRename := CanonicalHead.step_rename hscope.base (.proj typeName index major) ρ
    simp only [lift'] at oldRename
    rw [oldRename]
    cases old : CanonicalHead.step registry.toRegistry (.proj typeName index major) with
    | some out => rfl
    | none =>
      simp only [Option.map_none]
      rw [project_rename]
      cases reduced : project registry typeName index major with
      | some result => rfl
      | none =>
        simp only [Option.map_none]
        rw [majorIH]
        cases child : step registry major with
        | none => rfl
        | some out => rfl
  | const name levels =>
    have constant : step registry (.const name levels) =
        CanonicalHead.step registry.toRegistry (.const name levels) := by
      simp only [step]
      cases CanonicalHead.step registry.toRegistry (.const name levels) <;> rfl
    simp only [lift', constant]
    exact CanonicalHead.step_rename hscope.base (.const name levels) ρ
  | _ =>
    simp only [lift', step, CanonicalHead.step, CanonicalHead.spineStep,
      getAppFnArgs, getAppFnArgs.go, Option.map_none]

end Lean4Lean.CanonicalDataHead
