import Lean4Lean.Theory.Typing.CanonicalDataHeadCompatibility
import Lean4Lean.Theory.Typing.CanonicalHeadTraceLevels
import Lean4Lean.Theory.Typing.NativePrefixLevelCongruence

/-! The concrete data head scheduler preserves equivalent universe packets.
All choices depend on equal syntax tags and arities; no typed head equality
or semantic determinism assumption occurs in this transport. -/
namespace Lean4Lean.CanonicalDataHead
open VExpr VEnv InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

private theorem related_take {R : α → β → Prop} (h : List.Forall₂ R xs ys) (n : Nat) :
    List.Forall₂ R (xs.take n) (ys.take n) := by
  induction h generalizing n with
  | nil => simp
  | cons h hs ih => cases n with
    | zero => exact .nil
    | succ n => exact .cons h (ih n)

private theorem related_drop {R : α → β → Prop} (h : List.Forall₂ R xs ys) (n : Nat) :
    List.Forall₂ R (xs.drop n) (ys.drop n) := by
  induction h generalizing n with
  | nil => simp
  | cons h hs ih => cases n with
    | zero => exact .cons h hs
    | succ n => exact ih n

private theorem related_append {R : α → β → Prop}
    (h : List.Forall₂ R xs ys) (h' : List.Forall₂ R xs' ys') :
    List.Forall₂ R (xs ++ xs') (ys ++ ys') := by
  induction h with
  | nil => exact h'
  | cons h hs ih => exact .cons h ih

private theorem related_get {R : α → β → Prop} (h : List.Forall₂ R xs ys) (i : Nat) :
    Option.Rel R xs[i]? ys[i]? := by
  induction h generalizing i with
  | nil => exact .none
  | cons h hs ih => cases i with
    | zero => exact .some h
    | succ i => exact ih i

private theorem related_spine (he : EqUpToLevels U e e') :
    EqUpToLevels U e.getAppFnArgs.1 e'.getAppFnArgs.1 ∧
      List.Forall₂ (EqUpToLevels U) e.getAppFnArgs.2 e'.getAppFnArgs.2 := by
  suffices ∀ args args', List.Forall₂ (EqUpToLevels U) args args' →
      EqUpToLevels U (getAppFnArgs.go e args).1 (getAppFnArgs.go e' args').1 ∧
        List.Forall₂ (EqUpToLevels U)
          (getAppFnArgs.go e args).2 (getAppFnArgs.go e' args').2 from this [] [] .nil
  induction he with
  | app hfn harg ih _ => intro args args' ha; exact ih _ _ (.cons harg ha)
  | bvar => intro args args' ha; exact ⟨.bvar, ha⟩
  | const hl hr he => intro args args' ha; exact ⟨.const hl hr he, ha⟩
  | elim hl hr he => intro args args' ha; exact ⟨.elim hl hr he, ha⟩
  | sort hl hr he => intro args args' ha; exact ⟨.sort hl hr he, ha⟩
  | proj he _ => intro args args' ha; exact ⟨.proj he, ha⟩
  | lam hd hb _ _ => intro args args' ha; exact ⟨.lam hd hb, ha⟩
  | forallE hd hb _ _ => intro args args' ha; exact ⟨.forallE hd hb, ha⟩

structure Selected.LevelEquiv (U : Nat) (selected selected' : Selected) : Prop where
  leftLevels : ∀ l ∈ selected.levels, l.WF U
  rightLevels : ∀ l ∈ selected'.levels, l.WF U
  levels : List.Forall₂ (· ≈ ·) selected.levels selected'.levels
  arguments : List.Forall₂ (EqUpToLevels U) selected.arguments selected'.arguments
  majorOffset : selected.majorOffset = selected'.majorOffset
  rules : selected.rules = selected'.rules

theorem select_levels (he : EqUpToLevels U expression expression') :
    Option.Rel (Selected.LevelEquiv U) (select registry expression) (select registry expression') := by
  obtain ⟨headEq, argsEq⟩ := related_spine he
  unfold select
  cases hs : expression.getAppFnArgs with
  | mk head args =>
    cases ht : expression'.getAppFnArgs with
    | mk head' args' =>
      simp only [hs, ht] at headEq argsEq
      cases headEq <;> simp only <;> try exact .none
      case const ls rs name hl hr levels =>
        cases registry.natives name with
        | none =>
          simp only
          split
          · exact .some ⟨hl, hr, levels, argsEq, rfl, rfl⟩
          · exact .none
        | some data =>
          simp only
          split
          · exact .some ⟨hl, hr, levels, argsEq, rfl, rfl⟩
          · exact .none
      case elim ls rs block owner hl hr levels =>
        cases registry.cases block owner with
        | none => exact .none
        | some entry =>
          simp only
          split
          · exact .some ⟨hl, hr, levels, argsEq, rfl, rfl⟩
          · exact .none

theorem Selected.LevelEquiv.isMajor (equal : Selected.LevelEquiv U selected selected') :
    selected.isMajor = selected'.isMajor := by
  simp only [Selected.isMajor, equal.majorOffset, Lean4Lean.List.Forall₂.length_eq equal.arguments]

theorem Rule.run_levels (equal : Selected.LevelEquiv U selected selected')
    (majorEq : EqUpToLevels U major major') (rule : Rule) :
    Option.Rel (EqUpToLevels U) (rule.run selected major) (rule.run selected' major') := by
  obtain ⟨headEq, argsEq⟩ := related_spine majorEq
  unfold Rule.run
  cases hs : major.getAppFnArgs with
  | mk head args =>
    cases ht : major'.getAppFnArgs with
    | mk head' args' =>
      simp only [hs, ht] at headEq argsEq
      cases headEq <;> simp only <;> try exact .none
      case const ls rs name hl hr levels =>
        simp only [← Lean4Lean.List.Forall₂.length_eq argsEq,
          ← Lean4Lean.List.Forall₂.length_eq equal.levels,
          ← Lean4Lean.List.Forall₂.length_eq equal.arguments]
        split
        · apply Option.Rel.some
          apply (EqUpToLevels.instL_expr rule.equation.rhs
            equal.leftLevels equal.rightLevels equal.levels).mkApps_args
          simp only [Rule.captures]
          rw [← Lean4Lean.List.Forall₂.length_eq argsEq]
          exact related_append (related_take equal.arguments _) (related_drop argsEq _)
        · exact .none

theorem directIota_levels (equal : Selected.LevelEquiv U selected selected')
    (majorEq : EqUpToLevels U major major') :
    Option.Rel (EqUpToLevels U) (directIota selected major) (directIota selected' major') := by
  unfold directIota
  rw [← equal.rules]
  induction selected.rules with
  | nil => exact .none
  | cons rule rest ih =>
    simp only [List.findSome?]
    have h := rule.run_levels equal majorEq
    generalize rule.run selected major = left at h ⊢
    generalize rule.run selected' major' = right at h ⊢
    cases h with
    | none => exact ih
    | some h => exact .some h

theorem etaIota_levels (equal : Selected.LevelEquiv U selected selected')
    (majorEq : EqUpToLevels U major major') :
    Option.Rel (EqUpToLevels U) (etaIota registry selected major) (etaIota registry selected' major') := by
  unfold etaIota
  rw [← equal.rules]
  cases hs : selected.rules with
  | nil => exact .none
  | cons rule rest =>
    cases rest with
    | cons => exact .none
    | nil =>
      simp only
      cases he : registry.structureConstructors rule.constructor with
      | none => simp only [bind, he, Option.bind_none]; exact .none
      | some entry =>
        simp only [bind, he, Option.bind_some]
        cases hp : registry.projections entry.typeName with
        | none => simp only [hp, Option.bind_none]; exact .none
        | some info =>
          simp only [bind, hp, Option.bind_some,
            ← Lean4Lean.List.Forall₂.length_eq equal.levels,
            ← Lean4Lean.List.Forall₂.length_eq equal.arguments]
          split
          · apply Option.Rel.some
            apply (EqUpToLevels.instL_expr rule.equation.rhs
              equal.leftLevels equal.rightLevels equal.levels).mkApps_args
            apply related_append (related_take equal.arguments _)
            apply List.forall₂_map_left_iff.mpr
            apply List.forall₂_map_right_iff.mpr
            induction List.range info.numFields with
            | nil => exact .nil
            | cons index rest ih => exact .cons (.proj majorEq) ih
          · exact .none

theorem project_levels (majorEq : EqUpToLevels U major major') :
    Option.Rel (EqUpToLevels U) (project registry typeName index major)
      (project registry typeName index major') := by
  obtain ⟨headEq, argsEq⟩ := related_spine majorEq
  unfold project
  cases registry.projections typeName with
  | none => exact .none
  | some info =>
    simp only [bind, Option.bind_some]
    cases hs : major.getAppFnArgs with
    | mk head args =>
      cases ht : major'.getAppFnArgs with
      | mk head' args' =>
        simp only [hs, ht] at headEq argsEq
        cases headEq <;> simp only <;> try exact .none
        case const ls rs name hl hr levels =>
          split
          · exact related_get argsEq _
          · exact .none

private theorem legacy_levels (equal : EqUpToLevels U e e') :
    Option.Rel (CanonicalHead.Output.LevelEquiv U)
      (CanonicalHead.step registry e) (CanonicalHead.step registry e') := by
  cases left : CanonicalHead.step registry e with
  | some out =>
    obtain ⟨out', right, relation⟩ := CanonicalHead.step_levels equal left
    rw [right]
    exact .some relation
  | none =>
    cases right : CanonicalHead.step registry e' with
    | none => exact .none
    | some out' =>
      obtain ⟨out, found, _⟩ := CanonicalHead.step_levels equal.symm right
      rw [left] at found
      contradiction

private theorem output_app (relation : CanonicalHead.Output.LevelEquiv U out out')
    (argument : EqUpToLevels U a a') :
    CanonicalHead.Output.LevelEquiv U (appFunction out a) (appFunction out' a') := by
  refine ⟨relation.added, ?_⟩
  simp only [appFunction, ← lift'_consN_skipN (k := 0), Lift.consN]
  rw [← Lean4Lean.List.Forall₂.length_eq relation.added]
  apply EqUpToLevels.app relation.result
  simpa only [← lift'_consN_skipN (k := 0), Lift.consN] using argument.weakN (n := out.added.length) (k := 0)

private theorem output_major (function : EqUpToLevels U f f')
    (relation : CanonicalHead.Output.LevelEquiv U out out') :
    CanonicalHead.Output.LevelEquiv U (appMajor f out) (appMajor f' out') := by
  refine ⟨relation.added, ?_⟩
  simp only [appMajor, ← lift'_consN_skipN (k := 0), Lift.consN]
  rw [← Lean4Lean.List.Forall₂.length_eq relation.added]
  apply EqUpToLevels.app _ relation.result
  simpa only [← lift'_consN_skipN (k := 0), Lift.consN] using function.weakN (n := out.added.length) (k := 0)

private theorem step_app_eq (registry : Registry) (f a : VExpr) :
    step registry (.app f a) =
      match CanonicalHead.step registry.toRegistry (.app f a) with
      | some out => some out
      | none =>
        match select registry f with
        | some selected =>
          if selected.isMajor then
            match etaIota registry selected a with
            | some result => some ⟨[], result⟩
            | none => match directIota selected a with
              | some result => some ⟨[], result⟩
              | none => (step registry a).map (appMajor f)
          else (step registry f).map (fun out => appFunction out a)
        | none => (step registry f).map (fun out => appFunction out a) := by
  rw [step]
  rfl

private theorem step_proj_eq (registry : Registry) (name : Name) (index : Nat) (major : VExpr) :
    step registry (.proj name index major) =
      match project registry name index major with
      | some result => some ⟨[], result⟩
      | none => (step registry major).map (projMajor name index) := by rw [step]; rfl

/-- Total structural level congruence also retains failure, hence preserves
all scheduler priorities exactly. -/
theorem step_levels_relation (equal : EqUpToLevels U expression expression') :
    Option.Rel (CanonicalHead.Output.LevelEquiv U)
      (step registry expression) (step registry expression') := by
  induction equal with
  | app function argument ihf iha =>
    rw [step_app_eq, step_app_eq]
    have legacy := legacy_levels (registry := registry.toRegistry) (.app function argument)
    generalize CanonicalHead.step registry.toRegistry _ = left at legacy ⊢
    generalize CanonicalHead.step registry.toRegistry _ = right at legacy ⊢
    cases legacy with
    | some relation => exact .some relation
    | none =>
      simp only
      have selected := select_levels (registry := registry) function
      generalize select registry _ = left at selected ⊢
      generalize select registry _ = right at selected ⊢
      cases selected with
      | none =>
        simp only
        generalize step registry _ = left at ihf ⊢
        generalize step registry _ = right at ihf ⊢
        cases ihf with
        | none => exact .none
        | some relation => exact .some (output_app relation argument)
      | @some left right relation =>
        simp only
        rw [← relation.isMajor]
        split
        · have eta := etaIota_levels (registry := registry) relation argument
          generalize etaIota registry left _ = le at eta ⊢
          generalize etaIota registry right _ = re at eta ⊢
          cases eta with
          | some result => exact .some ⟨.nil, result⟩
          | none =>
            simp only
            have direct := directIota_levels relation argument
            generalize directIota left _ = ld at direct ⊢
            generalize directIota right _ = rd at direct ⊢
            cases direct with
            | some result => exact .some ⟨.nil, result⟩
            | none =>
              simp only
              generalize step registry _ = left at iha ⊢
              generalize step registry _ = right at iha ⊢
              cases iha with
              | none => exact .none
              | some result => exact .some (output_major function result)
        · generalize step registry _ = left at ihf ⊢
          generalize step registry _ = right at ihf ⊢
          cases ihf with
          | none => exact .none
          | some relation => exact .some (output_app relation argument)
  | @proj major major' name index equal ih =>
    rw [step_proj_eq, step_proj_eq]
    have projected := project_levels (registry := registry) (typeName := name) (index := index) equal
    generalize project registry _ _ _ = left at projected ⊢
    generalize project registry _ _ _ = right at projected ⊢
    cases projected with
    | some result => exact .some ⟨.nil, result⟩
    | none =>
      simp only
      generalize step registry _ = left at ih ⊢
      generalize step registry _ = right at ih ⊢
      cases ih with
      | none => exact .none
      | some result => exact .some ⟨result.added, .proj result.result⟩
  | @const ls rs name hl hr equal =>
    have legacy := legacy_levels (registry := registry.toRegistry) (.const (c := name) hl hr equal)
    simp only [step]
    generalize CanonicalHead.step registry.toRegistry _ = left at legacy ⊢
    generalize CanonicalHead.step registry.toRegistry _ = right at legacy ⊢
    cases legacy with
    | none => exact .none
    | some relation => exact .some relation
  | bvar => simp only [step, CanonicalHead.step, CanonicalHead.spineStep, getAppFnArgs, getAppFnArgs.go]; exact .none
  | sort => simp only [step, CanonicalHead.step, CanonicalHead.spineStep, getAppFnArgs, getAppFnArgs.go]; exact .none
  | elim => simp only [step, CanonicalHead.step, CanonicalHead.spineStep, getAppFnArgs, getAppFnArgs.go]; exact .none
  | lam => simp only [step, CanonicalHead.step, CanonicalHead.spineStep, getAppFnArgs, getAppFnArgs.go]; exact .none
  | forallE => simp only [step, CanonicalHead.step, CanonicalHead.spineStep, getAppFnArgs, getAppFnArgs.go]; exact .none

theorem step_levels (equal : EqUpToLevels U expression expression')
    (selected : step registry expression = some out) :
    ∃ out', step registry expression' = some out' ∧ CanonicalHead.Output.LevelEquiv U out out' := by
  have related := step_levels_relation (registry := registry) equal
  rw [selected] at related
  cases right : step registry expression' with
  | none => rw [right] at related; cases related
  | some out' =>
    rw [right] at related
    cases related with | some relation => exact ⟨out', rfl, relation⟩

theorem Trace.levels (trace : Trace registry expression added result)
    (expressionEq : EqUpToLevels U expression expression') :
    ∃ added' result', Trace registry expression' added' result' ∧
      List.Forall₂ (EqUpToLevels U) added added' ∧ EqUpToLevels U result result' := by
  induction trace generalizing expression' with
  | refl => exact ⟨[], _, .refl, .nil, expressionEq⟩
  | next selected tail ih =>
    obtain ⟨out', selected', outEq⟩ := step_levels expressionEq selected
    obtain ⟨added', result', tail', addedEq, resultEq⟩ := ih outEq.result
    exact ⟨_, _, .next selected' tail', related_append addedEq outEq.added, resultEq⟩

end Lean4Lean.CanonicalDataHead
