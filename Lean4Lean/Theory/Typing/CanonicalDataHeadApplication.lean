import Lean4Lean.Theory.Typing.CanonicalDataHeadCompatibility
import Lean4Lean.Theory.Typing.CanonicalHeadApplication

/-! Exact trailing-application closure of the concrete data-head machine. -/
namespace Lean4Lean.CanonicalDataHead
open VExpr InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private theorem select_app (registry : Registry) (function argument : VExpr) :
    select registry (.app function argument) =
      (select registry function).map (fun selected =>
        { selected with arguments := selected.arguments ++ [argument] }) := by
  simp only [select, getAppFnArgs_app]
  cases spine : function.getAppFnArgs with
  | mk head args =>
    cases head <;> simp only <;> try rfl
    case const name levels =>
      cases registry.natives name <;> simp only
      · split <;> rfl
      · split <;> rfl
    case elim block owner levels =>
      cases registry.cases block owner <;> simp only
      · rfl
      · split <;> rfl

private theorem legacy_none_function
    (absent : CanonicalHead.step registry (.app function argument) = none) :
    CanonicalHead.step registry function = none := by
  cases found : CanonicalHead.step registry function with
  | none => rfl
  | some out => rw [CanonicalHead.step_app found argument] at absent; contradiction

/-- Before its major argument a selected data head has no new reduction of
its own. Any reduction there must already be a legacy head reduction. -/
private theorem prefix_stuck (selected : select registry expression = some selection)
    (length : selection.arguments.length ≤ selection.majorOffset)
    (absent : CanonicalHead.step registry.toRegistry expression = none) :
    step registry expression = none := by
  induction expression generalizing selection with
  | app function argument ih _ =>
    rw [select_app] at selected
    obtain ⟨previous, chosen, rfl⟩ := Option.map_eq_some_iff.mp selected
    have smaller : previous.arguments.length < previous.majorOffset := by
      simp only [List.length_append, List.length_singleton] at length
      omega
    have notMajor : previous.isMajor = false := by
      simp only [Selected.isMajor, beq_eq_false_iff_ne]
      omega
    have stopped := ih chosen (Nat.le_of_lt smaller) (legacy_none_function absent)
    simp only [step, absent, chosen, notMajor, Bool.false_eq_true, if_false, stopped,
      Option.map_none]
  | proj => simp only [select, getAppFnArgs, getAppFnArgs.go] at selected; contradiction
  | _ => simp only [step, absent]

private theorem program_remove_last {data : NativeRecursorData} {levels : List VLevel}
    {arguments : List VExpr} {last : VExpr} {program : SaturatedProgram data}
    (selected : data.saturatedProgram levels (arguments ++ [last]) = some program)
    (enough : data.majorOffset + 1 ≤ arguments.length) :
    ∃ previous, data.saturatedProgram levels arguments = some previous := by
  unfold saturatedProgram at selected ⊢
  dsimp only at selected ⊢
  split at selected <;> try contradiction
  rename_i levelsValid
  simp only [levelsValid, splitSaturated, enough, if_pos,
    List.length_append, List.length_singleton, show data.majorOffset + 1 ≤ arguments.length + 1 by omega,
    List.take_append_of_le_length enough, List.drop_append_of_le_length enough,
    bind, Option.bind_some] at selected ⊢
  simp only [Option.bind_eq_some_iff] at selected
  obtain ⟨major, foundMajor, source, foundSource, selected⟩ := selected
  split at selected <;> try contradiction
  rename_i counts
  simp only [Option.bind_eq_some_iff] at selected
  obtain ⟨equation, foundEquation, body, foundBody, selected⟩ := selected
  split at selected <;> try contradiction
  rename_i domains
  split at selected <;> try contradiction
  rename_i head
  simp only [Option.bind_eq_some_iff] at selected
  obtain ⟨state, run, selected⟩ := selected
  simp only [foundMajor, foundSource, counts, foundEquation, foundBody, domains, head, run,
    Option.bind_some, Bool.false_eq_true, if_false, pure, Option.pure_def]
  exact ⟨_, rfl⟩

private theorem legacy_still_none
    (source : step registry expression = some out)
    (absent : CanonicalHead.step registry.toRegistry expression = none) (argument : VExpr) :
    CanonicalHead.step registry.toRegistry (.app expression argument) = none := by
  cases spine : expression.getAppFnArgs with
  | mk head args =>
    have old : CanonicalHead.spineStep registry.toRegistry head args = none := by
      simpa only [CanonicalHead.step, spine] using absent
    change CanonicalHead.spineStep registry.toRegistry _ _ = none
    rw [getAppFnArgs_app, spine]
    cases head <;> try rfl
    case lam A B =>
      cases args with
      | cons a rest => simp only [CanonicalHead.spineStep] at old; contradiction
      | nil =>
        have reconstruct := mkApps_getAppFnArgs_eq expression
        change mkApps expression.getAppFnArgs.1 expression.getAppFnArgs.2 = expression at reconstruct
        simp only [spine, mkApps, List.foldl_nil] at reconstruct
        subst expression
        simp only [step, CanonicalHead.step, getAppFnArgs, getAppFnArgs.go,
          CanonicalHead.spineStep] at source
        contradiction
    case const name levels =>
      cases definition : registry.definitions name with
      | some value =>
        simp only [CanonicalHead.spineStep, definition] at old ⊢
        split at old <;> try contradiction
        rename_i failed
        rw [if_neg failed]
      | none =>
        cases native : registry.natives name with
        | none => simp only [CanonicalHead.spineStep, definition, native]
        | some data =>
          by_cases named : data.name = name
          · simp only [CanonicalHead.spineStep, definition, native, named, if_pos,
              CanonicalHead.nativeOutput] at old ⊢
            cases program : data.saturatedProgram levels (args ++ [argument]) with
            | none => rfl
            | some chosen =>
              by_cases enough : data.majorOffset + 1 ≤ args.length
              · obtain ⟨previous, found⟩ := program_remove_last program enough
                rw [found] at old
                contradiction
              · have selected : select registry expression =
                    some ⟨levels, args, data.majorOffset, nativeRules data⟩ := by
                  simp only [select, spine, native, named, if_pos]
                have length : args.length ≤ data.majorOffset := by omega
                rw [prefix_stuck selected length absent] at source
                contradiction
          · simp only [CanonicalHead.spineStep, definition, native, named, ↓reduceIte]

/-- A trailing application does not change an already selected successful
step, including a step inside an eliminator's major or projection argument. -/
theorem step_app (selected : step registry expression = some out) (argument : VExpr) :
    step registry (.app expression argument) = some (out.apply argument) := by
  cases legacy : CanonicalHead.step registry.toRegistry expression with
  | some old =>
    have same := step_of_legacy legacy
    have eq : old = out := Option.some.inj (same.symm.trans selected)
    subst out
    exact step_of_legacy (CanonicalHead.step_app legacy argument)
  | none =>
    have outer := legacy_still_none selected legacy argument
    cases choice : select registry expression with
    | none =>
      simp only [step, outer, choice, selected, Option.map_some]
      simp only [appFunction, CanonicalHead.Output.apply, ← lift'_consN_skipN (k := 0), Lift.consN]
    | some selection =>
      have notMajor : selection.isMajor = false := by
        cases h : selection.isMajor with
        | false => rfl
        | true =>
          have length : selection.arguments.length ≤ selection.majorOffset := by
            exact Nat.le_of_eq (by simpa only [Selected.isMajor, beq_iff_eq] using h)
          rw [prefix_stuck choice length legacy] at selected
          contradiction
      simp only [step, outer, choice, notMajor, Bool.false_eq_true, if_false, selected,
        Option.map_some]
      simp only [appFunction, CanonicalHead.Output.apply, ← lift'_consN_skipN (k := 0), Lift.consN]

theorem Trace.app (trace : Trace registry expression added result) (argument : VExpr) :
    Trace registry (.app expression argument) added (.app result (argument.liftN added.length)) := by
  induction trace generalizing argument with
  | refl => simpa only [List.length_nil, liftN_zero] using Trace.refl (registry := registry)
  | @next expression output added result selected rest ih =>
    have h := Trace.next (step_app selected argument) (ih (argument.liftN output.added.length))
    simpa only [CanonicalHead.Output.apply, List.length_append, liftN_liftN, Nat.add_comm] using h

end Lean4Lean.CanonicalDataHead
