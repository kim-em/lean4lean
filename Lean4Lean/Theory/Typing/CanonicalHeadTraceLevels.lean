import Lean4Lean.Theory.Typing.CanonicalHeadTrace
import Lean4Lean.Theory.Typing.SaturatedNativeLevels

/-! Structural level congruence of the concrete canonical head machine.
The proof follows its selected step and retains the corresponding added
proof telescope; no semantic interpretation of a native rule is assumed. -/

namespace Lean4Lean.CanonicalHead
open VExpr VEnv InductiveSignature NativeRecursorData

structure Output.LevelEquiv (U : Nat) (out out' : Output) : Prop where
  added : List.Forall₂ (EqUpToLevels U) out.added out'.added
  result : EqUpToLevels U out.result out'.result

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

theorem spineStep_levels (headEq : EqUpToLevels U head head')
    (argsEq : List.Forall₂ (EqUpToLevels U) args args')
    (selected : spineStep registry head args = some out) :
    ∃ out', spineStep registry head' args' = some out' ∧ Output.LevelEquiv U out out' := by
  have origin := spineStep_origin selected
  cases origin with
  | beta =>
    cases headEq with
    | lam domainEq bodyEq =>
      cases argsEq with
      | cons argumentEq trailingEq =>
        exact ⟨_, rfl, .nil, (EqUpToLevels.instN argumentEq bodyEq).mkApps_args trailingEq⟩
  | delta definition nameEq lengthEq =>
    cases headEq with
    | const hl hr he =>
      rename_i name levels value levels'
      have hlen := Lean4Lean.List.Forall₂.length_eq he
      refine ⟨⟨[], mkApps (value.value.instL levels') args'⟩, ?_, ?_⟩
      · simp only [spineStep, definition]
        rw [if_pos ⟨nameEq, hlen ▸ lengthEq⟩]
      · exact ⟨.nil, (EqUpToLevels.instL_expr _ hl hr he).mkApps_args argsEq⟩
  | native definition native nameEq program =>
    cases headEq with
    | const hl hr he =>
      obtain ⟨program', selected', programEq⟩ := saturatedProgram_levels hl hr he argsEq program
      refine ⟨⟨program'.state.added, program'.result⟩, ?_, programEq.state.added, programEq.result⟩
      simp only [spineStep, definition, native]
      rw [if_pos nameEq]
      simp only [nativeOutput, selected', Option.map_some]

theorem step_levels (expressionEq : EqUpToLevels U expression expression')
    (selected : step registry expression = some out) :
    ∃ out', step registry expression' = some out' ∧ Output.LevelEquiv U out out' :=
  spineStep_levels (related_spine expressionEq).1 (related_spine expressionEq).2 selected

private theorem related_append {R : α → β → Prop}
    (h : List.Forall₂ R xs ys) (h' : List.Forall₂ R xs' ys') :
    List.Forall₂ R (xs ++ xs') (ys ++ ys') := by
  induction h with
  | nil => exact h'
  | cons h hs ih => exact .cons h ih

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

end Lean4Lean.CanonicalHead
