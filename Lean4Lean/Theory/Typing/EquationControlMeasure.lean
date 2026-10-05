import Lean4Lean.Theory.Typing.EquationStratification

/-! A finite alternating order for opening canonical equation sources.
Above the current source cutoff, each equation has its own unfolding fuel.
Crossing to an earlier source can introduce lower controls and more constants;
opening a missing newer equation spends its fuel before those coordinates.
This proves the order and its actual canonical-source edges. Preservation of
the controls by the mutually recursive semantic outputs is a separate goal. -/
namespace Lean4Lean.VEnv.EquationControlMeasure
set_option Elab.async false

/-- Highest equation first; constants and the original closure schedule last.
The fixed length matters: unrestricted lexicographic lists are not well founded. -/
def Key : Nat → Type
  | 0 => Nat × Nat
  | count + 1 => Nat × (Nat × Key count)

@[instance_reducible] def order : (count : Nat) → WellFoundedRelation (Key count)
  | 0 => Prod.lex Nat.lt_wfRel Nat.lt_wfRel
  | count + 1 => Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel (order count))

def Less {count : Nat} (left right : Key count) : Prop := (order count).rel left right

theorem wellFounded (count : Nat) : WellFounded (@Less count) := (order count).wf

def key (count cutoff : Nat) (fuel : Nat → Nat) (constants schedule : Nat) : Key count :=
  match count with
  | 0 => (constants, schedule)
  | count + 1 =>
    (if count + 1 ≤ cutoff then 1 else 0,
      (if cutoff < count + 1 then fuel (count + 1) else 0,
        key count cutoff fuel constants schedule))

/-- Lowering the actual source cutoff permits arbitrary new lower controls,
constant bounds and closure costs. Every still-lawful higher control is kept. -/
theorem cutoffDecrease {count cutoff nextCutoff : Nat} {fuel nextFuel : Nat → Nat}
    {constants nextConstants schedule nextSchedule : Nat}
    (bounded : cutoff ≤ count) (lower : nextCutoff < cutoff)
    (higher : ∀ index, cutoff < index → index ≤ count → nextFuel index ≤ fuel index) :
    Less (key count nextCutoff nextFuel nextConstants nextSchedule)
      (key count cutoff fuel constants schedule) := by
  induction count with
  | zero => omega
  | succ count ih =>
    by_cases atTop : cutoff = count + 1
    · subst cutoff
      simp only [key, if_pos (Nat.le_refl _), if_neg (by omega : ¬ count + 1 ≤ nextCutoff)]
      exact Prod.Lex.left _ _ (by decide : 0 < 1)
    · have beforeTop : cutoff < count + 1 := by omega
      have nextBefore : nextCutoff < count + 1 := by omega
      simp only [key, if_neg (by omega : ¬ count + 1 ≤ cutoff),
        if_neg (by omega : ¬ count + 1 ≤ nextCutoff), if_pos beforeTop, if_pos nextBefore]
      apply Prod.Lex.right
      rcases Nat.lt_or_eq_of_le (higher (count + 1) beforeTop (Nat.le_refl _)) with strict | same
      · exact Prod.Lex.left _ _ strict
      · rw [same]
        exact Prod.Lex.right _ (ih (by omega) (fun index above bound => higher index above (by omega)))

/-- A missing equation can open a source with more constants and any older
equations. Its own strictly spent fuel precedes all of those new coordinates. -/
theorem fuelDecrease {count selected cutoff nextCutoff : Nat} {fuel nextFuel : Nat → Nat}
    {constants nextConstants schedule nextSchedule : Nat}
    (bounded : selected ≤ count) (missing : cutoff < selected) (earlier : nextCutoff < selected)
    (spent : nextFuel selected < fuel selected)
    (higher : ∀ index, selected < index → index ≤ count → nextFuel index ≤ fuel index) :
    Less (key count nextCutoff nextFuel nextConstants nextSchedule)
      (key count cutoff fuel constants schedule) := by
  induction count with
  | zero => omega
  | succ count ih =>
    have beforeTop : cutoff < count + 1 := by omega
    have nextBefore : nextCutoff < count + 1 := by omega
    simp only [key, if_neg (by omega : ¬ count + 1 ≤ cutoff),
      if_neg (by omega : ¬ count + 1 ≤ nextCutoff), if_pos beforeTop, if_pos nextBefore]
    apply Prod.Lex.right
    by_cases atTop : selected = count + 1
    · subst selected
      exact Prod.Lex.left _ _ spent
    · rcases Nat.lt_or_eq_of_le (higher (count + 1) (by omega) (Nat.le_refl _)) with strict | same
      · exact Prod.Lex.left _ _ strict
      · rw [same]
        exact Prod.Lex.right _ (ih (by omega) (fun index above bound => higher index above (by omega)))

/-- Original header descent keeps equation controls fixed. -/
theorem constantsDecrease {constants nextConstants : Nat} (lower : nextConstants < constants)
    (count cutoff : Nat) (fuel : Nat → Nat) (schedule nextSchedule : Nat) :
    Less (key count cutoff fuel nextConstants nextSchedule)
      (key count cutoff fuel constants schedule) := by
  induction count with
  | zero => exact Prod.Lex.left _ _ lower
  | succ count ih => exact Prod.Lex.right _ (Prod.Lex.right _ ih)

/-- Ordinary original subcalls retain every equation and constant control. -/
theorem scheduleDecrease {schedule nextSchedule : Nat} (lower : nextSchedule < schedule)
    (count cutoff : Nat) (fuel : Nat → Nat) (constants : Nat) :
    Less (key count cutoff fuel constants nextSchedule)
      (key count cutoff fuel constants schedule) := by
  induction count with
  | zero => exact Prod.Lex.right _ lower
  | succ count ih => exact Prod.Lex.right _ (Prod.Lex.right _ ih)

/-- The next cutoff is computed from the actual canonical packet. It is not
a supplied declaration-rank inequality or a common-history assumption. -/
theorem selectedSourceDecrease {env : VEnv} {strata : EquationStratification env}
    (selected : strata.Selected rule) {cutoff : Nat} {fuel nextFuel : Nat → Nat}
    {constants nextConstants schedule nextSchedule : Nat}
    (bounded : cutoff ≤ strata.rules.length)
    (higher : ∀ index, max cutoff selected.ordinal < index → index ≤ strata.rules.length →
      nextFuel index ≤ fuel index)
    (spent : cutoff < selected.ordinal → nextFuel selected.ordinal < fuel selected.ordinal) :
    Less (key strata.rules.length (selected.ordinal - 1) nextFuel nextConstants nextSchedule)
      (key strata.rules.length cutoff fuel constants schedule) := by
  have positive := selected.ordinal_pos
  by_cases installed : selected.ordinal ≤ cutoff
  · apply cutoffDecrease bounded (by omega)
    intro index above bound
    exact higher index (by omega) bound
  · apply fuelDecrease selected.ordinal_le (by omega) (by omega) (spent (by omega))
    intro index above bound
    exact higher index (by omega) bound

end Lean4Lean.VEnv.EquationControlMeasure
