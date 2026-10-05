import Lean4Lean.Theory.Typing.EquationControls
import Lean4Lean.Theory.Typing.AnchoredStageBudgets

/-! The finite caller-budget list corresponding to an equation cutoff.
Only rules strictly above the cutoff are controlled; existing source rules
may legitimately be introduced by original equality steps. -/
namespace Lean4Lean.VEnv.EquationStratification
open AnchoredSource.Adapted
set_option Elab.async false

noncomputable def controlBudgets (strata : EquationStratification env)
    (registry : CanonicalHead.Registry) (cutoff : Nat) (fuel : Nat → Nat) : Budgeted.Budgets :=
  (List.range (strata.rules.length - cutoff)).map fun offset =>
    (strata.headControl registry (cutoff + offset + 1), fuel (cutoff + offset + 1))

theorem within_controlBudgets {strata : EquationStratification env}
    {registry : CanonicalHead.Registry} {cutoff : Nat} {fuel : Nat → Nat}
    {depth : (Name → Bool) → Nat} :
    Budgeted.Within (strata.controlBudgets registry cutoff fuel) depth ↔
      ∀ index, cutoff < index → index ≤ strata.rules.length →
        depth (strata.headControl registry index) ≤ fuel index := by
  constructor
  · intro bounded index above below
    have offset : index - cutoff - 1 < strata.rules.length - cutoff := by omega
    have same : cutoff + (index - cutoff - 1) + 1 = index := by omega
    apply bounded _ _
    apply List.mem_map.mpr
    exact ⟨index - cutoff - 1, List.mem_range.mpr offset, by rw [same]⟩
  · intro bounded current limit member
    obtain ⟨offset, inRange, equal⟩ := List.mem_map.mp member
    cases equal
    have bound := List.mem_range.mp inRange
    exact bounded _ (by omega) (by omega)

/-- This finite list is lawful for every actual source in the envelope. -/
theorem controlBudgets_lawful {strata : EquationStratification env}
    (bounded : strata.SourceCutoff source cutoff)
    (member : (current, limit) ∈ strata.controlBudgets registry cutoff fuel)
    (selected : headEquation registry name = some rule) (active : current name = true) :
    ¬ source.defeqs rule := by
  obtain ⟨offset, _, equal⟩ := List.mem_map.mp member
  cases equal
  exact headControl_lawful bounded (by omega) selected active

end Lean4Lean.VEnv.EquationStratification
