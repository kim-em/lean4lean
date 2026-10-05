import Lean4Lean.Theory.Typing.EquationControlMeasure

/-! Lower-ranked caller controls are masked beneath a higher canonical
computational head. Opening rank j only needs controls at ranks k ≥ j; rebuilding
that head restores all caller controls without assuming preservation of controls
that became installed in its canonical checking source. This is the finite
algebra required by the proposed stratified query-depth traversal. -/
namespace Lean4Lean.VEnv.EquationStratifiedFuel
set_option Elab.async false

def headDepth (head : Nat) (children : Nat → Nat) (control : Nat) : Nat :=
  if control < head then 0 else children control + if control = head then 1 else 0

def WithinAbove (cutoff : Nat) (fuel depth : Nat → Nat) : Prop :=
  ∀ control, cutoff < control → depth control ≤ fuel control

variable {head control cutoff count : Nat} {fuel children output body typeCode : Nat → Nat}

@[simp] theorem headDepth_below (lower : control < head) : headDepth head children control = 0 :=
  if_pos lower

@[simp] theorem headDepth_at : headDepth head children head = children head + 1 := by
  simp [headDepth]

@[simp] theorem headDepth_above (higher : head < control) :
    headDepth head children control = children control := by
  simp [headDepth, show ¬ control < head by omega, show control ≠ head by omega]

/-- Opening preserves every still-lawful higher control; the selected head
strictly spends one unit when it is above the caller's cutoff. -/
theorem opening
    (bound : WithinAbove cutoff fuel (headDepth head children)) :
    (∀ control, cutoff < control → head < control → children control ≤ fuel control) ∧
      (cutoff < head → children head < fuel head) := by
  constructor
  · intro control active higher
    simpa only [headDepth_above higher] using bound control active
  · intro active
    have paid := bound head active
    rw [headDepth_at] at paid
    omega

/-- Only ranks lawful in the new canonical source are promised by its answer.
No bound is required for an old caller rank strictly below the opened head. -/
theorem rebuild
    (headPositive : 0 < head)
    (incoming : WithinAbove cutoff fuel (headDepth head children))
    (returned : WithinAbove (head - 1) children output) :
    WithinAbove cutoff fuel (headDepth head output) := by
  intro control active
  by_cases lower : control < head
  · simp only [headDepth_below lower]
    exact Nat.zero_le _
  · have child := returned control (by omega)
    have parent := incoming control active
    simp only [headDepth, if_neg lower] at parent ⊢
    omega

/-- A returned type wrapper uses the very same head mask as the returned
value wrapper. Its child may be either actual branch of the incoming maximum. -/
theorem rebuild_component
    (headPositive : 0 < head)
    (incoming : WithinAbove cutoff fuel
      (headDepth head (fun control => max (body control) (typeCode control))))
    (returned : WithinAbove (head - 1)
      (fun control => max (body control) (typeCode control)) output) :
    WithinAbove cutoff fuel (headDepth head output) :=
  rebuild headPositive incoming returned

/-- Canonical opening fits the actual alternating well-founded key using
arbitrary returned lower controls; no global monotonicity below j is needed. -/
theorem openingDecrease
    (headPositive : 0 < head) (headBound : head ≤ count)
    (cutoffBound : cutoff ≤ count)
    (incoming : WithinAbove cutoff fuel (headDepth head children))
    (parentConstants parentSchedule childConstants childSchedule : Nat) :
    EquationControlMeasure.Less
      (EquationControlMeasure.key count (head - 1) children childConstants childSchedule)
      (EquationControlMeasure.key count cutoff fuel parentConstants parentSchedule) := by
  by_cases installed : head ≤ cutoff
  · apply EquationControlMeasure.cutoffDecrease cutoffBound (by omega)
    intro control above _
    exact (opening incoming).1 control above (by omega)
  · have missing : cutoff < head := by omega
    apply EquationControlMeasure.fuelDecrease headBound missing (by omega) ((opening incoming).2 missing)
    intro control higher _
    exact (opening incoming).1 control (by omega) higher

end Lean4Lean.VEnv.EquationStratifiedFuel
