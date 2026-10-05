import Lean4Lean.Theory.Inductive.NativeRecursorData

/-! A finite classification for the native proof-field replay.

The parser alone cannot decide whether a proposed fresh field is a proof.
This test uses the actual generic elimination instance: its source can be
Prop, while its target is not identically Prop. The compilation's elimination
admissibility therefore has to justify singleton elimination. Relevant
structure recursors fail this test and retain their ordinary data rules.
-/

namespace Lean4Lean.InductiveSignature.NativeRecursorData

private theorem eval_nil_le (level : VLevel) (values : List Nat) :
    level.eval [] ≤ level.eval values := by
  induction level with
  | zero => exact Nat.le_refl _
  | succ level ih => exact Nat.succ_le_succ ih
  | param index => exact Nat.zero_le _
  | max left right leftIH rightIH =>
    exact Nat.max_le.mpr ⟨Nat.le_trans leftIH (Nat.le_max_left ..), Nat.le_trans rightIH (Nat.le_max_right ..)⟩
  | imax left right leftIH rightIH =>
    simp only [VLevel.eval, Lean.Nat.imax]
    split
    · exact Nat.zero_le _
    · split
      · rename_i rightZero
        have impossible : right.eval [] = 0 := Nat.eq_zero_of_le_zero (rightZero ▸ rightIH)
        contradiction
      · exact Nat.max_le.mpr ⟨Nat.le_trans leftIH (Nat.le_max_left ..), Nat.le_trans rightIH (Nat.le_max_right ..)⟩

theorem neverZero_iff_eval_nil {level : VLevel} :
    level.IsNeverZero ↔ level.eval [] ≠ 0 := by
  refine ⟨fun positive => positive [], ?_⟩
  intro positive values zero
  exact positive (Nat.eq_zero_of_le_zero (zero ▸ eval_nil_le level values))

/-- A purely syntactic, substitution-independent classification. The source
test uses the declared generic levels, never the levels of an occurrence. -/
def proofReplayEligible (data : NativeRecursorData) : Bool :=
  data.schema.signature.families.size == 1 &&
    (data.schema.signature.families[data.owner].resultLevel.inst data.levels).eval [] == 0 &&
    data.largeTarget

theorem proofReplayEligible_spec {data : NativeRecursorData}
    (eligible : data.proofReplayEligible = true) :
    data.schema.signature.families.size = 1 ∧
      (¬ ∀ family ∈ data.schema.signature.families.toList,
        (family.resultLevel.inst data.levels).IsNeverZero) ∧
      ¬ data.target ≈ .zero := by
  simp only [proofReplayEligible, Bool.and_eq_true, beq_iff_eq] at eligible
  refine ⟨eligible.1.1, ?_, ?_⟩
  · intro relevant
    exact relevant _ (Array.getElem_mem_toList ..) [] eligible.1.2
  · intro zero
    have evaluated := VLevel.equiv_def.mp zero (List.replicate data.uvars 1)
    have nonzero := eligible.2
    simp only [largeTarget, evaluated, VLevel.eval, bne_self_eq_false, Bool.false_eq_true]
      at nonzero

theorem proofReplayEligible_of_branches {data : NativeRecursorData}
    (families : data.schema.signature.families.size = 1)
    (notRelevant : ¬ ∀ family ∈ data.schema.signature.families.toList,
      (family.resultLevel.inst data.levels).IsNeverZero)
    (large : data.largeTarget = true) : data.proofReplayEligible = true := by
  have zero : (data.schema.signature.families[data.owner].resultLevel.inst data.levels).eval [] = 0 := by
    apply Classical.byContradiction
    intro nonzero
    apply notRelevant
    intro family member
    obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp member
    have indexEq : index = data.owner.val := by
      have ownerBound := data.owner.isLt
      simp only [Array.length_toList] at bound
      omega
    have sameFamily : family = data.schema.signature.families[data.owner] := by
      simpa only [Array.getElem_toList, indexEq, Fin.getElem_fin] using same.symm
    rw [sameFamily]
    exact neverZero_iff_eval_nil.mpr nonzero
  simp only [proofReplayEligible, families, zero, large, beq_self_eq_true, Bool.and_self]

end Lean4Lean.InductiveSignature.NativeRecursorData
