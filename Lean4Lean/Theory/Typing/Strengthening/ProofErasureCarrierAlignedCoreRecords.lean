import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedRecordApplication
import Lean4Lean.Theory.Typing.Strengthening.DeclarationLevelCompatibility
import Lean4Lean.Theory.Typing.Confluence.Params

/-! # Record carrier computation in actual environments

For the actual declaration registry and concrete pattern table, all primitive
compatibility premises are theorems. The finite recovered union contains these
core steps at stage zero. Record guards therefore support arbitrary finite core
computation at every nested carrier without an extra semantic hypothesis.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr ProofShape PureObservation

variable {E : VEnv} (hE : E.WF) (U : Nat)

/-- Concrete environment computation preserves structural universe variants;
there is no declaration-compatibility or pattern-soundness premise to discharge. -/
theorem proofErase_carrier_aligned_environment_compute_variant
    (R : ProofShape.Compute (@ErasedIotaPrimitive (hE.params U) (Definitions.ofEnv E U hE)) a out)
    (hΓ : OnCtx Γ (E.IsType U)) (hΓ' : OnCtx Γ' (E.IsType U))
    (ht : E.HasType U Γ e T) (ht' : E.HasType U Γ' e' T')
    (Ee : @proofErase (hE.params U) Γ e = a) (V : StructuralVariant a (@proofErase (hE.params U) Γ' e')) :
    ∃ out', ProofShape.Compute (@ErasedIotaPrimitive (hE.params U) (Definitions.ofEnv E U hE))
      (@proofErase (hE.params U) Γ' e') out' ∧ StructuralVariant out out' := by
  letI := hE.params U
  exact proofErase_carrier_aligned_compute_variant (Definitions.ofEnv_sound hE)
    (Definitions.ofEnv_levelCompatible hE) (fun H => H) R hΓ hΓ' ht ht' Ee V

/-- Every finite actual core carrier path can precede a recursive record guard
in the recovered union. Neither canonical Eq nor normalization is needed here. -/
theorem ProofShape.RecordCarrierGuard.environment_core
    (R : ProofShape.Compute (@ErasedIotaPrimitive (hE.params U) (Definitions.ofEnv E U hE)) A A')
    (H : @RecordCarrierGuard (hE.params U) (@ErasedCarrierRecoveredUnion (hE.params U) (Definitions.ofEnv E U hE)) Δ A' a b) :
    @RecordCarrierGuard (hE.params U) (@ErasedCarrierRecoveredUnion (hE.params U) (Definitions.ofEnv E U hE)) Δ A a b := by
  letI := hE.params U
  exact .core (Definitions.ofEnv_sound hE) (Definitions.ofEnv_levelCompatible hE)
    (fun H => H) (fun H => .base ⟨0, H⟩) R H

/-- A stored type alias can expose a recursive record guard, and that guard
transfers to an equivalent universe instance of the alias. The target's stored
body may have different universe syntax; no equality of erased bodies is required. -/
theorem proofErase_carrier_aligned_record_alias_variant
    (heq : E.HasCanonicalEq)
    (HD : (Definitions.ofEnv E U hE).unfolds name ls rhs)
    (HL : List.Forall₂ (· ≈ ·) ls ls')
    (hΓ : OnCtx Γ (E.IsType U))
    (ha : E.HasType U Γ a (.const name ls)) (hb : E.HasType U Γ b (.const name ls))
    (hB : E.HasType U Γ (.const name ls') (.sort v))
    (H : @RecordCarrierGuard (hE.params U) (@ErasedCarrierRecoveredUnion (hE.params U) (Definitions.ofEnv E U hE))
      (@proofEraseCtx (hE.params U) Γ) (@proofErase (hE.params U) [] rhs) (@proofErase (hE.params U) Γ a) (@proofErase (hE.params U) Γ b)) :
    @RecordCarrierGuard (hE.params U) (@ErasedCarrierRecoveredUnion (hE.params U) (Definitions.ofEnv E U hE))
      (@proofEraseCtx (hE.params U) Γ) (@proofErase (hE.params U) Γ (.const name ls')) (@proofErase (hE.params U) Γ a) (@proofErase (hE.params U) Γ b) := by
  letI := hE.params U
  obtain ⟨_, hA⟩ := ha.isType hE hΓ
  have EA : proofErase Γ (.const name ls) = .const name ls := if_neg (not_isProof_of_sort hΓ hA)
  have EB : proofErase Γ (.const name ls') = .const name ls' := if_neg (not_isProof_of_sort hΓ hB)
  have HG := RecordCarrierGuard.environment_core hE U (.base (.inl (.inl (.delta HD)))) H
  apply proofErase_carrier_aligned_record_variant
    (Step := @ErasedCarrierRecoveredUnion (hE.params U) (Definitions.ofEnv E U hE))
    (erased_carrier_recovered_union_descent heq (Definitions.ofEnv_sound hE)) hΓ ha hb hB
  · simpa only [EA, EB] using StructuralVariant.const HL
  · simpa only [EA] using HG

end Lean4Lean.VEnv.Strengthening
