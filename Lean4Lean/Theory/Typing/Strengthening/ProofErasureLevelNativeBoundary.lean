import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelNativeExample
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedLevelExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeFunctionExample

/-! # Universe conversion leaves the expanded-domain obstruction

Pi domains cannot acquire an application head by forward computation. This
survives all new universe steps and all recovered singleton-family guards.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- A lambda's selected native domain is reached from its written domain
whenever primitive computation has no Pi root. -/
theorem ProofShape.ScopedTypeRecovery.lambda_domain_compute_of_no_root
    (hn : ∀ {Δ A B out}, ¬ Step Δ (.forallE A B) out)
    (R : ScopedTypeRecovery Step Δ (.lam X b) out) :
    ∃ A B, out = .forallE A B ∧ ScopedCompute Step Δ X A := by
  generalize E : ProofShape.lam X b = source at R
  induction R with
  | lam => cases E; exact ⟨_, _, rfl, .refl⟩
  | convert R RC ih =>
    obtain ⟨A, B, EA, RX⟩ := ih E
    rw [EA] at RC
    obtain ⟨A', B', EB, RA⟩ := RC.forallE_domain_inv_of_no_root hn
    exact ⟨A', B', EB, RX.trans RA⟩
  | bvar | sort | const | app | forallE | proj => cases E

namespace TypeFunctionExample
open private image_erasure from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeFunctionExample

/-- Even the level-extended recovered union cannot recover this actually typed
higher-order lambda at its beta-expanded assigned input. Consequently the new
native-image transport class is still not arbitrary typed substitution. -/
theorem level_assigned_recovery_failure (D : PureObservation.Definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ¬ ScopedTypeRecovery (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ)
      (proofErase Γ image) (proofErase Γ assigned) := by
  intro R
  have hAssigned := HasType.forallE (Γ := Γ) inputs_equal.hasType.1 (HasType.sort (l := .zero) (by trivial))
  have EA : proofErase Γ assigned = .forallE (proofErase Γ selected)
      (proofErase (selected :: Γ) (.sort .zero)) :=
    if_neg (not_isProof_of_sort hΓ hAssigned)
  have ES : proofErase Γ selected = .app _ _ :=
    if_neg (not_isProof_of_sort hΓ inputs_equal.hasType.1)
  rw [image_erasure hΓ, EA] at R
  obtain ⟨A, B, E, RA⟩ := R.lambda_domain_compute_of_no_root erased_level_recovered_union_no_pi
  cases E
  obtain ⟨X, Y, E, _⟩ := RA.forallE_domain_inv_of_no_root erased_level_recovered_union_no_pi
  rw [ES] at E
  cases E

end TypeFunctionExample
end Lean4Lean.VEnv.Strengthening
