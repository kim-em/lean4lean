import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedPairedBeta
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedConvertedUnit

/-! # Joined bodies at argument images with no computational join

The converted-unit witness supplies inferred-related variable images which
cannot join in the full old carrier-recovered union. Every finite body-beta
join nevertheless instantiates at those distinct images in the aligned checker.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Assuming a positive registered fieldless structure, there are common-typed
nonjoining images for which all finite body-beta joins instantiate. The old
checker cannot compare even the images; the enlarged one handles two bodies
without an argument-join or exact assigned-domain recovery premise. -/
theorem carrier_aligned_nonjoining_images_joined_bodies
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs [] (.const family ls) (.sort (.succ u))) :
    ∃ Γ A x y, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ x A ∧ env.HasType univs Γ y A ∧
      (¬ ∃ out, ScopedCompute (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ x) out ∧
        ScopedCompute (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ y) out) ∧
      (¬ CarrierRecoveredCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) true
        (proofErase Γ x) (proofErase Γ y)) ∧
      (∀ {b c B C shared}, env.HasType univs (A :: Γ) b B → env.HasType univs (A :: Γ) c C →
        ProofShape.BetaRed (proofErase (A :: Γ) b) shared →
        ProofShape.BetaRed (proofErase (A :: Γ) c) shared →
        CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) false
          (proofErase Γ (b.inst x)) (proofErase Γ (c.inst y))) := by
  obtain ⟨Γ, A, a, b, i, j, hΓ, _, _, hiT, hjT, _, _, _, Hno, Hnew⟩ :=
    carrier_aligned_converted_unit_beta_repair (D := D) hi hp hx hf hS
  obtain ⟨v, hA⟩ := hiT.isType henv hΓ
  refine ⟨Γ, A, .bvar i, .bvar j, hΓ, hiT, hjT, ?_, Hno, ?_⟩
  · rintro ⟨out, RX, RY⟩
    exact Hno (.base (.compute RX RY (.leaf .refl)))
  · intro b c B C shared hb hc RB RC
    exact proofErase_carrier_aligned_joined_body_images (erased_carrier_recovered_union_rename heq hs)
      ⟨hΓ, v, hA⟩ ⟨hΓ, v, hA⟩ hb hc hiT hjT hjT RB RC (Hnew.mono (fun H => ⟨0, H⟩))

end Lean4Lean.VEnv.Strengthening
