import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaClassification
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedEtaBeta

/-! # Paired substitution through typed eta guards

Common typing classifies the fresh eta argument before the two image maps are
applied. The short function's two images compare by typed template congruence;
recursive eta-body checking then handles the long image. No erased eta
contractum is replayed without a typed original.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

/-- A typed common eta guard survives two independently related image maps.
The target comparison recursively contains the new image certificates. -/
theorem proofErase_carrier_aligned_eta_subst_images
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (W : CarrierAlignedSubstitution Step Γ Γ₀ σ φ ρ τ)
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b T)
    (H : EtaHead (proofErase Γ a) (proofErase Γ b)) :
    CarrierAlignedCompare Step (proofEraseCtx Γ₀) true
      ((proofErase Γ a).subst ρ) ((proofErase Γ b).subst τ) := by
  obtain ⟨A, B, u, hA, hbPi, _, E⟩ := proofErase_eta_head_classified W.left.wf ha hb H
  have hAσ := hA.subst henv.orderedStrong W.left W.target_wf
  have hΓA : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) := ⟨W.target_wf, u, hAσ⟩
  have HC := proofErase_carrier_aligned_subst_images hrename W.target_wf W.left hbPi W.left_erasure W.images
  have HR := HC.rename hrename (ContextRenaming.of_liftN W.target_wf hΓA Ctx.LiftN.one)
  simp only [subst_bvar_liftN] at HR
  have Ectx : proofEraseCtx (A.subst σ :: Γ₀) =
      (proofErase Γ A).subst ρ :: proofEraseCtx Γ₀ := by
    simp only [proofEraseCtx, proofErase_subst_with W.target_wf W.left hA W.left_erasure]
  rw [Ectx] at HR
  have S : DomainSort (proofEraseCtx Γ₀) ((proofErase Γ A).subst ρ) u := by
    rw [← proofErase_subst_with W.target_wf W.left hA W.left_erasure]
    exact .of_typed W.target_wf hAσ
  rw [E]
  simp only [ProofShape.subst, ProofShape.lift_subst_lift, etaArgument_subst]
  exact .etaBodyL S (.app HR (.computed (.leaf .refl)))

/-- If both ends of a typed eta guard are lambdas, their bodies have a finite
beta path. The short body's context may use a different displayed domain;
typing and erasure conversion justify the fresh proof-marker case. -/
theorem proofErase_eta_lambda_bodies_beta
    (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs Γ (.lam A b) T) (hf : env.HasType univs Γ (.lam D c) T)
    (H : EtaHead (proofErase Γ (.lam A b)) (proofErase Γ (.lam D c))) :
    ProofShape.BetaRed (proofErase (A :: Γ) b) (proofErase (D :: Γ) c) := by
  obtain ⟨_, _, Eshape, _⟩ := H.shape
  have hn : ¬ IsProof Γ (.lam A b) := by
    intro hp
    rw [proofErase_eq_proof.2 hp] at Eshape
    cases Eshape
  have hnf : ¬ IsProof Γ (.lam D c) := fun hp => hn (isProof_of_common_type hΓ hf he hp)
  have Ee : proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b) := if_neg hn
  have Ef : proofErase Γ (.lam D c) = .lam (proofErase Γ D) (proofErase (D :: Γ) c) := if_neg hnf
  obtain ⟨A₀, C₀, u, hA₀, hfPi, _, EE⟩ := proofErase_eta_head_classified hΓ he hf H
  obtain ⟨⟨v, hD⟩, C, hc⟩ := hf.lam_inv henv hΓ
  obtain ⟨⟨_, HAD⟩, _, _⟩ := (hfPi.uniqU henv hΓ (HasType.lam hD hc)).forallE_inv henv hΓ
  have hctx := IsDefEqCtx.succ .zero HAD.symm
  have Ectx := proofErase_defeqCtx (Γ₁ := D :: Γ) ⟨hΓ, v, hD⟩ hctx hc
  have Erestore := proofErase_eta_inst hΓ hA₀ (hc.defeqDFC henv hctx)
  rw [← Ectx] at Erestore
  have Ebody := (ProofShape.lam.inj (Ee.symm.trans EE)).2
  rw [Ebody, Ef]
  simpa only [ProofShape.liftN, Erestore] using
    (ProofShape.BetaRed.beta (A := (proofErase Γ D).liftN 1)
      (b := (proofErase (D :: Γ) c).liftN 1 1) (a := etaArgument u))

end Lean4Lean.VEnv.Strengthening
