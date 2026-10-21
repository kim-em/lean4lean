import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveringCover
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointPropBeta

/-! # Simultaneous proposition substitution from beta stability

Recoverable expansions of all dependent images replace the earlier single
identity argument. Beta stability contracts those expansions in both typed
propositions. The target context is fixed throughout, including when it was
obtained by extending a substitution under a generated telescope.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private beta_images from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointPropBeta
variable [Params]

/-- Proposition beta stability of the joint union gives arbitrary typed
simultaneous substitution of proposition comparisons. No recovery premise on
any original image, primitive-substitution premise, or re-synthesis law is
assumed; the expanded substitution uses stage-zero image recovery. -/
theorem JointPropBetaStability.subst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (Hbeta : JointPropBetaStability (ErasedJointUnion D))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (hP : env.HasType univs Γ P (.sort .zero)) (hQ : env.HasType univs Γ Q (.sort .zero))
    (H : JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true (proofErase Γ P) (proofErase Γ Q)) :
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ₀) true
      (proofErase Γ₀ (P.subst σ)) (proofErase Γ₀ (Q.subst σ)) := by
  obtain ⟨ρ, WR, RB, HR⟩ := proofErase_recovering_substitution_cover
    (Step := ErasedJointStage D 0) hΓ₀ W
  have H' := H.subst_recovering (erased_joint_union_descent heq hs)
    (erased_joint_stage_rename heq hs 0) (fun R => ⟨0, R⟩)
    (erased_joint_union_recovering heq hs 0) W.wf hP hQ rfl rfl rfl HR
  have Eρ : ErasedSubstAgreement Γ Γ₀ ρ (fun i => proofErase Γ₀ (ρ i)) := fun _ _ => rfl
  have Eσ : ErasedSubstAgreement Γ Γ₀ σ (fun i => proofErase Γ₀ (σ i)) := fun _ _ => rfl
  rw [← proofErase_subst_with hΓ₀ WR.left hP Eρ,
    ← proofErase_subst_with hΓ₀ WR.left hQ Eρ] at H'
  have RP : ProofShape.BetaRed (proofErase Γ₀ (P.subst ρ)) (proofErase Γ₀ (P.subst σ)) := by
    rw [proofErase_subst_with hΓ₀ WR.left hP Eρ, proofErase_subst_with hΓ₀ W hP Eσ]
    exact beta_images _ RB
  have RQ : ProofShape.BetaRed (proofErase Γ₀ (Q.subst ρ)) (proofErase Γ₀ (Q.subst σ)) := by
    rw [proofErase_subst_with hΓ₀ WR.left hQ Eρ, proofErase_subst_with hΓ₀ W hQ Eσ]
    exact beta_images _ RB
  have hPρ := hP.subst henv.orderedStrong WR.left hΓ₀
  have hQρ := hQ.subst henv.orderedStrong WR.left hΓ₀
  have hQσ := hQ.subst henv.orderedStrong W hΓ₀
  have HQ := Hbeta hΓ₀ hPρ hQρ H' RQ
  exact (Hbeta hΓ₀ hQσ hPρ HQ.symm RP).symm

end Lean4Lean.VEnv.Strengthening
