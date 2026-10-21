import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointPropContext

/-! # Beta transport with a fixed source stage

The target may be the whole union while the input certificate stays at one
finite stage. Both endpoints are transported in one invocation: composing two
one-sided laws would incorrectly require stability of the enlarged target.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private beta_images from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointPropBeta
variable [Params]

/-- Missing two-sided beta transport from a specified source relation into a
possibly larger target. It asserts no stability of target certificates. -/
def JointPropBetaTransport
    (Step Target : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ P Q p q}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ P (.sort .zero) → env.HasType univs Γ Q (.sort .zero) →
    JointCompare Step (proofEraseCtx Γ) true (proofErase Γ P) (proofErase Γ Q) →
    ProofShape.BetaRed (proofErase Γ P) p → ProofShape.BetaRed (proofErase Γ Q) q →
    JointCompare Target (proofEraseCtx Γ) true p q

/-- Decreasing the input primitive relation preserves directed beta transport;
the target relation and its unproved stability are untouched. -/
theorem JointPropBetaTransport.source_mono
    (H : JointPropBetaTransport Step Target)
    (hinc : ∀ {Δ a b}, Step' Δ a b → Step Δ a b) :
    JointPropBetaTransport Step' Target :=
  fun hΓ hP hQ HC RP RQ => H hΓ hP hQ (HC.mono hinc) RP RQ

/-- The family of finite-source transport laws is exactly full-union
proposition beta stability, with no uniform bound on output stages. -/
theorem joint_prop_beta_transport_stages_iff :
    (∀ stage, JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D)) ↔
      JointPropBetaStability (ErasedJointUnion D) := by
  constructor
  · intro H Γ P Q out hΓ hP hQ HC R
    obtain ⟨stage, HC⟩ := HC.finite_stage erased_joint_stage_mono
    exact H stage hΓ hP hQ HC .refl R
  · intro H stage Γ P Q p q hΓ hP hQ HC RP RQ
    exact H.forward hΓ hP hQ (HC.mono (fun R => ⟨stage, R⟩)) RP RQ

/-- Arbitrary proposition substitution from stage n uses beta transport only
for input certificates at stage n. The recovering cover uses stage-zero image
recovery, so its expanded comparison remains at n before both endpoints are
contracted together with any additional endpoint beta paths. No beta
transport of a target certificate is invoked. -/
theorem JointPropBetaTransport.subst_beta_stage
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) Target)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (hP : env.HasType univs Γ P (.sort .zero)) (hQ : env.HasType univs Γ Q (.sort .zero))
    (H : JointCompare (ErasedJointStage D stage) (proofEraseCtx Γ) true
      (proofErase Γ P) (proofErase Γ Q))
    (RP : ProofShape.BetaRed (proofErase Γ₀ (P.subst σ)) p)
    (RQ : ProofShape.BetaRed (proofErase Γ₀ (Q.subst σ)) q) :
    JointCompare Target (proofEraseCtx Γ₀) true p q := by
  obtain ⟨ρ, WR, RB, HR⟩ := proofErase_recovering_substitution_cover
    (Step := ErasedJointStage D 0) hΓ₀ W
  have H' := H.subst_recovering (erased_joint_stage_descent heq hs stage)
    (erased_joint_stage_rename heq hs 0)
    (erased_joint_stage_mono (Nat.zero_le stage))
    (fun hΓ ht EΓ WR H => by
      simpa only [Nat.zero_add] using erased_joint_stage_recovering heq hs 0 stage hΓ ht EΓ WR H)
    W.wf hP hQ rfl rfl rfl HR
  have Eρ : ErasedSubstAgreement Γ Γ₀ ρ (fun i => proofErase Γ₀ (ρ i)) := fun _ _ => rfl
  have Eσ : ErasedSubstAgreement Γ Γ₀ σ (fun i => proofErase Γ₀ (σ i)) := fun _ _ => rfl
  rw [← proofErase_subst_with hΓ₀ WR.left hP Eρ,
    ← proofErase_subst_with hΓ₀ WR.left hQ Eρ] at H'
  apply Hbeta hΓ₀ (hP.subst henv.orderedStrong WR.left hΓ₀)
    (hQ.subst henv.orderedStrong WR.left hΓ₀) H'
  · apply ProofShape.BetaRed.trans (b := proofErase Γ₀ (P.subst σ)) _ RP
    rw [proofErase_subst_with hΓ₀ WR.left hP Eρ, proofErase_subst_with hΓ₀ W hP Eσ]
    exact beta_images _ RB
  · apply ProofShape.BetaRed.trans (b := proofErase Γ₀ (Q.subst σ)) _ RQ
    rw [proofErase_subst_with hΓ₀ WR.left hQ Eρ, proofErase_subst_with hΓ₀ W hQ Eσ]
    exact beta_images _ RB

/-- Substitution alone is the reflexive-endpoint case of joint substitution
and beta transport, retaining the fixed source-stage hypothesis. -/
theorem JointPropBetaTransport.subst_stage
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) Target)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (hP : env.HasType univs Γ P (.sort .zero)) (hQ : env.HasType univs Γ Q (.sort .zero))
    (H : JointCompare (ErasedJointStage D stage) (proofEraseCtx Γ) true
      (proofErase Γ P) (proofErase Γ Q)) :
    JointCompare Target (proofEraseCtx Γ₀) true
      (proofErase Γ₀ (P.subst σ)) (proofErase Γ₀ (Q.subst σ)) :=
  Hbeta.subst_beta_stage heq hs hΓ₀ W hP hQ H .refl .refl

/-- Converted contexts and beta-reduced endpoints are transported together
from the original finite stage. This avoids applying beta stability to an
already transported, potentially higher-stage certificate. -/
theorem JointPropBetaTransport.defeqCtx_beta_stage
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) Target)
    (hΓ : OnCtx Γ (env.IsType univs)) (W : IsDefEqCtx env univs Γ Γ₁ Γ₂)
    (hP : env.HasType univs Γ₁ P (.sort .zero)) (hQ : env.HasType univs Γ₁ Q (.sort .zero))
    (H : JointCompare (ErasedJointStage D stage) (proofEraseCtx Γ₁) true
      (proofErase Γ₁ P) (proofErase Γ₁ Q))
    (RP : ProofShape.BetaRed (proofErase Γ₁ P) p) (RQ : ProofShape.BetaRed (proofErase Γ₁ Q) q) :
    JointCompare Target (proofEraseCtx Γ₂) true p q := by
  have W₀ : IsDefEqCtx env univs [] Γ₁ Γ₂ := by
    clear hP hQ H RP RQ
    induction W with
    | zero => exact .refl hΓ
    | succ _ hA ih => exact .succ ih hA
  have hΓ₂ := (W₀.symm henv.ordered).isType
  have WS : Ctx.SubstEq env univs Γ₂ VExpr.Subst.id VExpr.Subst.id Γ₁ :=
    substEq_source_convert hΓ₂ (W₀.symm henv.ordered) (Ctx.SubstEq.id henv.ordered hΓ₂)
  apply Hbeta.subst_beta_stage heq hs hΓ₂ WS hP hQ H
  · simpa only [VExpr.subst_id, ← proofErase_defeqCtx W₀.isType W hP] using RP
  · simpa only [VExpr.subst_id, ← proofErase_defeqCtx W₀.isType W hQ] using RQ

end Lean4Lean.VEnv.Strengthening
