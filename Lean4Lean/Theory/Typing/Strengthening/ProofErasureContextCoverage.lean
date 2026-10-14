import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextEta
import Lean4Lean.Theory.Typing.Strengthening.BidirectionalCertificateDescent

/-! # Bidirectional normal coverage of contextual erased comparison

Every existing bidirectional normal certificate has a contextual erased
certificate. Domain sorts come directly from original typing, and recursive
eta needs no computational recovery. Computation remains available throughout
the target relation; declarative completeness and composition remain open.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- Full coverage of the bidirectional normal fragment, in its original mode.
Fresh-spine cancellation removes eta-both with a smaller normal certificate.
No recovery-existence, primitive-descent or canonical-Eq hypothesis is needed. -/
theorem BiNormal.context_compare (hΓ : OnCtx Γ (env.IsType univs))
    (H : BiNormal mode n Γ a b) :
    ProofShape.ContextCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b) := by
  classical
  induction n using Nat.strongRecOn generalizing Γ mode a b with | _ n ih => ?_
  obtain ⟨T, HE⟩ := H.defeq hΓ
  by_cases hna : IsProof Γ a
  · have hnb := (isProof_congr hΓ HE).1 hna
    rw [proofErase_eq_proof.2 hna, proofErase_eq_proof.2 hnb]
    exact .refl
  have hnb : ¬ IsProof Γ b := mt (isProof_congr hΓ HE).2 hna
  cases H with
  | refl => exact .refl
  | sortDF hu hv huv =>
    rw [show proofErase Γ (.sort _) = .sort _ from if_neg hna,
      show proofErase Γ (.sort _) = .sort _ from if_neg hnb]
    exact .base (.base (.sort huv))
  | constDF hc hls hls' hlen hlevels =>
    rw [show proofErase Γ (.const _ _) = .const _ _ from if_neg hna,
      show proofErase Γ (.const _ _) = .const _ _ from if_neg hnb]
    exact .base (.base (.const hlevels))
  | appDF hf hf' hx hx' HF HX =>
    rw [show proofErase Γ (.app _ _) = .app _ _ from if_neg hna,
      show proofErase Γ (.app _ _) = .app _ _ from if_neg hnb]
    exact .app (ih _ (by omega) hΓ HF) (ih _ (by omega) hΓ HX)
  | projDF ht HM =>
    rw [show proofErase Γ (.proj _ _ _) = .proj _ _ _ from if_neg hna,
      show proofErase Γ (.proj _ _ _) = .proj _ _ _ from if_neg hnb]
    exact .proj (ih _ (by omega) hΓ HM)
  | @lamIndependent Γ A₁ u nd A₂ nb b₁ b₂ hA HD HB =>
    have hDA := (HD.defeq hΓ).of_l henv hΓ hA
    have hΓA : OnCtx (A₁ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have hctx := IsDefEqCtx.succ .zero hDA
    obtain ⟨_, Hbody⟩ := HB.defeq hΓA
    have Ebody := proofErase_defeqCtx hΓA hctx Hbody.hasType.2
    rw [show proofErase Γ (.lam A₁ b₁) = .lam _ _ from if_neg hna,
      show proofErase Γ (.lam A₂ b₂) = .lam _ _ from if_neg hnb, ← Ebody]
    exact .lamSorted (.of_typed hΓ hA) (.of_typed hΓ hDA.hasType.2)
      (ih _ (by omega) hΓ HD) (ih _ (by omega) hΓA HB)
  | @lamCommon Γ A A₁ u A₂ n b₁ b₂ HA₁ HA₂ HB =>
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HA₁.hasType.1⟩
    have hΓA₁ : OnCtx (A₁ :: Γ) (env.IsType univs) := ⟨hΓ, u, HA₁.hasType.2⟩
    have hctx₁ := IsDefEqCtx.succ .zero HA₁
    have hctx₂ := IsDefEqCtx.succ .zero HA₂
    obtain ⟨_, Hbody⟩ := HB.defeq hΓA
    have Ebody := (proofErase_defeqCtx hΓA hctx₁ Hbody.hasType.2).symm.trans
      (proofErase_defeqCtx hΓA hctx₂ Hbody.hasType.2)
    rw [show proofErase Γ (.lam A₁ b₁) = .lam _ _ from if_neg hna,
      show proofErase Γ (.lam A₂ b₂) = .lam _ _ from if_neg hnb, ← Ebody]
    exact .lamCommon (ih _ (by omega) hΓA₁ (HB.defeqDFC hΓ hctx₁))
  | @forallEDF Γ A₁ u nd A₂ B₁ v nb B₂ mode hA HD hB HB =>
    have hDA := (HD.defeq hΓ).of_l henv hΓ hA
    have hΓA : OnCtx (A₁ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have hctx := IsDefEqCtx.succ .zero hDA
    have hDB := (HB.defeq hΓA).of_l henv hΓA hB
    have Ebody := proofErase_defeqCtx hΓA hctx hDB.hasType.2
    rw [show proofErase Γ (.forallE A₁ B₁) = .forallE _ _ from if_neg hna,
      show proofErase Γ (.forallE A₂ B₂) = .forallE _ _ from if_neg hnb, ← Ebody]
    exact .forallSorted (.of_typed hΓ hA) (.of_typed hΓ hDA.hasType.2)
      (ih _ (by omega) hΓ HD) (.of_typed hΓA hB) (.of_typed hΓA hDB.hasType.2)
      (ih _ (by omega) hΓA HB)
  | etaL hf HB =>
    obtain ⟨⟨u, hA⟩, _⟩ := (hf.isType henv hΓ).forallE_inv henv
    have hΓA : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have hη := HasType.app (hf.weak henv (B := _)) (.bvar .zero)
    simp only [lift, inst_liftN_bvar] at hη
    have hb := ((HB.defeq hΓA).of_r henv hΓA hη).hasType.1
    exact proofErase_context_etaL hΓ hA hb hf (ih _ (by omega) hΓA HB)
  | etaR hf HB =>
    obtain ⟨⟨u, hA⟩, _⟩ := (hf.isType henv hΓ).forallE_inv henv
    have hΓA : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have hη := HasType.app (hf.weak henv (B := _)) (.bvar .zero)
    simp only [lift, inst_liftN_bvar] at hη
    have hb := ((HB.defeq hΓA).of_l henv hΓA hη).hasType.2
    exact proofErase_context_etaR hΓ hA hb hf (ih _ (by omega) hΓA HB)
  | etaBoth hf hg HB =>
    obtain ⟨k, hk, HK⟩ := BiNormal.etaBoth_inferred hΓ hf hg hna HB
    exact (ih k (by omega) hΓ HK).common
  | proofIrrel hP ha hb => exact (hna ⟨_, ha, hP⟩).elim
  | promote HB => exact (ih _ (by omega) hΓ HB).common

end Lean4Lean.VEnv.Strengthening
