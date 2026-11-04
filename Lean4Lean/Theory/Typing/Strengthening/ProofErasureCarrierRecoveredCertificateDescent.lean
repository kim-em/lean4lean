import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierRecoveredCompare
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointCertificateDescent

/-! # Retaining recovered-carrier certificates through binder descent -/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private ProofShape.liftN_app_inv ProofShape.liftN_proj_inv ProofShape.liftN_lam_inv
  ProofShape.liftN_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

open private carrier_recovered_descent from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierRecoveredCompare

private def CarrierRecoveredCertificateDescent (Target : List ProofShape → ProofShape → ProofShape → Prop) (n : Nat) (Δ : List ProofShape)
    (mode : Bool) (sa sb : ProofShape) : Prop :=
  ∀ {Γ Γ' k a b A B}, OnCtx Γ (env.IsType univs) → OnCtx Γ' (env.IsType univs) →
    Ctx.LiftN n k Γ Γ' → proofEraseCtx Γ' = Δ →
    env.HasType univs Γ a A → env.HasType univs Γ b B →
    (proofErase Γ a).liftN n k = sa → (proofErase Γ b).liftN n k = sb →
    (env.IsDefEqU univs Γ A B → CarrierRecoveredCompare Target (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b)) ∧
    (mode = false → ¬ IsProof Γ a → ¬ IsProof Γ b → CarrierRecoveredCompare Target (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b))

private theorem carrier_recovered_certificate_descent
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Target)
    (H : CarrierRecoveredCompare Step Δ mode sa sb) :
    CarrierRecoveredCertificateDescent Target n Δ mode sa sb := by
  induction H with
  | base H =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    have HC := proofErase_computed_joint_compare_certificate_descend hstep hΓ hΓ' W hΔ ha hb
      (by simpa only [Ea, Eb] using H)
    exact ⟨fun H => .base (HC.1 H), fun hm ha hb => .base (HC.2 hm ha hb)⟩
  | recovered RA RB HC =>
    rename_i mode
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    obtain ⟨A₀, ha₀, RAl, EA₀⟩ := proofErase_scoped_recovery_certificate_descend hstep hΓ hΓ' W ha hΔ
      (by simpa only [Ea] using RA)
    obtain ⟨B₀, hb₀, RBl, EB₀⟩ := proofErase_scoped_recovery_certificate_descend hstep hΓ hΓ' W hb hΔ
      (by simpa only [Eb] using RB)
    obtain ⟨_, hA₀⟩ := ha₀.isType henv hΓ
    obtain ⟨_, hB₀⟩ := hb₀.isType henv hΓ
    have EAB : proofErase Γ A₀ = proofErase Γ B₀ := ProofShape.liftN_inj.1 (EA₀.trans EB₀.symm)
    obtain ⟨_, HAB⟩ := (proofErase_reflect hΓ hA₀ hB₀ EAB).2 (not_isProof_of_sort hΓ hA₀)
    have HAB := (HAB.defeq hΓ).of_l henv hΓ hA₀
    have hbA := HAB.symm.defeq hb₀
    have HCl := proofErase_computed_joint_carrier_certificate_descend hstep hΓ hΓ' W ha₀ hbA
      (by simpa only [hΔ, EA₀, Ea, Eb] using HC)
    have H : CarrierRecoveredCompare Target (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b) :=
      .recovered RAl (EAB.symm ▸ RBl) HCl
    exact ⟨fun _ => H, fun _ _ _ => H⟩
  | app Hf Hx ihf ihx =>
    rename_i mode
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    obtain ⟨_, _, haE, Eaf, Eax⟩ := ProofShape.liftN_app_inv Ea
    obtain ⟨_, _, hbE, Ebf, Ebx⟩ := ProofShape.liftN_app_inv Eb
    obtain ⟨f, x, rfl, hna, Ef, Ex⟩ := erase_app_inv haE
    obtain ⟨f', x', rfl, hnb, Ef', Ex'⟩ := erase_app_inv hbE
    rw [← Ef] at Eaf
    rw [← Ex] at Eax
    rw [← Ef'] at Ebf
    rw [← Ex'] at Ebx
    obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
    obtain ⟨_, _, hf', hx'⟩ := hb.app_inv henv hΓ
    have HF := ((carrier_recovered_descent hstep.descent Hf) hΓ hΓ' W hΔ hf hf' Eaf Ebf).2 rfl (not_isProof_fn hΓ hf hx hna) (not_isProof_fn hΓ hf' hx' hnb)
    have HFF := HF.of_l henv hΓ hf
    obtain ⟨⟨_, hDD⟩, _⟩ := (HFF.hasType.2.uniqU henv hΓ hf').forallE_inv henv hΓ
    have CF := (ihf hΓ hΓ' W hΔ hf hf' Eaf Ebf).2 rfl
      (not_isProof_fn hΓ hf hx hna) (not_isProof_fn hΓ hf' hx' hnb)
    have CX := (ihx hΓ hΓ' W hΔ hx hx' Eax Ebx).1 ⟨_, hDD⟩
    have C : ProofShape.CarrierRecoveredCompare Target (proofEraseCtx Γ) mode
        (proofErase Γ (.app f x)) (proofErase Γ (.app f' x')) := by
      simpa only [proofErase, if_neg hna, if_neg hnb] using ProofShape.CarrierRecoveredCompare.app CF CX
    exact ⟨fun _ => C, fun _ _ _ => C⟩
  | proj Hm ihm =>
    rename_i mode s i
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    obtain ⟨_, haE, Eam⟩ := ProofShape.liftN_proj_inv Ea
    obtain ⟨_, hbE, Ebm⟩ := ProofShape.liftN_proj_inv Eb
    obtain ⟨m, rfl, hn, Em⟩ := erase_proj_inv haE
    obtain ⟨m', rfl, hn', Em'⟩ := erase_proj_inv hbE
    rw [← Em] at Eam
    rw [← Em'] at Ebm
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm', _, _⟩ := hb.proj_inv henv hΓ
    have CM := (ihm hΓ hΓ' W hΔ hm.hasType.2 hm'.hasType.2 Eam Ebm).2 rfl
      (not_isProof_major hΓ ha hn) (not_isProof_major hΓ hb hn')
    have C : ProofShape.CarrierRecoveredCompare Target (proofEraseCtx Γ) mode
        (proofErase Γ (.proj s i m)) (proofErase Γ (.proj s i m')) := by
      simpa only [proofErase, if_neg hn, if_neg hn'] using ProofShape.CarrierRecoveredCompare.proj CM
    exact ⟨fun _ => C, fun _ _ _ => C⟩
  | lam HD Hbody ihD ihbody =>
    rename_i mode rb rb2
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    obtain ⟨_, _, haE, EaD, Eab⟩ := ProofShape.liftN_lam_inv Ea
    obtain ⟨_, _, hbE, EbD, Ebb⟩ := ProofShape.liftN_lam_inv Eb
    obtain ⟨D, body, rfl, hna, ED, Ebody⟩ := erase_lam_inv haE
    obtain ⟨D', body', rfl, hnb, ED', Ebody'⟩ := erase_lam_inv hbE
    rw [← ED] at EaD
    rw [← Ebody] at Eab
    rw [← ED'] at EbD
    rw [← Ebody'] at Ebb
    obtain ⟨⟨u, hD⟩, C, hbody⟩ := ha.lam_inv henv hΓ
    obtain ⟨⟨_, hD'⟩, C', hbody'⟩ := hb.lam_inv henv hΓ
    have HDU := ((carrier_recovered_descent hstep.descent HD) hΓ hΓ' W hΔ hD hD' EaD EbD).2 rfl (not_isProof_of_sort hΓ hD) (not_isProof_of_sort hΓ hD')
    have HDD := HDU.of_l henv hΓ hD
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have hΓD' : OnCtx (D.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', u, hD.weakN henv W⟩
    have hctx := IsDefEqCtx.succ .zero HDD.symm
    have Ectx := proofErase_defeqCtx (Γ₁ := D' :: Γ) ⟨hΓ, _, hD'⟩ hctx hbody'
    rw [Ectx] at Ebb
    have hbody'' := hbody'.defeqDFC henv hctx
    have HI := ihbody hΓD hΓD' W.succ
      (by simp only [proofEraseCtx, proofErase_liftN hΓ hΓ' W hD, hΔ, EaD])
      hbody hbody'' Eab Ebb
    have CD := (ihD hΓ hΓ' W hΔ hD hD' EaD EbD).2 rfl
      (not_isProof_of_sort hΓ hD) (not_isProof_of_sort hΓ hD')
    have finish (CB : ProofShape.CarrierRecoveredCompare Target (proofEraseCtx (D :: Γ)) mode
        (proofErase (D :: Γ) body) (proofErase (D :: Γ) body')) :
        ProofShape.CarrierRecoveredCompare Target (proofEraseCtx Γ) mode
          (proofErase Γ (.lam D body)) (proofErase Γ (.lam D' body')) := by
      simpa only [proofErase, if_neg hna, if_neg hnb, Ectx, proofEraseCtx] using
        (show ProofShape.CarrierRecoveredCompare Target (proofEraseCtx Γ) mode
          (.lam (proofErase Γ D) (proofErase (D :: Γ) body))
          (.lam (proofErase Γ D') (proofErase (D :: Γ) body')) from .lam CD CB)
    constructor
    · intro hAB
      have HPi := ((ha.uniqU henv hΓ (HasType.lam hD hbody)).symm.trans henv hΓ hAB).trans
        henv hΓ (hb.uniqU henv hΓ (HasType.lam hD' hbody'))
      obtain ⟨_, _, hCC⟩ := HPi.forallE_inv henv hΓ
      exact finish (HI.1 ⟨_, hCC⟩)
    · intro hmode hn hn'
      exact finish (HI.2 hmode (fun hp => hn (hp.lam hΓ hD))
        (fun hp => hn' ((isProof_defeqCtx hctx).2 hp |>.lam hΓ hD')))
  | forallE HD HC ihD ihC =>
    rename_i mode
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    obtain ⟨_, _, haE, EaD, EaC⟩ := ProofShape.liftN_forallE_inv Ea
    obtain ⟨_, _, hbE, EbD, EbC⟩ := ProofShape.liftN_forallE_inv Eb
    obtain ⟨D, C, rfl, hna, ED, EC⟩ := erase_forallE_inv haE
    obtain ⟨D', C', rfl, hnb, ED', EC'⟩ := erase_forallE_inv hbE
    rw [← ED] at EaD
    rw [← EC] at EaC
    rw [← ED'] at EbD
    rw [← EC'] at EbC
    obtain ⟨⟨u, hD⟩, _, hC⟩ := ha.forallE_inv henv
    obtain ⟨⟨_, hD'⟩, _, hC'⟩ := hb.forallE_inv henv
    have HDU := ((carrier_recovered_descent hstep.descent HD) hΓ hΓ' W hΔ hD hD' EaD EbD).2 rfl (not_isProof_of_sort hΓ hD) (not_isProof_of_sort hΓ hD')
    have HDD := HDU.of_l henv hΓ hD
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have hΓD' : OnCtx (D.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', u, hD.weakN henv W⟩
    have hctx := IsDefEqCtx.succ .zero HDD.symm
    have Ectx := proofErase_defeqCtx (Γ₁ := D' :: Γ) ⟨hΓ, _, hD'⟩ hctx hC'
    rw [Ectx] at EbC
    have CC := (ihC hΓD hΓD' W.succ
      (by simp only [proofEraseCtx, proofErase_liftN hΓ hΓ' W hD, hΔ, EaD])
      hC (hC'.defeqDFC henv hctx) EaC EbC).2 rfl
      (not_isProof_of_sort hΓD hC) (not_isProof_of_sort hΓD (hC'.defeqDFC henv hctx))
    have CD := (ihD hΓ hΓ' W hΔ hD hD' EaD EbD).2 rfl
      (not_isProof_of_sort hΓ hD) (not_isProof_of_sort hΓ hD')
    have C : ProofShape.CarrierRecoveredCompare Target (proofEraseCtx Γ) mode
        (proofErase Γ (.forallE D C)) (proofErase Γ (.forallE D' C')) := by
      simpa only [proofErase, if_neg hna, if_neg hnb, Ectx, proofEraseCtx] using
        (show ProofShape.CarrierRecoveredCompare Target (proofEraseCtx Γ) mode
          (.forallE (proofErase Γ D) (proofErase (D :: Γ) C))
          (.forallE (proofErase Γ D') (proofErase (D :: Γ) C')) from .forallE CD CC)
    exact ⟨fun _ => C, fun _ _ _ => C⟩
  | compute Ra Rb HC ih =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    rw [← Ea] at Ra
    rw [← Eb] at Rb
    obtain ⟨a', HA, RA, EA⟩ := proofErase_scoped_compute_certificate_descend hstep hΓ hΓ' W ha hΔ Ra
    obtain ⟨b', HB, RB, EB⟩ := proofErase_scoped_compute_certificate_descend hstep hΓ hΓ' W hb hΔ Rb
    have HI := ih hΓ hΓ' W hΔ HA.hasType.2 HB.hasType.2 EA EB
    exact ⟨fun hAB => .compute RA RB (HI.1 hAB),
      fun hmode hn hn' => .compute RA RB (HI.2 hmode (mt (isProof_congr hΓ HA).2 hn)
        (mt (isProof_congr hΓ HB).2 hn'))⟩
  | symm HC ih =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    have HI := ih hΓ hΓ' W hΔ hb ha Eb Ea
    exact ⟨fun hAB => (HI.1 hAB.symm).symm, fun hm hn hn' => (HI.2 hm hn' hn).symm⟩

/-- Exact certificate descent for the compatible recovered-carrier extension.
Both selected native recoveries and the carrier certificate survive below the
inserted block. No soundness assumption on the target relation is needed. -/
theorem proofErase_carrier_recovered_compare_certificate_descend
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Target)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (hΔ : proofEraseCtx Γ' = Δ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : CarrierRecoveredCompare Step Δ mode
      ((proofErase Γ a).liftN n k) ((proofErase Γ b).liftN n k)) :
    (env.IsDefEqU univs Γ A B →
      CarrierRecoveredCompare Target (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b)) ∧
    (mode = false → ¬ IsProof Γ a → ¬ IsProof Γ b →
      CarrierRecoveredCompare Target (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b)) :=
  carrier_recovered_certificate_descent hstep H hΓ hΓ' W hΔ ha hb rfl rfl

end Lean4Lean.VEnv.Strengthening
