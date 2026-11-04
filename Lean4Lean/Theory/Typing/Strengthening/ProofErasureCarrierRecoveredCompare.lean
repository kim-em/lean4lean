import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointPrimitiveRenaming
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedConvertedHeadBeta

/-! # Compatible comparison through a recovered common carrier

Two native recoveries at the same raw type license explicit carrier checking
in inferred mode. Compatible closure propagates this rule through syntax.
This enlarges the comparison language, without adding primitive computations
or asserting beta stability or completeness of the new relation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private ProofShape.liftN_app_inv ProofShape.liftN_proj_inv ProofShape.liftN_lam_inv
  ProofShape.liftN_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

namespace ProofShape
/-- Compatible closure of computed comparison and checking at a shared
natively recovered carrier. Each binder retains the left annotation. -/
inductive CarrierRecoveredCompare (Step : List ProofShape → ProofShape → ProofShape → Prop) :
    List ProofShape → Bool → ProofShape → ProofShape → Prop where
  | base : ComputedJointCompare Step Δ mode a b → CarrierRecoveredCompare Step Δ mode a b
  | recovered : ScopedTypeRecovery Step Δ a A → ScopedTypeRecovery Step Δ b A →
      ComputedJointCarrierGuard Step Δ A a b → CarrierRecoveredCompare Step Δ mode a b
  | app : CarrierRecoveredCompare Step Δ false f g → CarrierRecoveredCompare Step Δ true a b →
      CarrierRecoveredCompare Step Δ mode (.app f a) (.app g b)
  | proj : CarrierRecoveredCompare Step Δ false a b →
      CarrierRecoveredCompare Step Δ mode (.proj s i a) (.proj s i b)
  | lam : CarrierRecoveredCompare Step Δ false A D → CarrierRecoveredCompare Step (A :: Δ) mode b c →
      CarrierRecoveredCompare Step Δ mode (.lam A b) (.lam D c)
  | forallE : CarrierRecoveredCompare Step Δ false A D → CarrierRecoveredCompare Step (A :: Δ) false B C →
      CarrierRecoveredCompare Step Δ mode (.forallE A B) (.forallE D C)
  | compute : ScopedCompute Step Δ a a' → ScopedCompute Step Δ b b' →
      CarrierRecoveredCompare Step Δ mode a' b' → CarrierRecoveredCompare Step Δ mode a b
  | symm : CarrierRecoveredCompare Step Δ mode a b → CarrierRecoveredCompare Step Δ mode b a

/-- Either checking mode embeds into common mode without changing recursive
inferred premises. -/
theorem CarrierRecoveredCompare.common (H : CarrierRecoveredCompare Step Δ mode a b) :
    CarrierRecoveredCompare Step Δ true a b := by
  induction H with
  | base H => exact .base H.common
  | recovered RA RB H => exact .recovered RA RB H
  | app HF HX => exact .app HF HX
  | proj H => exact .proj H
  | lam HA HB ihA ihB => exact .lam HA ihB
  | forallE HA HB => exact .forallE HA HB
  | compute RA RB H ih => exact .compute RA RB ih
  | symm H ih => exact .symm ih

end ProofShape

private def CarrierRecoveredDescent (n : Nat) (Δ : List ProofShape)
    (mode : Bool) (sa sb : ProofShape) : Prop :=
  ∀ {Γ Γ' k a b A B}, OnCtx Γ (env.IsType univs) → OnCtx Γ' (env.IsType univs) →
    Ctx.LiftN n k Γ Γ' → proofEraseCtx Γ' = Δ →
    env.HasType univs Γ a A → env.HasType univs Γ b B →
    (proofErase Γ a).liftN n k = sa → (proofErase Γ b).liftN n k = sb →
    (env.IsDefEqU univs Γ A B → env.IsDefEqU univs Γ a b) ∧
    (mode = false → ¬ IsProof Γ a → ¬ IsProof Γ b → env.IsDefEqU univs Γ a b)

private theorem carrier_recovered_descent (hstep : ErasedScopedPrimitiveDescent Step)
    (H : CarrierRecoveredCompare Step Δ mode sa sb) : CarrierRecoveredDescent n Δ mode sa sb := by
  induction H with
  | base H =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    exact proofErase_computed_joint_compare_descend hstep hΓ hΓ' W hΔ ha hb
      (by simpa only [Ea, Eb] using H)
  | recovered RA RB HC =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    obtain ⟨A₀, ha₀, EA₀⟩ := proofErase_scoped_typeRecovery_descend hstep hΓ hΓ' W ha hΔ
      (by simpa only [hΔ, Ea] using RA)
    obtain ⟨B₀, hb₀, EB₀⟩ := proofErase_scoped_typeRecovery_descend hstep hΓ hΓ' W hb hΔ
      (by simpa only [hΔ, Eb] using RB)
    obtain ⟨_, hA₀⟩ := ha₀.isType henv hΓ
    obtain ⟨_, hB₀⟩ := hb₀.isType henv hΓ
    have EAB : proofErase Γ A₀ = proofErase Γ B₀ := ProofShape.liftN_inj.1 (EA₀.trans EB₀.symm)
    obtain ⟨_, HAB⟩ := (proofErase_reflect hΓ hA₀ hB₀ EAB).2 (not_isProof_of_sort hΓ hA₀)
    have HAB := (HAB.defeq hΓ).of_l henv hΓ hA₀
    have hbA := HAB.symm.defeq hb₀
    have HH := proofErase_computed_joint_carrier_descend hstep hΓ hΓ' W ha₀ hbA
      (by simpa only [hΔ, EA₀, Ea, Eb] using HC)
    exact ⟨fun _ => HH, fun _ _ _ => HH⟩
  | app Hf Hx ihf ihx =>
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
    have HF := (ihf hΓ hΓ' W hΔ hf hf' Eaf Ebf).2 rfl (not_isProof_fn hΓ hf hx hna) (not_isProof_fn hΓ hf' hx' hnb)
    have HFF := HF.of_l henv hΓ hf
    obtain ⟨⟨_, hDD⟩, _⟩ := (HFF.hasType.2.uniqU henv hΓ hf').forallE_inv henv hΓ
    have HX := (ihx hΓ hΓ' W hΔ hx hx' Eax Ebx).1 ⟨_, hDD⟩
    have HH : env.IsDefEqU univs Γ _ _ := ⟨_, IsDefEq.appDF HFF (HX.of_l henv hΓ hx)⟩
    exact ⟨fun _ => HH, fun _ _ _ => HH⟩
  | proj Hm ihm =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    obtain ⟨_, haE, Eam⟩ := ProofShape.liftN_proj_inv Ea
    obtain ⟨_, hbE, Ebm⟩ := ProofShape.liftN_proj_inv Eb
    obtain ⟨m, rfl, hn, Em⟩ := erase_proj_inv haE
    obtain ⟨m', rfl, hn', Em'⟩ := erase_proj_inv hbE
    rw [← Em] at Eam
    rw [← Em'] at Ebm
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm', _, _⟩ := hb.proj_inv henv hΓ
    have HM := (ihm hΓ hΓ' W hΔ hm.hasType.2 hm'.hasType.2 Eam Ebm).2 rfl (not_isProof_major hΓ ha hn) (not_isProof_major hΓ hb hn')
    have HH : env.IsDefEqU univs Γ _ _ :=
      ⟨_, SimAt.proj henv.orderedStrong hΓ (fun _ ht => HM.of_l henv hΓ ht) _ ha⟩
    exact ⟨fun _ => HH, fun _ _ _ => HH⟩
  | lam HD Hbody ihD ihbody =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    obtain ⟨_, _, haE, EaD, Eab⟩ := ProofShape.liftN_lam_inv Ea
    obtain ⟨_, _, hbE, EbD, Ebb⟩ := ProofShape.liftN_lam_inv Eb
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv haE
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv hbE
    rw [← ED] at EaD
    rw [← Ebody] at Eab
    rw [← ED'] at EbD
    rw [← Ebody'] at Ebb
    obtain ⟨⟨u, hD⟩, C, hbody⟩ := ha.lam_inv henv hΓ
    obtain ⟨⟨_, hD'⟩, C', hbody'⟩ := hb.lam_inv henv hΓ
    have HDU := (ihD hΓ hΓ' W hΔ hD hD' EaD EbD).2 rfl (not_isProof_of_sort hΓ hD) (not_isProof_of_sort hΓ hD')
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
    have finish (HH : env.IsDefEqU univs (D :: Γ) body body') :
        env.IsDefEqU univs Γ (.lam D body) (.lam D' body') :=
      ⟨_, IsDefEq.lamDF HDD (HH.of_l henv hΓD hbody)⟩
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
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    obtain ⟨_, _, haE, EaD, EaC⟩ := ProofShape.liftN_forallE_inv Ea
    obtain ⟨_, _, hbE, EbD, EbC⟩ := ProofShape.liftN_forallE_inv Eb
    obtain ⟨D, C, rfl, _, ED, EC⟩ := erase_forallE_inv haE
    obtain ⟨D', C', rfl, _, ED', EC'⟩ := erase_forallE_inv hbE
    rw [← ED] at EaD
    rw [← EC] at EaC
    rw [← ED'] at EbD
    rw [← EC'] at EbC
    obtain ⟨⟨u, hD⟩, _, hC⟩ := ha.forallE_inv henv
    obtain ⟨⟨_, hD'⟩, _, hC'⟩ := hb.forallE_inv henv
    have HDU := (ihD hΓ hΓ' W hΔ hD hD' EaD EbD).2 rfl (not_isProof_of_sort hΓ hD) (not_isProof_of_sort hΓ hD')
    have HDD := HDU.of_l henv hΓ hD
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have hΓD' : OnCtx (D.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', u, hD.weakN henv W⟩
    have hctx := IsDefEqCtx.succ .zero HDD.symm
    have Ectx := proofErase_defeqCtx (Γ₁ := D' :: Γ) ⟨hΓ, _, hD'⟩ hctx hC'
    rw [Ectx] at EbC
    have HCU := (ihC hΓD hΓD' W.succ
      (by simp only [proofEraseCtx, proofErase_liftN hΓ hΓ' W hD, hΔ, EaD])
      hC (hC'.defeqDFC henv hctx) EaC EbC).2 rfl
      (not_isProof_of_sort hΓD hC) (not_isProof_of_sort hΓD (hC'.defeqDFC henv hctx))
    have HH : env.IsDefEqU univs Γ _ _ := ⟨_, IsDefEq.forallEDF HDD (HCU.of_l henv hΓD hC)⟩
    exact ⟨fun _ => HH, fun _ _ _ => HH⟩
  | compute Ra Rb HC ih =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    rw [← Ea] at Ra
    rw [← Eb] at Rb
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ' W ha hΔ Ra
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ' W hb hΔ Rb
    have HI := ih hΓ hΓ' W hΔ HA.hasType.2 HB.hasType.2 EA EB
    have finish (HH : env.IsDefEqU univs Γ a' b') : env.IsDefEqU univs Γ a b :=
      ((show env.IsDefEqU univs Γ a a' from ⟨_, HA⟩).trans henv hΓ HH).trans henv hΓ ⟨_, HB.symm⟩
    exact ⟨fun hAB => finish (HI.1 hAB),
      fun hmode hn hn' => finish (HI.2 hmode (mt (isProof_congr hΓ HA).2 hn)
        (mt (isProof_congr hΓ HB).2 hn'))⟩

  | symm HC ih =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    have HI := ih hΓ hΓ' W hΔ hb ha Eb Ea
    exact ⟨fun hAB => (HI.1 hAB.symm).symm, fun hm hn hn' => (HI.2 hm hn' hn).symm⟩



/-- The enlarged comparison descends through arbitrary inserted binder blocks.
The recovered-carrier case reconstructs both lower types and aligns them by
literal erasure reflection before using carrier descent. -/
theorem proofErase_carrier_recovered_compare_descend (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (hΔ : proofEraseCtx Γ' = Δ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : CarrierRecoveredCompare Step Δ mode
      ((proofErase Γ a).liftN n k) ((proofErase Γ b).liftN n k)) :
    (env.IsDefEqU univs Γ A B → env.IsDefEqU univs Γ a b) ∧
    (mode = false → ¬ IsProof Γ a → ¬ IsProof Γ b → env.IsDefEqU univs Γ a b) :=
  carrier_recovered_descent hstep H hΓ hΓ' W hΔ ha hb rfl rfl

end Lean4Lean.VEnv.Strengthening
