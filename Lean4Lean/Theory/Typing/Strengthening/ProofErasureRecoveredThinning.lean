import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredWeakening
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveryThinning

/-! # Recovered compatible comparison through arbitrary thinning

Typed oracle recovery and computation reconstruct all intermediate originals
below the thinning. The two endpoint oracles keep separate binder annotations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives

/-- Head eta reflects through arbitrary raw thinning by substitution retraction. -/
theorem ProofShape.EtaHead.of_lift' (H : ProofShape.EtaHead (a.lift' ρ) (b.lift' ρ)) :
    ProofShape.EtaHead a b :=
  ProofShape.relation_lift'_reflect (fun _ H => H.subst) H

variable [Params]

/-- Compatible recovered comparison descends in both modes. Independent typed
oracle representatives allow the two binder annotations to remain distinct.
Every computation and recovered function type is reconstructed below. -/
theorem proofErase_recovered_compare_thinning (hstep : ErasedPrimitiveDescent Step)
    (hsubst : ∀ {a b} (σ : ProofShape.Subst), Step a b → Step (a.subst σ) (b.subst σ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.Lift' ρ Γ Γ')
    (hσ : ErasedOracleThinning Γ σ ρ) (hτ : ErasedOracleThinning Γ τ ρ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ProofShape.RecoveredCompare Step σ τ mode
      ((proofErase Γ a).lift' ρ) ((proofErase Γ b).lift' ρ)) :
    (env.IsDefEqU univs Γ A B → env.IsDefEqU univs Γ a b) ∧
    (mode = false → ¬ IsProof Γ a → env.IsDefEqU univs Γ a b) := by
  have hcompute : ErasedPrimitiveThinning (ProofShape.Compute Step) :=
    proofErase_compute_thinning hstep hsubst
  generalize Ea : (proofErase Γ a).lift' ρ = sa at H
  generalize Eb : (proofErase Γ b).lift' ρ = sb at H
  induction H generalizing Γ Γ' ρ a b A B with
  | base H =>
    rw [← Ea, ← Eb] at H
    exact proofErase_compare_reflect hstep hΓ ha hb
      (ProofShape.relation_lift'_reflect (fun _ H => H.subst (fun H => hsubst _ H)) H)
  | app Hf Hx ihf ihx =>
    obtain ⟨_, _, haE, Eaf, Eax⟩ := ProofShape.lift'_app_inv Ea
    obtain ⟨_, _, hbE, Ebf, Ebx⟩ := ProofShape.lift'_app_inv Eb
    obtain ⟨f, x, rfl, hna, Ef, Ex⟩ := erase_app_inv haE
    obtain ⟨f', x', rfl, _, Ef', Ex'⟩ := erase_app_inv hbE
    rw [← Ef] at Eaf
    rw [← Ex] at Eax
    rw [← Ef'] at Ebf
    rw [← Ex'] at Ebx
    obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
    obtain ⟨_, _, hf', hx'⟩ := hb.app_inv henv hΓ
    have HF := (ihf hΓ hΓ' W hσ hτ hf hf' Eaf Ebf).2 rfl (not_isProof_fn hΓ hf hx hna)
    have HFF := HF.of_l henv hΓ hf
    obtain ⟨⟨_, hDD⟩, _⟩ := (HFF.hasType.2.uniqU henv hΓ hf').forallE_inv henv hΓ
    have HX := (ihx hΓ hΓ' W hσ hτ hx hx' Eax Ebx).1 ⟨_, hDD⟩
    have HH : env.IsDefEqU univs Γ _ _ := ⟨_, IsDefEq.appDF HFF (HX.of_l henv hΓ hx)⟩
    exact ⟨fun _ => HH, fun _ _ => HH⟩
  | proj Hm ihm =>
    obtain ⟨_, haE, Eam⟩ := ProofShape.lift'_proj_inv Ea
    obtain ⟨_, hbE, Ebm⟩ := ProofShape.lift'_proj_inv Eb
    obtain ⟨m, rfl, hn, Em⟩ := erase_proj_inv haE
    obtain ⟨m', rfl, _, Em'⟩ := erase_proj_inv hbE
    rw [← Em] at Eam
    rw [← Em'] at Ebm
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm', _, _⟩ := hb.proj_inv henv hΓ
    have HM := (ihm hΓ hΓ' W hσ hτ hm.hasType.2 hm'.hasType.2 Eam Ebm).2 rfl (not_isProof_major hΓ ha hn)
    have HH : env.IsDefEqU univs Γ _ _ :=
      ⟨_, SimAt.proj henv.orderedStrong hΓ (fun _ ht => HM.of_l henv hΓ ht) _ ha⟩
    exact ⟨fun _ => HH, fun _ _ => HH⟩
  | lam HD Hbody ihD ihbody =>
    obtain ⟨_, _, haE, EaD, Eab⟩ := ProofShape.lift'_lam_inv Ea
    obtain ⟨_, _, hbE, EbD, Ebb⟩ := ProofShape.lift'_lam_inv Eb
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv haE
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv hbE
    rw [← ED] at EaD
    rw [← Ebody] at Eab
    rw [← ED'] at EbD
    rw [← Ebody'] at Ebb
    obtain ⟨⟨u, hD⟩, C, hbody⟩ := ha.lam_inv henv hΓ
    obtain ⟨⟨_, hD'⟩, C', hbody'⟩ := hb.lam_inv henv hΓ
    have HDU := (ihD hΓ hΓ' W hσ hτ hD hD' EaD EbD).2 rfl (not_isProof_of_sort hΓ hD)
    have HDD := HDU.of_l henv hΓ hD
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have hΓD' : OnCtx (D.lift' ρ :: Γ') (env.IsType univs) := ⟨hΓ', u, hD.weak' henv.ordered W⟩
    have hctx := IsDefEqCtx.succ .zero HDD.symm
    have Ectx := proofErase_defeqCtx (Γ₁ := D' :: Γ) ⟨hΓ, _, hD'⟩ hctx hbody'
    rw [Ectx] at Ebb
    have hbody'' := hbody'.defeqDFC henv hctx
    have HI := ihbody hΓD hΓD' W.cons
      (EaD ▸ hσ.cons hΓ hD) (EbD ▸ hτ.cons_convert hΓ hD hD' HDU) hbody hbody'' Eab Ebb
    have finish (HH : env.IsDefEqU univs (D :: Γ) body body') :
        env.IsDefEqU univs Γ (.lam D body) (.lam D' body') :=
      ⟨_, IsDefEq.lamDF HDD (HH.of_l henv hΓD hbody)⟩
    constructor
    · intro hAB
      have HPi := ((ha.uniqU henv hΓ (HasType.lam hD hbody)).symm.trans henv hΓ hAB).trans
        henv hΓ (hb.uniqU henv hΓ (HasType.lam hD' hbody'))
      obtain ⟨_, _, hCC⟩ := HPi.forallE_inv henv hΓ
      exact finish (HI.1 ⟨_, hCC⟩)
    · intro hmode hn
      exact finish (HI.2 hmode (fun hp => hn (hp.lam hΓ hD)))
  | forallE HD HC ihD ihC =>
    obtain ⟨_, _, haE, EaD, EaC⟩ := ProofShape.lift'_forallE_inv Ea
    obtain ⟨_, _, hbE, EbD, EbC⟩ := ProofShape.lift'_forallE_inv Eb
    obtain ⟨D, C, rfl, _, ED, EC⟩ := erase_forallE_inv haE
    obtain ⟨D', C', rfl, _, ED', EC'⟩ := erase_forallE_inv hbE
    rw [← ED] at EaD
    rw [← EC] at EaC
    rw [← ED'] at EbD
    rw [← EC'] at EbC
    obtain ⟨⟨u, hD⟩, _, hC⟩ := ha.forallE_inv henv
    obtain ⟨⟨_, hD'⟩, _, hC'⟩ := hb.forallE_inv henv
    have HDU := (ihD hΓ hΓ' W hσ hτ hD hD' EaD EbD).2 rfl (not_isProof_of_sort hΓ hD)
    have HDD := HDU.of_l henv hΓ hD
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have hΓD' : OnCtx (D.lift' ρ :: Γ') (env.IsType univs) := ⟨hΓ', u, hD.weak' henv.ordered W⟩
    have hctx := IsDefEqCtx.succ .zero HDD.symm
    have Ectx := proofErase_defeqCtx (Γ₁ := D' :: Γ) ⟨hΓ, _, hD'⟩ hctx hC'
    rw [Ectx] at EbC
    have HCU := (ihC hΓD hΓD' W.cons
      (EaD ▸ hσ.cons hΓ hD) (EbD ▸ hτ.cons_convert hΓ hD hD' HDU) hC (hC'.defeqDFC henv hctx) EaC EbC).2 rfl
      (not_isProof_of_sort hΓD hC)
    have HH : env.IsDefEqU univs Γ _ _ := ⟨_, IsDefEq.forallEDF HDD (HCU.of_l henv hΓD hC)⟩
    exact ⟨fun _ => HH, fun _ _ => HH⟩
  | etaL HR HD HE ihD =>
    obtain ⟨_, _, Es, EA, Ebody⟩ := ProofShape.lift'_lam_inv Ea
    obtain ⟨D, body, rfl, _, ED, _⟩ := erase_lam_inv Es
    rw [← ED] at EA
    obtain ⟨D', C', hfPi, ED', _⟩ := proofErase_recovered_pi_thinning
      hcompute hΓ hΓ' W hτ hb (Eb ▸ HR)
    obtain ⟨⟨_, hD⟩, _, _⟩ := ha.lam_inv henv hΓ
    obtain ⟨⟨_, hD'⟩, _⟩ := (hfPi.isType henv hΓ).forallE_inv henv
    have HDD := (ihD hΓ hΓ' W hσ hτ hD hD' EA ED').2 rfl (not_isProof_of_sort hΓ hD)
    have HE' : ProofShape.EtaHead ((proofErase Γ (.lam D body)).lift' ρ)
        ((proofErase Γ b).lift' ρ) := by simpa only [Ea, Eb] using HE
    have HH := proofErase_eta_head_infer hΓ ha hfPi HDD HE'.of_lift'
    exact ⟨fun _ => HH, fun _ _ => HH⟩
  | etaR HR HD HE ihD =>
    obtain ⟨_, _, Es, EB, Ebody⟩ := ProofShape.lift'_lam_inv Eb
    obtain ⟨D, body, rfl, _, ED, _⟩ := erase_lam_inv Es
    rw [← ED] at EB
    obtain ⟨D', C', hfPi, ED', _⟩ := proofErase_recovered_pi_thinning
      hcompute hΓ hΓ' W hσ ha (Ea ▸ HR)
    obtain ⟨⟨_, hD⟩, _, _⟩ := hb.lam_inv henv hΓ
    obtain ⟨⟨_, hD'⟩, _⟩ := (hfPi.isType henv hΓ).forallE_inv henv
    have HDD := (ihD hΓ hΓ' W hσ hτ hD' hD ED' EB).2 rfl (not_isProof_of_sort hΓ hD')
    have HE' : ProofShape.EtaHead ((proofErase Γ (.lam D body)).lift' ρ)
        ((proofErase Γ a).lift' ρ) := by simpa only [Ea, Eb] using HE
    have HH := (proofErase_eta_head_infer hΓ hb hfPi HDD.symm HE'.of_lift').symm
    exact ⟨fun _ => HH, fun _ _ => HH⟩
  | compute Ra Rb HC ih =>
    rw [← Ea] at Ra
    rw [← Eb] at Rb
    obtain ⟨a', HA, EA⟩ := hcompute hΓ hΓ' W ha Ra
    obtain ⟨b', HB, EB⟩ := hcompute hΓ hΓ' W hb Rb
    have HI := ih hΓ hΓ' W hσ hτ HA.hasType.2 HB.hasType.2 EA EB
    have finish (HH : env.IsDefEqU univs Γ a' b') : env.IsDefEqU univs Γ a b :=
      ((show env.IsDefEqU univs Γ a a' from ⟨_, HA⟩).trans henv hΓ HH).trans henv hΓ ⟨_, HB.symm⟩
    exact ⟨fun hAB => finish (HI.1 hAB),
      fun hmode hn => finish (HI.2 hmode (mt (isProof_congr hΓ HA).2 hn))⟩

/-- Repeated block weakening preserves the contextual certificate through every
well-formed thinning, including maps with interleaved inserted binders. -/
theorem ErasedRecoveredComparison.weak' (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.Lift' ρ Γ Γ')
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ErasedRecoveredComparison D stage mode Γ a b) :
    ErasedRecoveredComparison D stage mode Γ' (a.lift' ρ) (b.lift' ρ) := by
  generalize hd : ρ.depth = d
  induction d generalizing ρ Γ' with
  | zero => simpa only [VExpr.lift'_depth_zero hd, ← W.depth_zero hd] using H
  | succ d ih =>
    obtain ⟨ρ₀, k, hd₀, rfl⟩ := Lift.depth_succ hd
    obtain ⟨Γ₂, W₁, W₂, hΓ₂⟩ := thinning_split_wf W hΓ hΓ'
    have H₁ := ih hΓ₂ W₁ (by simpa using hd₀)
    have H₂ := H₁.weakN hΓ₂ hΓ' W₂ (ha.weak' henv.ordered W₁) (hb.weak' henv.ordered W₁)
    rw [Lift.consN_skip_eq, VExpr.lift'_comp, VExpr.lift'_comp]
    simpa only [← Lift.skipN_one, VExpr.lift'_consN_skipN] using H₂

/-- Concrete recovered comparison descends through arbitrary thinning
with the same two endpoint-typing modes as the earlier raw comparison. -/
theorem ErasedRecoveredComparison.descend (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.Lift' ρ Γ Γ')
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ErasedRecoveredComparison D stage mode Γ' (a.lift' ρ) (b.lift' ρ)) :
    (env.IsDefEqU univs Γ A B → env.IsDefEqU univs Γ a b) ∧
    (mode = false → ¬ IsProof Γ a → env.IsDefEqU univs Γ a b) := by
  unfold ErasedRecoveredComparison at H
  rw [proofErase_lift' hΓ hΓ' W ha, proofErase_lift' hΓ hΓ' W hb] at H
  have hσ : ErasedOracleThinning Γ (erasedTypeOracle Γ') ρ :=
    ErasedOracleValid.thinning (erasedTypeOracle_valid hΓ') hΓ hΓ' W
  exact proofErase_recovered_compare_thinning (erased_compared_K_stage_descent heq hs stage)
    (fun _ H => erased_compared_K_stage_subst stage H) hΓ hΓ' W hσ hσ ha hb H

/-- Common-typed endpoints need no non-proof premise in recovered descent. -/
theorem ErasedRecoveredComparison.common_descend (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.Lift' ρ Γ Γ')
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b T)
    (H : ErasedRecoveredComparison D stage true Γ' (a.lift' ρ) (b.lift' ρ)) :
    env.IsDefEq univs Γ a b T := by
  obtain ⟨_, hT⟩ := ha.isType henv hΓ
  exact ((H.descend heq hs hΓ hΓ' W ha hb).1 ⟨_, hT⟩).of_l henv hΓ ha

end Lean4Lean.VEnv.Strengthening
