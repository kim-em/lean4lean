import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredComparison

/-! # Erased comparison checked against endpoint types

Common-mode lambdas compare their bodies while their supplied endpoint typings
align the domains. Inferred mode still requires independent justification.
Recovered types can align endpoints before using a common-mode certificate.
Completeness and typed composition are not assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private ProofShape.liftN_app_inv ProofShape.liftN_proj_inv ProofShape.liftN_lam_inv
  ProofShape.liftN_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

namespace ProofShape
/-- Compatible erased comparison with a checking rule for common-type lambdas
and recovery of endpoint types for inferred use of a common certificate. -/
inductive CheckedCompare (Step : ProofShape → ProofShape → Prop) :
    TypeOracle → TypeOracle → Bool → ProofShape → ProofShape → Prop where
  | base : RecoveredCompare Step σ τ mode a b → CheckedCompare Step σ τ mode a b
  | app : CheckedCompare Step σ τ false f f' → CheckedCompare Step σ τ true a a' →
      CheckedCompare Step σ τ mode (.app f a) (.app f' a')
  | proj : CheckedCompare Step σ τ false m m' → CheckedCompare Step σ τ mode (.proj s i m) (.proj s i m')
  | lam : CheckedCompare Step σ τ false A A' →
      CheckedCompare Step (σ.cons A) (τ.cons A') mode b b' →
      CheckedCompare Step σ τ mode (.lam A b) (.lam A' b')
  | forallE : CheckedCompare Step σ τ false A A' →
      CheckedCompare Step (σ.cons A) (τ.cons A') false B B' →
      CheckedCompare Step σ τ mode (.forallE A B) (.forallE A' B')
  | etaL : TypeRecovery Step τ f (.forallE D C) → CheckedCompare Step σ τ false A D →
      EtaHead (.lam A b) f → CheckedCompare Step σ τ mode (.lam A b) f
  | etaR : TypeRecovery Step σ f (.forallE D C) → CheckedCompare Step σ τ false D A →
      EtaHead (.lam A b) f → CheckedCompare Step σ τ mode f (.lam A b)
  /-- Common endpoint types already align lambda domains during replay. -/
  | lamCommon : CheckedCompare Step (σ.cons A) (τ.cons A') true b b' →
      CheckedCompare Step σ τ true (.lam A b) (.lam A' b')
  /-- Recovered result types allow a common-mode certificate in inferred mode. -/
  | recover : TypeRecovery Step σ a A → TypeRecovery Step τ b B →
      CheckedCompare Step σ τ false A B → CheckedCompare Step σ τ true a b →
      CheckedCompare Step σ τ mode a b
  | compute : Compute Step a a' → Compute Step b b' → CheckedCompare Step σ τ mode a' b' →
      CheckedCompare Step σ τ mode a b

end ProofShape

/-- Both checking and inference descend. Common lambda types provide domain
alignment; recovered types justify the mode switch without strengthening. -/
theorem proofErase_checked_compare_descend (hstep : ErasedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ')
    (hσ : ErasedOracleTyping Γ σ n k) (hτ : ErasedOracleTyping Γ τ n k)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ProofShape.CheckedCompare Step σ τ mode
      ((proofErase Γ a).liftN n k) ((proofErase Γ b).liftN n k)) :
    (env.IsDefEqU univs Γ A B → env.IsDefEqU univs Γ a b) ∧
    (mode = false → ¬ IsProof Γ a → env.IsDefEqU univs Γ a b) := by
  generalize Ea : (proofErase Γ a).liftN n k = sa at H
  generalize Eb : (proofErase Γ b).liftN n k = sb at H
  induction H generalizing Γ Γ' k a b A B with
  | base H =>
    exact proofErase_recovered_compare_descend hstep hΓ hΓ' W hσ hτ ha hb (by simpa only [Ea, Eb] using H)
  | app Hf Hx ihf ihx =>
    obtain ⟨_, _, haE, Eaf, Eax⟩ := ProofShape.liftN_app_inv Ea
    obtain ⟨_, _, hbE, Ebf, Ebx⟩ := ProofShape.liftN_app_inv Eb
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
    obtain ⟨_, haE, Eam⟩ := ProofShape.liftN_proj_inv Ea
    obtain ⟨_, hbE, Ebm⟩ := ProofShape.liftN_proj_inv Eb
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
    have HDU := (ihD hΓ hΓ' W hσ hτ hD hD' EaD EbD).2 rfl (not_isProof_of_sort hΓ hD)
    have HDD := HDU.of_l henv hΓ hD
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have hΓD' : OnCtx (D.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', u, hD.weakN henv W⟩
    have hctx := IsDefEqCtx.succ .zero HDD.symm
    have Ectx := proofErase_defeqCtx (Γ₁ := D' :: Γ) ⟨hΓ, _, hD'⟩ hctx hbody'
    rw [Ectx] at Ebb
    have hbody'' := hbody'.defeqDFC henv hctx
    have HI := ihbody hΓD hΓD' W.succ
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
    have HDU := (ihD hΓ hΓ' W hσ hτ hD hD' EaD EbD).2 rfl (not_isProof_of_sort hΓ hD)
    have HDD := HDU.of_l henv hΓ hD
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have hΓD' : OnCtx (D.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', u, hD.weakN henv W⟩
    have hctx := IsDefEqCtx.succ .zero HDD.symm
    have Ectx := proofErase_defeqCtx (Γ₁ := D' :: Γ) ⟨hΓ, _, hD'⟩ hctx hC'
    rw [Ectx] at EbC
    have HCU := (ihC hΓD hΓD' W.succ
      (EaD ▸ hσ.cons hΓ hD) (EbD ▸ hτ.cons_convert hΓ hD hD' HDU) hC (hC'.defeqDFC henv hctx) EaC EbC).2 rfl
      (not_isProof_of_sort hΓD hC)
    have HH : env.IsDefEqU univs Γ _ _ := ⟨_, IsDefEq.forallEDF HDD (HCU.of_l henv hΓD hC)⟩
    exact ⟨fun _ => HH, fun _ _ => HH⟩
  | etaL HR HD HE ihD =>
    obtain ⟨_, _, Es, EA, Ebody⟩ := ProofShape.liftN_lam_inv Ea
    obtain ⟨D, body, rfl, _, ED, _⟩ := erase_lam_inv Es
    rw [← ED] at EA
    obtain ⟨D', C', hfPi, ED', _⟩ := proofErase_recovered_pi_descend_of_oracleTyping
      hstep hΓ hΓ' W hτ hb (Eb ▸ HR)
    obtain ⟨⟨_, hD⟩, _, _⟩ := ha.lam_inv henv hΓ
    obtain ⟨⟨_, hD'⟩, _⟩ := (hfPi.isType henv hΓ).forallE_inv henv
    have HDD := (ihD hΓ hΓ' W hσ hτ hD hD' EA ED').2 rfl (not_isProof_of_sort hΓ hD)
    have HE' : ProofShape.EtaHead ((proofErase Γ (.lam D body)).liftN n k)
        ((proofErase Γ b).liftN n k) := by simpa only [Ea, Eb] using HE
    have HH := proofErase_eta_head_infer hΓ ha hfPi HDD HE'.of_liftN
    exact ⟨fun _ => HH, fun _ _ => HH⟩
  | etaR HR HD HE ihD =>
    obtain ⟨_, _, Es, EB, Ebody⟩ := ProofShape.liftN_lam_inv Eb
    obtain ⟨D, body, rfl, _, ED, _⟩ := erase_lam_inv Es
    rw [← ED] at EB
    obtain ⟨D', C', hfPi, ED', _⟩ := proofErase_recovered_pi_descend_of_oracleTyping
      hstep hΓ hΓ' W hσ ha (Ea ▸ HR)
    obtain ⟨⟨_, hD⟩, _, _⟩ := hb.lam_inv henv hΓ
    obtain ⟨⟨_, hD'⟩, _⟩ := (hfPi.isType henv hΓ).forallE_inv henv
    have HDD := (ihD hΓ hΓ' W hσ hτ hD' hD ED' EB).2 rfl (not_isProof_of_sort hΓ hD')
    have HE' : ProofShape.EtaHead ((proofErase Γ (.lam D body)).liftN n k)
        ((proofErase Γ a).liftN n k) := by simpa only [Ea, Eb] using HE
    have HH := (proofErase_eta_head_infer hΓ hb hfPi HDD.symm HE'.of_liftN).symm
    exact ⟨fun _ => HH, fun _ _ => HH⟩
  | lamCommon Hbody ihbody =>
    constructor
    · intro hAB
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
      have HPi := ((ha.uniqU henv hΓ (HasType.lam hD hbody)).symm.trans henv hΓ hAB).trans
        henv hΓ (hb.uniqU henv hΓ (HasType.lam hD' hbody'))
      obtain ⟨⟨_, HDD⟩, _, hCC⟩ := HPi.forallE_inv henv hΓ
      have HDU : env.IsDefEqU univs Γ D D' := ⟨_, HDD⟩
      have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
      have hΓD' : OnCtx (D.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', u, hD.weakN henv W⟩
      have hctx := IsDefEqCtx.succ .zero HDD.symm
      have Ectx := proofErase_defeqCtx (Γ₁ := D' :: Γ) ⟨hΓ, _, hD'⟩ hctx hbody'
      rw [Ectx] at Ebb
      have hbody'' := hbody'.defeqDFC henv hctx
      have HI := ihbody hΓD hΓD' W.succ
        (EaD ▸ hσ.cons hΓ hD) (EbD ▸ hτ.cons_convert hΓ hD hD' HDU) hbody hbody'' Eab Ebb
      exact ⟨_, IsDefEq.lamDF (HDU.of_l henv hΓ hD) ((HI.1 ⟨_, hCC⟩).of_l henv hΓD hbody)⟩
    · intro hmode; cases hmode
  | recover RA RB HT HC ihT ihC =>
    obtain ⟨TA, haT, ETA⟩ := proofErase_typeRecovery_descend_of_oracleTyping
      hstep hΓ hΓ' W hσ ha (Ea ▸ RA)
    obtain ⟨TB, hbT, ETB⟩ := proofErase_typeRecovery_descend_of_oracleTyping
      hstep hΓ hΓ' W hτ hb (Eb ▸ RB)
    obtain ⟨_, hTA⟩ := haT.isType henv hΓ
    obtain ⟨_, hTB⟩ := hbT.isType henv hΓ
    have HTT := (ihT hΓ hΓ' W hσ hτ hTA hTB ETA ETB).2 rfl (not_isProof_of_sort hΓ hTA)
    have HH := (ihC hΓ hΓ' W hσ hτ haT hbT Ea Eb).1 HTT
    exact ⟨fun _ => HH, fun _ _ => HH⟩
  | compute Ra Rb HC ih =>
    rw [← Ea] at Ra
    rw [← Eb] at Rb
    obtain ⟨a', HA, EA⟩ := proofErase_compute_typed_descend hstep hΓ hΓ' W ha Ra
    obtain ⟨b', HB, EB⟩ := proofErase_compute_typed_descend hstep hΓ hΓ' W hb Rb
    have HI := ih hΓ hΓ' W hσ hτ HA.hasType.2 HB.hasType.2 EA EB
    have finish (HH : env.IsDefEqU univs Γ a' b') : env.IsDefEqU univs Γ a b :=
      ((show env.IsDefEqU univs Γ a a' from ⟨_, HA⟩).trans henv hΓ HH).trans henv hΓ ⟨_, HB.symm⟩
    exact ⟨fun hAB => finish (HI.1 hAB),
      fun hmode hn => finish (HI.2 hmode (mt (isProof_congr hΓ HA).2 hn))⟩

/-- The canonical context oracles instantiate checked comparison at a finite
computational stage. This is a certificate relation, with coverage still open. -/
def ErasedCheckedComparison (D : PureObservation.Definitions) (stage : Nat) (mode : Bool)
    (Γ : List VExpr) (a b : VExpr) : Prop :=
  ProofShape.CheckedCompare (ErasedComparedKStage D stage)
    (erasedTypeOracle Γ) (erasedTypeOracle Γ) mode (proofErase Γ a) (proofErase Γ b)

/-- Checked comparison descends through a block insertion with the same common
or inferred endpoint-typing premises as its predecessor. -/
theorem ErasedCheckedComparison.descendN (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n k Γ Γ')
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ErasedCheckedComparison D stage mode Γ' (a.liftN n k) (b.liftN n k)) :
    (env.IsDefEqU univs Γ A B → env.IsDefEqU univs Γ a b) ∧
    (mode = false → ¬ IsProof Γ a → env.IsDefEqU univs Γ a b) := by
  unfold ErasedCheckedComparison at H
  rw [proofErase_liftN hΓ hΓ' W ha, proofErase_liftN hΓ hΓ' W hb] at H
  have hσ : ErasedOracleTyping Γ (erasedTypeOracle Γ') n k :=
    ErasedOracleAbove.typing (ErasedOracleValid.above (erasedTypeOracle_valid hΓ') hΓ hΓ' W)
  exact proofErase_checked_compare_descend (erased_compared_K_stage_descent heq hs stage)
    hΓ hΓ' W hσ hσ ha hb H

end Lean4Lean.VEnv.Strengthening
