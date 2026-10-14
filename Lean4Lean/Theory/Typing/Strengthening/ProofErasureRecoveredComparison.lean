import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveryEta

/-! # Compatible erased comparison with recovered inferred eta

Each endpoint carries its own erased variable-type oracle. Beneath binders the
oracles retain the respective annotations, while typed oracle agreement permits
replay in one common original context. The previous context-free comparison is
included, and recovered head eta may now occur at every compatible position.
Transitivity and completeness are not assumed.
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
/-- Compatible two-mode comparison, with a separate type oracle for each side.
The inferred eta cases compare recovered domains recursively in this relation. -/
inductive RecoveredCompare (Step : ProofShape → ProofShape → Prop) :
    TypeOracle → TypeOracle → Bool → ProofShape → ProofShape → Prop where
  | base : Compare Step mode a b → RecoveredCompare Step σ τ mode a b
  | app : RecoveredCompare Step σ τ false f f' → RecoveredCompare Step σ τ true a a' →
      RecoveredCompare Step σ τ mode (.app f a) (.app f' a')
  | proj : RecoveredCompare Step σ τ false m m' → RecoveredCompare Step σ τ mode (.proj s i m) (.proj s i m')
  | lam : RecoveredCompare Step σ τ false A A' →
      RecoveredCompare Step (σ.cons A) (τ.cons A') mode b b' →
      RecoveredCompare Step σ τ mode (.lam A b) (.lam A' b')
  | forallE : RecoveredCompare Step σ τ false A A' →
      RecoveredCompare Step (σ.cons A) (τ.cons A') false B B' →
      RecoveredCompare Step σ τ mode (.forallE A B) (.forallE A' B')
  | etaL : TypeRecovery Step τ f (.forallE D C) → RecoveredCompare Step σ τ false A D →
      EtaHead (.lam A b) f → RecoveredCompare Step σ τ mode (.lam A b) f
  | etaR : TypeRecovery Step σ f (.forallE D C) → RecoveredCompare Step σ τ false D A →
      EtaHead (.lam A b) f → RecoveredCompare Step σ τ mode f (.lam A b)
  | compute : Compute Step a a' → Compute Step b b' → RecoveredCompare Step σ τ mode a' b' →
      RecoveredCompare Step σ τ mode a b

/-- Symmetry exchanges the endpoint oracles, including their binder annotations. -/
theorem RecoveredCompare.symm (H : RecoveredCompare Step σ τ mode a b) :
    RecoveredCompare Step τ σ mode b a := by
  induction H with
  | base H => exact .base H.symm
  | app _ _ ihf iha => exact .app ihf iha
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | etaL HR _ HE ih => exact .etaR HR ih HE
  | etaR HR _ HE ih => exact .etaL HR ih HE
  | compute Ra Rb _ ih => exact .compute Rb Ra ih

/-- An inferred certificate can be used in common-type mode. -/
theorem RecoveredCompare.common (H : RecoveredCompare Step σ τ mode a b) :
    RecoveredCompare Step σ τ true a b := by
  induction H with
  | base H => exact .base H.common
  | app Hf Ha => exact .app Hf Ha
  | proj H => exact .proj H
  | lam HA _ _ ihb => exact .lam HA ihb
  | forallE HA HB => exact .forallE HA HB
  | etaL HR HD HE => exact .etaL HR HD HE
  | etaR HR HD HE => exact .etaR HR HD HE
  | compute Ra Rb _ ih => exact .compute Ra Rb ih

/-- Earlier recovered head eta embeds in the compatible relation. -/
theorem RecoveredEtaHead.compare (H : RecoveredEtaHead Step σ a b) :
    RecoveredCompare Step σ σ mode a b := by
  cases H with
  | intro HR HD HE => exact .etaL HR (.base HD) HE
end ProofShape

/-- Compatible recovered comparison descends in both modes. Independent typed
oracle representatives allow the two binder annotations to remain distinct.
Every computation and recovered function type is reconstructed below. -/
theorem proofErase_recovered_compare_descend (hstep : ErasedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ')
    (hσ : ErasedOracleTyping Γ σ n k) (hτ : ErasedOracleTyping Γ τ n k)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ProofShape.RecoveredCompare Step σ τ mode
      ((proofErase Γ a).liftN n k) ((proofErase Γ b).liftN n k)) :
    (env.IsDefEqU univs Γ A B → env.IsDefEqU univs Γ a b) ∧
    (mode = false → ¬ IsProof Γ a → env.IsDefEqU univs Γ a b) := by
  generalize Ea : (proofErase Γ a).liftN n k = sa at H
  generalize Eb : (proofErase Γ b).liftN n k = sb at H
  induction H generalizing Γ Γ' k a b A B with
  | base H =>
    exact proofErase_compare_descend hstep hΓ hΓ' W ha hb (by simpa only [Ea, Eb] using H)
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

/-- The canonical context oracle gives a concrete recovered comparison at a
finite K stage. All prior context-free certificates remain valid. -/
def ErasedRecoveredComparison (D : PureObservation.Definitions) (stage : Nat) (mode : Bool)
    (Γ : List VExpr) (a b : VExpr) : Prop :=
  ProofShape.RecoveredCompare (ErasedComparedKStage D stage)
    (erasedTypeOracle Γ) (erasedTypeOracle Γ) mode (proofErase Γ a) (proofErase Γ b)

/-- Concrete recovered comparison descends through arbitrary block insertion
with the same two endpoint-typing modes as the earlier raw comparison. -/
theorem ErasedRecoveredComparison.descendN (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n k Γ Γ')
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ErasedRecoveredComparison D stage mode Γ' (a.liftN n k) (b.liftN n k)) :
    (env.IsDefEqU univs Γ A B → env.IsDefEqU univs Γ a b) ∧
    (mode = false → ¬ IsProof Γ a → env.IsDefEqU univs Γ a b) := by
  unfold ErasedRecoveredComparison at H
  rw [proofErase_liftN hΓ hΓ' W ha, proofErase_liftN hΓ hΓ' W hb] at H
  have hσ : ErasedOracleTyping Γ (erasedTypeOracle Γ') n k :=
    ErasedOracleAbove.typing (ErasedOracleValid.above (erasedTypeOracle_valid hΓ') hΓ hΓ' W)
  exact proofErase_recovered_compare_descend (erased_compared_K_stage_descent heq hs stage)
    hΓ hΓ' W hσ hσ ha hb H

/-- Common-typed endpoints need no non-proof premise in recovered descent. -/
theorem ErasedRecoveredComparison.common_descendN (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n k Γ Γ')
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b T)
    (H : ErasedRecoveredComparison D stage true Γ' (a.liftN n k) (b.liftN n k)) :
    env.IsDefEq univs Γ a b T := by
  obtain ⟨_, hT⟩ := ha.isType henv hΓ
  exact ((H.descendN heq hs hΓ hΓ' W ha hb).1 ⟨_, hT⟩).of_l henv hΓ ha

end Lean4Lean.VEnv.Strengthening
