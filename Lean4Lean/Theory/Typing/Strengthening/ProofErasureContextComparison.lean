import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRawChecking
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContext

/-! # Checked erased comparison with contextual sort witnesses

Both endpoints use one erased context. Binder bodies are checked in the left
binder context, after endpoint typing aligns the original domains. Recursive
eta uses a contextual domain-sort witness, with no computational recovery of
that sort. The oracle-free base permits raw substitution of its certificates.
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
/-- Computation-aware checking with one ambient erased context. Symmetry is an
explicit finite rule; inference is replayed at independently typed non-proofs.
No transitive intermediate witness or declarative completeness is assumed. -/
inductive ContextCompare (Step : ProofShape → ProofShape → Prop) :
    List ProofShape → Bool → ProofShape → ProofShape → Prop where
  | base : RawCheckedCompare Step mode a b → ContextCompare Step Δ mode a b
  | app : ContextCompare Step Δ false f f' → ContextCompare Step Δ true a a' →
      ContextCompare Step Δ mode (.app f a) (.app f' a')
  | proj : ContextCompare Step Δ false m m' →
      ContextCompare Step Δ mode (.proj s i m) (.proj s i m')
  | lam : ContextCompare Step Δ false A A' → ContextCompare Step (A :: Δ) mode b b' →
      ContextCompare Step Δ mode (.lam A b) (.lam A' b')
  | forallE : ContextCompare Step Δ false A A' → ContextCompare Step (A :: Δ) false B B' →
      ContextCompare Step Δ mode (.forallE A B) (.forallE A' B')
  /-- Equal witnessed sorts align independently supplied domain typings. -/
  | lamSorted : DomainSort Δ A u → DomainSort Δ A' u → ContextCompare Step Δ true A A' →
      ContextCompare Step (A :: Δ) mode b b' →
      ContextCompare Step Δ mode (.lam A b) (.lam A' b')
  /-- Pi domains and codomains are types, so shared witnessed sorts suffice
  for common-mode recursive comparison at both positions. -/
  | forallSorted : DomainSort Δ A u → DomainSort Δ A' u → ContextCompare Step Δ true A A' →
      DomainSort (A :: Δ) B v → DomainSort (A :: Δ) B' v →
      ContextCompare Step (A :: Δ) true B B' →
      ContextCompare Step Δ mode (.forallE A B) (.forallE A' B')
  | lamCommon : ContextCompare Step (A :: Δ) true b b' →
      ContextCompare Step Δ true (.lam A b) (.lam A' b')
  | etaBodyL : DomainSort Δ A u →
      ContextCompare Step (A :: Δ) true b (.app (f.liftN 1) (etaArgument u)) →
      ContextCompare Step Δ true (.lam A b) f
  | etaBodyR : DomainSort Δ A u →
      ContextCompare Step (A :: Δ) true (.app (f.liftN 1) (etaArgument u)) b →
      ContextCompare Step Δ true f (.lam A b)
  | compute : Compute Step a a' → Compute Step b b' → ContextCompare Step Δ mode a' b' →
      ContextCompare Step Δ mode a b
  | symm : ContextCompare Step Δ mode a b → ContextCompare Step Δ mode b a
end ProofShape

/-- Contextual comparison descends. Common endpoint types justify checking;
inference accepts independently typed non-proofs on both sides. Ambient sort
witnesses are reinterpreted below through erased-context conversion. -/
theorem proofErase_context_compare_descend (hstep : ErasedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (hΔ : proofEraseCtx Γ' = Δ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ProofShape.ContextCompare Step Δ mode
      ((proofErase Γ a).liftN n k) ((proofErase Γ b).liftN n k)) :
    (env.IsDefEqU univs Γ A B → env.IsDefEqU univs Γ a b) ∧
    (mode = false → ¬ IsProof Γ a → ¬ IsProof Γ b → env.IsDefEqU univs Γ a b) := by
  generalize Ea : (proofErase Γ a).liftN n k = sa at H
  generalize Eb : (proofErase Γ b).liftN n k = sb at H
  induction H generalizing Γ Γ' k a b A B with
  | base H =>
    have HI := proofErase_rawChecked_compare_descend hstep hΓ hΓ' W ha hb
      (by simpa only [Ea, Eb] using H)
    exact ⟨HI.1, fun hm hn _ => HI.2 hm hn⟩
  | app Hf Hx ihf ihx =>
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
  | lamSorted SA SA' HD Hbody ihD ihbody =>
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
    have hD := ProofShape.DomainSort.descend (by simpa only [hΔ, EaD] using SA) hΓ hΓ' W hD
    have hD' := ProofShape.DomainSort.descend (by simpa only [hΔ, EbD] using SA') hΓ hΓ' W hD'
    have HDU := (ihD hΓ hΓ' W hΔ hD hD' EaD EbD).1 ⟨_, HasType.sort (hD.sort_r henv hΓ)⟩
    have HDD := HDU.of_l henv hΓ hD
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, hD⟩
    have hΓD' : OnCtx (D.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', _, hD.weakN henv W⟩
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
  | forallSorted SA SA' HD SB SB' HC ihD ihC =>
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
    have hD := ProofShape.DomainSort.descend (by simpa only [hΔ, EaD] using SA) hΓ hΓ' W hD
    have hD' := ProofShape.DomainSort.descend (by simpa only [hΔ, EbD] using SA') hΓ hΓ' W hD'
    have HDU := (ihD hΓ hΓ' W hΔ hD hD' EaD EbD).1 ⟨_, HasType.sort (hD.sort_r henv hΓ)⟩
    have HDD := HDU.of_l henv hΓ hD
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, hD⟩
    have hΓD' : OnCtx (D.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', _, hD.weakN henv W⟩
    have hctx := IsDefEqCtx.succ .zero HDD.symm
    have Ectx := proofErase_defeqCtx (Γ₁ := D' :: Γ) ⟨hΓ, _, hD'⟩ hctx hC'
    rw [Ectx] at EbC
    have hctxE := congr (congrArg List.cons ((proofErase_liftN hΓ hΓ' W hD).trans EaD)) hΔ
    change proofEraseCtx (D.liftN n k :: Γ') = _ at hctxE
    have hC := ProofShape.DomainSort.descend
      (by simpa only [hctxE, EaC] using SB) hΓD hΓD' W.succ hC
    have hC' := ProofShape.DomainSort.descend
      (by simpa only [hctxE, EbC] using SB') hΓD hΓD' W.succ (hC'.defeqDFC henv hctx)
    have HCU := (ihC hΓD hΓD' W.succ hctxE
      hC hC' EaC EbC).1 ⟨_, HasType.sort (hC.sort_r henv hΓD)⟩
    have HH : env.IsDefEqU univs Γ _ _ := ⟨_, IsDefEq.forallEDF HDD (HCU.of_l henv hΓD hC)⟩
    exact ⟨fun _ => HH, fun _ _ _ => HH⟩
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
        (by simp only [proofEraseCtx, proofErase_liftN hΓ hΓ' W hD, hΔ, EaD])
        hbody hbody'' Eab Ebb
      exact ⟨_, IsDefEq.lamDF (HDU.of_l henv hΓ hD) ((HI.1 ⟨_, hCC⟩).of_l henv hΓD hbody)⟩
    · intro hmode; cases hmode
  | etaBodyL HR Hbody ihbody =>
    constructor
    · intro hAB
      obtain ⟨_, _, Elam, ED, Ebody⟩ := ProofShape.liftN_lam_inv Ea
      obtain ⟨D, body, rfl, hn, ED', Ebody'⟩ := erase_lam_inv Elam
      rw [← ED'] at ED
      rw [← Ebody'] at Ebody
      obtain ⟨⟨_, hD₀⟩, C, hbody⟩ := ha.lam_inv henv hΓ
      have hD := ProofShape.DomainSort.descend (by simpa only [hΔ, ED] using HR) hΓ hΓ' W hD₀
      have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, hD⟩
      have hΓD' : OnCtx (D.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', _, hD.weakN henv W⟩
      have hfPi : env.HasType univs Γ b (.forallE D C) :=
        hb.defeqU_r henv hΓ (hAB.symm.trans henv hΓ (ha.uniqU henv hΓ (HasType.lam hD hbody)))
      have hnf : ¬ IsProof Γ b := by
        rintro ⟨P, hfP, hP⟩
        exact hn ⟨P, ha.defeqU_r henv hΓ (hAB.trans henv hΓ (hb.uniqU henv hΓ hfP)), hP⟩
      have hηbody : env.HasType univs (D :: Γ) (.app b.lift (.bvar 0)) C := by
        have H := HasType.app (hfPi.weak henv (B := D)) (.bvar .zero)
        simpa only [lift, liftN, inst_liftN_bvar] using H
      have Eη := proofErase_eta_body_liftN (n := n) (k := k) hΓ hD hfPi hnf
      rw [Eb] at Eη
      have HI := (ihbody hΓD hΓD' W.succ
        (by simp only [proofEraseCtx, proofErase_liftN hΓ hΓ' W hD, hΔ, ED])
        hbody hηbody Ebody Eη).1 ⟨_, hηbody.isType henv hΓD |>.choose_spec⟩
      have HH : env.IsDefEqU univs Γ (.lam D body) b :=
        ⟨_, (IsDefEq.lamDF hD (HI.of_l henv hΓD hbody)).trans (IsDefEq.eta hfPi)⟩
      exact HH
    · intro hmode; cases hmode
  | etaBodyR HR Hbody ihbody =>
    constructor
    · intro hAB
      obtain ⟨_, _, Elam, ED, Ebody⟩ := ProofShape.liftN_lam_inv Eb
      obtain ⟨D, body, rfl, hn, ED', Ebody'⟩ := erase_lam_inv Elam
      rw [← ED'] at ED
      rw [← Ebody'] at Ebody
      obtain ⟨⟨_, hD₀⟩, C, hbody⟩ := hb.lam_inv henv hΓ
      have hD := ProofShape.DomainSort.descend (by simpa only [hΔ, ED] using HR) hΓ hΓ' W hD₀
      have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, hD⟩
      have hΓD' : OnCtx (D.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', _, hD.weakN henv W⟩
      have hfPi : env.HasType univs Γ a (.forallE D C) :=
        ha.defeqU_r henv hΓ (hAB.trans henv hΓ (hb.uniqU henv hΓ (HasType.lam hD hbody)))
      have hnf : ¬ IsProof Γ a := by
        rintro ⟨P, hfP, hP⟩
        exact hn ⟨P, hb.defeqU_r henv hΓ (hAB.symm.trans henv hΓ (ha.uniqU henv hΓ hfP)), hP⟩
      have hηbody : env.HasType univs (D :: Γ) (.app a.lift (.bvar 0)) C := by
        have H := HasType.app (hfPi.weak henv (B := D)) (.bvar .zero)
        simpa only [lift, liftN, inst_liftN_bvar] using H
      have Eη := proofErase_eta_body_liftN (n := n) (k := k) hΓ hD hfPi hnf
      rw [Ea] at Eη
      have HI := (ihbody hΓD hΓD' W.succ
        (by simp only [proofEraseCtx, proofErase_liftN hΓ hΓ' W hD, hΔ, ED])
        hηbody hbody Eη Ebody).1 ⟨_, hηbody.isType henv hΓD |>.choose_spec⟩
      have HH : env.IsDefEqU univs Γ (.lam D body) a :=
        ⟨_, (IsDefEq.lamDF hD (HI.symm.of_l henv hΓD hbody)).trans (IsDefEq.eta hfPi)⟩
      exact HH.symm
    · intro hmode; cases hmode
  | compute Ra Rb HC ih =>
    rw [← Ea] at Ra
    rw [← Eb] at Rb
    obtain ⟨a', HA, EA⟩ := proofErase_compute_typed_descend hstep hΓ hΓ' W ha Ra
    obtain ⟨b', HB, EB⟩ := proofErase_compute_typed_descend hstep hΓ hΓ' W hb Rb
    have HI := ih hΓ hΓ' W hΔ HA.hasType.2 HB.hasType.2 EA EB
    have finish (HH : env.IsDefEqU univs Γ a' b') : env.IsDefEqU univs Γ a b :=
      ((show env.IsDefEqU univs Γ a a' from ⟨_, HA⟩).trans henv hΓ HH).trans henv hΓ ⟨_, HB.symm⟩
    exact ⟨fun hAB => finish (HI.1 hAB),
      fun hmode hn hn' => finish (HI.2 hmode (mt (isProof_congr hΓ HA).2 hn)
        (mt (isProof_congr hΓ HB).2 hn'))⟩

  | symm HC ih =>
    have HI := ih hΓ hΓ' W hΔ hb ha Eb Ea
    exact ⟨fun hAB => (HI.1 hAB.symm).symm, fun hm hn hn' => (HI.2 hm hn' hn).symm⟩

end Lean4Lean.VEnv.Strengthening
