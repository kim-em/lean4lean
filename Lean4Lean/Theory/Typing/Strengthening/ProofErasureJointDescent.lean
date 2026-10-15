import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointChecking

/-! # Simultaneous descent of comparison and carrier checking

One structural induction covers every alternation between inferred/common
comparison and explicit-carrier checking. Each recursive use retains its
actual upper context and lower source typings.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private ProofShape.liftN_app_inv ProofShape.liftN_proj_inv ProofShape.liftN_lam_inv
  ProofShape.liftN_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]



private def JointDescent (n : Nat) (Δ : List ProofShape)
    (kind : ProofShape.JointCheckKind) (sa sb : ProofShape) : Prop :=
  match kind with
  | .compare mode => ∀ {Γ Γ' k a b A B},
      OnCtx Γ (env.IsType univs) → OnCtx Γ' (env.IsType univs) →
      Ctx.LiftN n k Γ Γ' → proofEraseCtx Γ' = Δ →
      env.HasType univs Γ a A → env.HasType univs Γ b B →
      (proofErase Γ a).liftN n k = sa → (proofErase Γ b).liftN n k = sb →
      (env.IsDefEqU univs Γ A B → env.IsDefEqU univs Γ a b) ∧
      (mode = false → ¬ IsProof Γ a → ¬ IsProof Γ b → env.IsDefEqU univs Γ a b)
  | .carrier α => ∀ {Γ Γ' k A a b},
      OnCtx Γ (env.IsType univs) → OnCtx Γ' (env.IsType univs) →
      Ctx.LiftN n k Γ Γ' → env.HasType univs Γ a A → env.HasType univs Γ b A →
      proofEraseCtx Γ' = Δ → (proofErase Γ A).liftN n k = α →
      (proofErase Γ a).liftN n k = sa → (proofErase Γ b).liftN n k = sb →
      env.IsDefEqU univs Γ a b

private theorem joint_check_descent (hstep : ErasedScopedPrimitiveDescent Step)
    (H : ProofShape.JointCheck Step Δ kind sa sb) : JointDescent n Δ kind sa sb := by
  induction H with
  | leaf H =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    exact proofErase_context_compare_descend (Step := fun _ _ => False) (by intro Γ Γ' n k e T out hΓ hΓ' W ht H; exact H.elim)
      hΓ hΓ' W hΔ ha hb (by simpa only [Ea, Eb] using H.context)
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
  | appCarrier R HF HX ihf ihx =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    obtain ⟨_, _, Eaa, Eaf, Eax⟩ := ProofShape.liftN_app_inv Ea
    obtain ⟨_, _, Ebb, Ebg, Eby⟩ := ProofShape.liftN_app_inv Eb
    obtain ⟨f, x, rfl, hna, Ef, Ex⟩ := erase_app_inv Eaa
    obtain ⟨g, y, rfl, hnb, Eg, Ey⟩ := erase_app_inv Ebb
    rw [← Ef] at Eaf
    rw [← Ex] at Eax
    rw [← Eg] at Ebg
    rw [← Ey] at Eby
    obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
    obtain ⟨_, _, hg, hy⟩ := hb.app_inv henv hΓ
    rw [← Eaf, ← hΔ] at R
    obtain ⟨D, C, hfPi, ED, EC⟩ := proofErase_scoped_recovered_pi_descend hstep hΓ hΓ' W hf R
    have Hfg := (ihf hΓ hΓ' W hΔ hf hg Eaf Ebg).2 rfl
      (not_isProof_fn hΓ hf hx hna) (not_isProof_fn hΓ hg hy hnb)
    have HfgPi := Hfg.of_l henv hΓ hfPi
    have hxD := argument_at_displayed_domain hΓ hf hfPi hx
    have hyD := argument_at_displayed_domain hΓ hg HfgPi.hasType.2 hy
    have Hxy := ihx hΓ hΓ' W hxD hyD hΔ ED Eax Eby
    have HH : env.IsDefEqU univs Γ (.app f x) (.app g y) :=
      ⟨_, IsDefEq.appDF HfgPi (Hxy.of_l henv hΓ hxD)⟩
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
  | lamSorted SA SA' HD Hbody ihD ihbody =>
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
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
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
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
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
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
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
  | @structFields Δ family info ls ps fields major hi hx hp hf hadm Hfields ihfields =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    constructor
    · intro hAB
      apply Exists.intro _
      apply proofErase_structure_fields_reflect hΓ ha (hb.defeqU_r henv hΓ hAB.symm)
        hi hx hp hf hadm Ea
      intro i hj x X hxt hpt Ex
      by_cases hpx : IsProof Γ x
      · exact proofErase_structure_field hΓ hb hxt hpt (.inl (proofErase_eq_proof.2 hpx))
      have hnp : ¬ IsProof Γ (.proj family i b) := by
        rintro ⟨P, hpP, hP⟩
        exact hpx ⟨P, hxt.defeqU_r henv hΓ (hpt.uniqU henv hΓ hpP), hP⟩
      have hnraw : fields[i] ≠ ProofShape.proof := by
        intro H
        apply hpx
        apply proofErase_eq_proof.1
        exact ProofShape.liftN_inj.1 (Ex.trans H)
      have Eproj : (proofErase Γ (.proj family i b)).liftN n k = .proj family i major := by
        rw [show proofErase Γ (.proj family i b) = .proj family i (proofErase Γ b) from if_neg hnp]
        simp only [ProofShape.liftN, Eb]
      exact (ihfields i hj hnraw hΓ hΓ' W hΔ hxt hpt Ex Eproj).1
        ⟨_, hxt.isType henv hΓ |>.choose_spec⟩
    · intro hm; cases hm
  | etaLams HD Hη ihD =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    rw [← Ea, ← Eb] at Hη
    obtain ⟨_, _, haE, EaD, _⟩ := ProofShape.liftN_lam_inv Ea
    obtain ⟨_, _, hbE, EbD, _⟩ := ProofShape.liftN_lam_inv Eb
    obtain ⟨D, body, rfl, _, ED, _⟩ := erase_lam_inv haE
    obtain ⟨D', body', rfl, _, ED', _⟩ := erase_lam_inv hbE
    rw [← ED] at EaD
    rw [← ED'] at EbD
    obtain ⟨⟨_, hD⟩, _, hbody⟩ := ha.lam_inv henv hΓ
    obtain ⟨⟨_, hD'⟩, _, hbody'⟩ := hb.lam_inv henv hΓ
    have HDD := (ihD hΓ hΓ' W hΔ hD hD' EaD EbD).2 rfl (not_isProof_of_sort hΓ hD) (not_isProof_of_sort hΓ hD')
    have HH : env.IsDefEqU univs Γ (.lam D body) (.lam D' body') := by
      rcases Hη with Hη | Hη
      · exact proofErase_eta_head_infer hΓ ha (HasType.lam hD' hbody') HDD Hη.of_liftN
      · exact (proofErase_eta_head_infer hΓ hb (HasType.lam hD hbody) HDD.symm Hη.of_liftN).symm
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


  | carrierChecked HC ih =>
    intro Γ Γ' k A a b hΓ hΓ' W ha hb EΔ Eα Ea Eb
    obtain ⟨_, hA⟩ := ha.isType henv hΓ
    exact (ih hΓ hΓ' W EΔ ha hb Ea Eb).1 (.refl ⟨_, hA⟩)
  | carrierSubsingleton H =>
    intro Γ Γ' k A a b hΓ hΓ' W ha hb EΔ Eα Ea Eb
    rw [← Eα] at H
    exact ⟨_, proofErase_subsingleton_carrier_descend hΓ ha hb H⟩
  | carrierFunction S H ih =>
    intro Γ Γ' k A a b hΓ hΓ' W ha hb EΔ Eα Ea Eb
    obtain ⟨_, _, ET, ED, EB⟩ := ProofShape.liftN_forallE_inv Eα
    obtain ⟨D, B, rfl, _, ED', EB'⟩ := erase_forallE_inv ET
    rw [← ED'] at ED
    rw [← EB'] at EB
    obtain ⟨_, hT⟩ := ha.isType henv hΓ
    obtain ⟨⟨_, hD₀⟩, _, _⟩ := hT.forallE_inv henv
    have hD := ProofShape.DomainSort.descend (by simpa only [EΔ, ED] using S) hΓ hΓ' W hD₀
    by_cases hpa : IsProof Γ a
    · obtain ⟨P, haP, hP⟩ := hpa
      exact ⟨_, IsDefEq.proofIrrel hP haP (hb.defeqU_r henv hΓ (ha.uniqU henv hΓ haP))⟩
    have hpb : ¬ IsProof Γ b := by
      rintro ⟨P, hbP, hP⟩
      exact hpa ⟨P, ha.defeqU_r henv hΓ (hb.uniqU henv hΓ hbP), hP⟩
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, hD⟩
    have hΓD' : OnCtx (D.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', _, hD.weakN henv W⟩
    have hfa : env.HasType univs (D :: Γ) (.app a.lift (.bvar 0)) B := by
      simpa only [lift, liftN, inst_liftN_bvar] using HasType.app (ha.weak henv) (HasType.bvar .zero)
    have hfb : env.HasType univs (D :: Γ) (.app b.lift (.bvar 0)) B := by
      simpa only [lift, liftN, inst_liftN_bvar] using HasType.app (hb.weak henv) (HasType.bvar .zero)
    have Efa := proofErase_eta_body_liftN (n := n) (k := k) hΓ hD ha hpa
    have Efb := proofErase_eta_body_liftN (n := n) (k := k) hΓ hD hb hpb
    rw [Ea] at Efa
    rw [Eb] at Efb
    have HI := ih hΓD hΓD' W.succ hfa hfb
      (by simp only [proofEraseCtx, proofErase_liftN hΓ hΓ' W hD, EΔ, ED]) EB Efa Efb
    exact ⟨_, (IsDefEq.eta ha).symm.trans
      ((IsDefEq.lamDF hD (HI.of_l henv hΓD hfa)).trans (IsDefEq.eta hb))⟩
  | carrierSymm H ih =>
    intro Γ Γ' k A a b hΓ hΓ' W ha hb EΔ Eα Ea Eb
    exact (ih hΓ hΓ' W hb ha EΔ Eα Eb Ea).symm
  | carrierCompute R H ih =>
    intro Γ Γ' k A a b hΓ hΓ' W ha hb EΔ Eα Ea Eb
    rw [← Eα] at R
    obtain ⟨u, hA⟩ := ha.isType henv hΓ
    obtain ⟨A', HE, EA'⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ' W hA EΔ R
    exact ih hΓ hΓ' W (HE.defeq ha) (HE.defeq hb) EΔ EA' Ea Eb
  | carrierReduce Ra Rb H ih =>
    intro Γ Γ' k A a b hΓ hΓ' W ha hb EΔ Eα Ea Eb
    rw [← Ea] at Ra
    rw [← Eb] at Rb
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ' W ha EΔ Ra
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ' W hb EΔ Rb
    have HI := ih hΓ hΓ' W HA.hasType.2 HB.hasType.2 EΔ Eα EA EB
    exact ((show env.IsDefEqU univs Γ a a' from ⟨_, HA⟩).trans henv hΓ HI).trans henv hΓ ⟨_, HB.symm⟩
  | carrierIntro hi hx hp hadm Hfields ihfields =>
    intro Γ Γ' k A a b hΓ hΓ' W ha hb EΔ Eα Ea Eb
    rename_i family info ls Δ sa sb ps
    obtain ⟨rawArgs, Es, Eargs⟩ := ProofShape.liftN_const_spine_inv Eα
    obtain ⟨args, rfl, Eoriginal⟩ := proofErase_const_spine_inv Es
    have hlen : args.length = info.nparams := by
      have Hlen := congrArg List.length Eargs
      rw [Eoriginal] at Hlen
      simpa only [List.length_map, hp] using Hlen.symm
    have hexpa := (StructureReplay.expansion_typed_iff henv hΓ hi hlen hx ha).2 hadm
    apply structure_neutral_fields hΓ hi hlen hx hadm ha hb
    intro i hj T hia hib
    have proof_case (HP : IsProof Γ (.proj family i a)) : env.IsDefEqU univs Γ (.proj family i a) (.proj family i b) := by
      obtain ⟨P, hiaP, hP⟩ := HP
      have hibP := hib.defeqU_r henv hΓ (hia.uniqU henv hΓ hiaP)
      exact ⟨_, IsDefEq.proofIrrel hP hiaP hibP⟩
    by_cases HP : StructureReplay.ProofField env univs info ls i
    · exact proof_case (HP.projection hΓ hi hlen hexpa)
    by_cases hpa : IsProof Γ (.proj family i a)
    · exact proof_case hpa
    have hpb : ¬ IsProof Γ (.proj family i b) := by
      rintro ⟨P, hibP, hP⟩
      exact hpa ⟨P, hia.defeqU_r henv hΓ (hib.uniqU henv hΓ hibP), hP⟩
    have Epa : (proofErase Γ (.proj family i a)).liftN n k = .proj family i sa := by
      rw [show proofErase Γ (.proj family i a) = .proj family i (proofErase Γ a) from if_neg hpa]
      simp only [ProofShape.liftN, Ea]
    have Epb : (proofErase Γ (.proj family i b)).liftN n k = .proj family i sb := by
      rw [show proofErase Γ (.proj family i b) = .proj family i (proofErase Γ b) from if_neg hpb]
      simp only [ProofShape.liftN, Eb]
    obtain ⟨_, hT⟩ := hia.isType henv hΓ
    exact (ihfields i hj HP hΓ hΓ' W EΔ hia hib Epa Epb).1 (.refl ⟨_, hT⟩)
  | carrierNested hi hx hp hadm HT Hfields ihfields =>
    intro Γ Γ' k A a b hΓ hΓ' W ha hb EΔ Eα Ea Eb
    rename_i family info ls doms result Δ ps sa sb
    obtain ⟨rawArgs, Es, Eargs⟩ := ProofShape.liftN_const_spine_inv Eα
    obtain ⟨args, rfl, Eoriginal⟩ := proofErase_const_spine_inv Es
    rw [Eoriginal] at Eargs
    have hlen : args.length = info.nparams := by
      have Hlen := congrArg List.length Eargs
      simpa only [List.length_map, hp] using Hlen.symm
    have hexpa := (StructureReplay.expansion_typed_iff henv hΓ hi hlen hx ha).2 hadm
    apply structure_neutral_fields hΓ hi hlen hx hadm ha hb
    intro i hj T hia hib
    by_cases HP : StructureReplay.ProofField env univs info ls i
    · obtain ⟨P, hiaP, hP⟩ := HP.projection hΓ hi hlen hexpa
      exact ⟨_, IsDefEq.proofIrrel hP hiaP
        (hib.defeqU_r henv hΓ (hia.uniqU henv hΓ hiaP))⟩
    have hpa : ¬ IsProof Γ (.proj family i a) := fun H =>
      HP (StructureReplay.ProofField.of_projection hΓ hi hlen hj hexpa H)
    have hpb : ¬ IsProof Γ (.proj family i b) := by
      rintro ⟨P, hibP, hP⟩
      exact hpa ⟨P, hia.defeqU_r henv hΓ (hib.uniqU henv hΓ hibP), hP⟩
    obtain ⟨hj', F, hiaF, EF⟩ := proofErase_projection_at_recovered_family hΓ hi HT hia hpa ha
    have hibF := hib.defeqU_r henv hΓ (hia.uniqU henv hΓ hiaF)
    have EF' : proofErase Γ F = ProofShape.projectionType family info doms i hj'
        (args.map (proofErase Γ)) (proofErase Γ a) := by
      simpa only [ProofShape.projectionType, List.map_take] using EF
    have EFlift : (proofErase Γ F).liftN n k =
        ProofShape.projectionType family info doms i hj' ps sa := by
      rw [EF', ProofShape.projectionType_liftN HT hj' (by simp [hlen]), ← Eargs, Ea]
    have Epa : (proofErase Γ (.proj family i a)).liftN n k = .proj family i sa := by
      rw [show proofErase Γ (.proj family i a) = .proj family i (proofErase Γ a) from if_neg hpa]
      simp only [ProofShape.liftN, Ea]
    have Epb : (proofErase Γ (.proj family i b)).liftN n k = .proj family i sb := by
      rw [show proofErase Γ (.proj family i b) = .proj family i (proofErase Γ b) from if_neg hpb]
      simp only [ProofShape.liftN, Eb]
    exact ihfields i hj HP hΓ hΓ' W hiaF hibF EΔ EFlift Epa Epb

/-- Joint comparison descends below any inserted block. Common-mode checking
uses the supplied type equality; inferred checking only needs non-proofness. -/
theorem proofErase_joint_compare_descend (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (hΔ : proofEraseCtx Γ' = Δ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ProofShape.JointCompare Step Δ mode
      ((proofErase Γ a).liftN n k) ((proofErase Γ b).liftN n k)) :
    (env.IsDefEqU univs Γ A B → env.IsDefEqU univs Γ a b) ∧
    (mode = false → ¬ IsProof Γ a → ¬ IsProof Γ b → env.IsDefEqU univs Γ a b) :=
  joint_check_descent hstep H hΓ hΓ' W hΔ ha hb rfl rfl

/-- Explicit-carrier checking descends with its lower carrier and endpoint
 typings, even when it recursively invokes recovered application comparison. -/
theorem proofErase_joint_carrier_descend (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : ProofShape.JointCarrierGuard Step (proofEraseCtx Γ')
      ((proofErase Γ A).liftN n k) ((proofErase Γ a).liftN n k) ((proofErase Γ b).liftN n k)) :
    env.IsDefEqU univs Γ a b :=
  joint_check_descent hstep H hΓ hΓ' W ha hb rfl rfl rfl rfl

/-- Original-context reflection for the two comparison modes. -/
theorem proofErase_joint_compare_reflect (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ProofShape.JointCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b)) :
    (env.IsDefEqU univs Γ A B → env.IsDefEqU univs Γ a b) ∧
    (mode = false → ¬ IsProof Γ a → ¬ IsProof Γ b → env.IsDefEqU univs Γ a b) :=
  proofErase_joint_compare_descend hstep hΓ hΓ (show Ctx.LiftN 0 0 Γ Γ from .zero []) rfl ha hb
    (by simpa only [ProofShape.liftN_zero] using H)

/-- Original-context reflection at the supplied common carrier. -/
theorem proofErase_joint_carrier_reflect (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : ProofShape.JointCarrierGuard Step (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ a) (proofErase Γ b)) : env.IsDefEq univs Γ a b A :=
  IsDefEqU.of_l henv hΓ (proofErase_joint_carrier_descend hstep hΓ hΓ
    (show Ctx.LiftN 0 0 Γ Γ from .zero []) ha hb
    (by simpa only [ProofShape.liftN_zero] using H)) ha

end Lean4Lean.VEnv.Strengthening
