import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCertificateDescent
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointFieldRealization

/-! # Lower certificates for mutually recursive joint checking

Typed descent reconstructs a checker certificate, including recovered domains,
eta bodies and dependent record fields. Only primitive certificate descent is
assumed; no completeness, inverse typing weakening or carrier resynthesis law
is used.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private ProofShape.liftN_app_inv ProofShape.liftN_proj_inv ProofShape.liftN_lam_inv
  ProofShape.liftN_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private joint_check_descent from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointDescent
variable [Params]

omit [Params] in
private theorem leaf_descend
    (H : ProofShape.ScopedLeaf mode (a.liftN n k) (b.liftN n k)) :
    ProofShape.ScopedLeaf mode a b := by
  have R := H.subst (τ := ProofShape.Subst.retract (.consN (.skipN .refl n) k))
  simpa only [← ProofShape.lift'_consN_skipN, ProofShape.subst_retract_lift'] using R

private theorem subsingleton_descend
    (H : ProofShape.SubsingletonCarrier (a.liftN n k)) :
    ProofShape.SubsingletonCarrier a := by
  have R := H.subst (ProofShape.Subst.retract (.consN (.skipN .refl n) k))
  simpa only [← ProofShape.lift'_consN_skipN, ProofShape.subst_retract_lift'] using R




private def JointCertificateDescent (Target : List ProofShape → ProofShape → ProofShape → Prop) (n : Nat) (Δ : List ProofShape)
    (kind : ProofShape.JointCheckKind) (sa sb : ProofShape) : Prop :=
  match kind with
  | .compare mode => ∀ {Γ Γ' k a b A B},
      OnCtx Γ (env.IsType univs) → OnCtx Γ' (env.IsType univs) →
      Ctx.LiftN n k Γ Γ' → proofEraseCtx Γ' = Δ →
      env.HasType univs Γ a A → env.HasType univs Γ b B →
      (proofErase Γ a).liftN n k = sa → (proofErase Γ b).liftN n k = sb →
      (env.IsDefEqU univs Γ A B → ProofShape.JointCompare Target (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b)) ∧
      (mode = false → ¬ IsProof Γ a → ¬ IsProof Γ b → ProofShape.JointCompare Target (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b))
  | .carrier α => ∀ {Γ Γ' k A a b},
      OnCtx Γ (env.IsType univs) → OnCtx Γ' (env.IsType univs) →
      Ctx.LiftN n k Γ Γ' → env.HasType univs Γ a A → env.HasType univs Γ b A →
      proofEraseCtx Γ' = Δ → (proofErase Γ A).liftN n k = α →
      (proofErase Γ a).liftN n k = sa → (proofErase Γ b).liftN n k = sb →
      ProofShape.JointCarrierGuard Target (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ a) (proofErase Γ b)

private theorem joint_check_certificate_descend
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Target)
    (H : ProofShape.JointCheck Step Δ kind sa sb) : JointCertificateDescent Target n Δ kind sa sb := by
  induction H with
  | leaf H =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    have C : ProofShape.JointCompare Target (proofEraseCtx Γ) _ (proofErase Γ a) (proofErase Γ b) :=
      .leaf (leaf_descend (n := n) (k := k) (by simpa only [Ea, Eb] using H))
    exact ⟨fun _ => C, fun _ _ _ => C⟩
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
    have HF := ((joint_check_descent hstep.descent Hf) hΓ hΓ' W hΔ hf hf' Eaf Ebf).2 rfl (not_isProof_fn hΓ hf hx hna) (not_isProof_fn hΓ hf' hx' hnb)
    have HFF := HF.of_l henv hΓ hf
    obtain ⟨⟨_, hDD⟩, _⟩ := (HFF.hasType.2.uniqU henv hΓ hf').forallE_inv henv hΓ
    have CF := (ihf hΓ hΓ' W hΔ hf hf' Eaf Ebf).2 rfl
      (not_isProof_fn hΓ hf hx hna) (not_isProof_fn hΓ hf' hx' hnb)
    have CX := (ihx hΓ hΓ' W hΔ hx hx' Eax Ebx).1 ⟨_, hDD⟩
    have C : ProofShape.JointCompare Target (proofEraseCtx Γ) mode
        (proofErase Γ (.app f x)) (proofErase Γ (.app f' x')) := by
      simpa only [proofErase, if_neg hna, if_neg hnb] using ProofShape.JointCheck.app CF CX
    exact ⟨fun _ => C, fun _ _ _ => C⟩
  | appCarrier R HF HX ihf ihx =>
    rename_i mode
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
    obtain ⟨F, hfPi, RF, EF⟩ := proofErase_scoped_recovery_certificate_descend hstep hΓ hΓ' W hf rfl R
    obtain ⟨_, _, Es, ED, EC⟩ := ProofShape.liftN_forallE_inv EF
    obtain ⟨D, C, rfl, hnF, EDom, ECod⟩ := erase_forallE_inv Es
    rw [← EDom] at ED
    rw [← ECod] at EC
    rw [show proofErase Γ (.forallE D C) = .forallE (proofErase Γ D) (proofErase (D :: Γ) C) from if_neg hnF] at RF
    have Hfg := ((joint_check_descent hstep.descent HF) hΓ hΓ' W hΔ hf hg Eaf Ebg).2 rfl
      (not_isProof_fn hΓ hf hx hna) (not_isProof_fn hΓ hg hy hnb)
    have HfgPi := Hfg.of_l henv hΓ hfPi
    have hxD := argument_at_displayed_domain hΓ hf hfPi hx
    have hyD := argument_at_displayed_domain hΓ hg HfgPi.hasType.2 hy
    have CX := ihx hΓ hΓ' W hxD hyD hΔ ED Eax Eby
    have CF := (ihf hΓ hΓ' W hΔ hf hg Eaf Ebg).2 rfl
      (not_isProof_fn hΓ hf hx hna) (not_isProof_fn hΓ hg hy hnb)
    have C : ProofShape.JointCompare Target (proofEraseCtx Γ) mode
        (proofErase Γ (.app f x)) (proofErase Γ (.app g y)) := by
      simpa only [proofErase, if_neg hna, if_neg hnb] using ProofShape.JointCheck.appCarrier RF CF CX
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
    have C : ProofShape.JointCompare Target (proofEraseCtx Γ) mode
        (proofErase Γ (.proj s i m)) (proofErase Γ (.proj s i m')) := by
      simpa only [proofErase, if_neg hn, if_neg hn'] using ProofShape.JointCheck.proj CM
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
    have HDU := ((joint_check_descent hstep.descent HD) hΓ hΓ' W hΔ hD hD' EaD EbD).2 rfl (not_isProof_of_sort hΓ hD) (not_isProof_of_sort hΓ hD')
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
    have finish (CB : ProofShape.JointCompare Target (proofEraseCtx (D :: Γ)) mode
        (proofErase (D :: Γ) body) (proofErase (D :: Γ) body')) :
        ProofShape.JointCompare Target (proofEraseCtx Γ) mode
          (proofErase Γ (.lam D body)) (proofErase Γ (.lam D' body')) := by
      simpa only [proofErase, if_neg hna, if_neg hnb, Ectx, proofEraseCtx] using
        (show ProofShape.JointCompare Target (proofEraseCtx Γ) mode
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
    have HDU := ((joint_check_descent hstep.descent HD) hΓ hΓ' W hΔ hD hD' EaD EbD).2 rfl (not_isProof_of_sort hΓ hD) (not_isProof_of_sort hΓ hD')
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
    have C : ProofShape.JointCompare Target (proofEraseCtx Γ) mode
        (proofErase Γ (.forallE D C)) (proofErase Γ (.forallE D' C')) := by
      simpa only [proofErase, if_neg hna, if_neg hnb, Ectx, proofEraseCtx] using
        (show ProofShape.JointCompare Target (proofEraseCtx Γ) mode
          (.forallE (proofErase Γ D) (proofErase (D :: Γ) C))
          (.forallE (proofErase Γ D') (proofErase (D :: Γ) C')) from .forallE CD CC)
    exact ⟨fun _ => C, fun _ _ _ => C⟩
  | lamSorted SA SA' HD Hbody ihD ihbody =>
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
    have hD := ProofShape.DomainSort.descend (by simpa only [hΔ, EaD] using SA) hΓ hΓ' W hD
    have hD' := ProofShape.DomainSort.descend (by simpa only [hΔ, EbD] using SA') hΓ hΓ' W hD'
    have HDU := ((joint_check_descent hstep.descent HD) hΓ hΓ' W hΔ hD hD' EaD EbD).1 ⟨_, HasType.sort (hD.sort_r henv hΓ)⟩
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
    have CD := (ihD hΓ hΓ' W hΔ hD hD' EaD EbD).1 ⟨_, HasType.sort (hD.sort_r henv hΓ)⟩
    have finish (CB : ProofShape.JointCompare Target (proofEraseCtx (D :: Γ)) mode
        (proofErase (D :: Γ) body) (proofErase (D :: Γ) body')) :
        ProofShape.JointCompare Target (proofEraseCtx Γ) mode
          (proofErase Γ (.lam D body)) (proofErase Γ (.lam D' body')) := by
      simpa only [proofErase, if_neg hna, if_neg hnb, Ectx, proofEraseCtx] using
        (show ProofShape.JointCompare Target (proofEraseCtx Γ) mode
          (.lam (proofErase Γ D) (proofErase (D :: Γ) body))
          (.lam (proofErase Γ D') (proofErase (D :: Γ) body')) from .lamSorted (.of_typed hΓ hD) (.of_typed hΓ hD') CD CB)
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
    have hD := ProofShape.DomainSort.descend (by simpa only [hΔ, EaD] using SA) hΓ hΓ' W hD
    have hD' := ProofShape.DomainSort.descend (by simpa only [hΔ, EbD] using SA') hΓ hΓ' W hD'
    have HDU := ((joint_check_descent hstep.descent HD) hΓ hΓ' W hΔ hD hD' EaD EbD).1 ⟨_, HasType.sort (hD.sort_r henv hΓ)⟩
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
    have CC := (ihC hΓD hΓD' W.succ hctxE
      hC hC' EaC EbC).1 ⟨_, HasType.sort (hC.sort_r henv hΓD)⟩
    have CD := (ihD hΓ hΓ' W hΔ hD hD' EaD EbD).1 ⟨_, HasType.sort (hD.sort_r henv hΓ)⟩
    have C : ProofShape.JointCompare Target (proofEraseCtx Γ) mode
        (proofErase Γ (.forallE D C)) (proofErase Γ (.forallE D' C')) := by
      simpa only [proofErase, if_neg hna, if_neg hnb, Ectx, proofEraseCtx] using
        (show ProofShape.JointCompare Target (proofEraseCtx Γ) mode
          (.forallE (proofErase Γ D) (proofErase (D :: Γ) C))
          (.forallE (proofErase Γ D') (proofErase (D :: Γ) C')) from .forallSorted (.of_typed hΓ hD) (.of_typed hΓ hD') CD (.of_typed hΓD hC) (.of_typed hΓD hC') CC)
    exact ⟨fun _ => C, fun _ _ _ => C⟩
  | lamCommon Hbody ihbody =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    constructor
    · intro hAB
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
      have CB := HI.1 ⟨_, hCC⟩
      simpa only [proofErase, if_neg hna, if_neg hnb, Ectx, proofEraseCtx] using
        (show ProofShape.JointCompare Target (proofEraseCtx Γ) true
          (.lam (proofErase Γ D) (proofErase (D :: Γ) body))
          (.lam (proofErase Γ D') (proofErase (D :: Γ) body')) from .lamCommon CB)
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
      rw [proofErase_eta_body hΓ hD hfPi hnf] at HI
      have C := ProofShape.JointCheck.etaBodyL (Step := Target) (.of_typed hΓ hD) HI
      simpa only [proofErase, if_neg hn] using C
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
      rw [proofErase_eta_body hΓ hD hfPi hnf] at HI
      have C := ProofShape.JointCheck.etaBodyR (Step := Target) (.of_typed hΓ hD) HI
      simpa only [proofErase, if_neg hn] using C
    · intro hmode; cases hmode
  | @structFields Δ family info ls ps fields major hi hx hp hf hadm Hfields ihfields =>
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    constructor
    · intro hAB
      have HE := ((joint_check_descent hstep.descent
        (.structFields hi hx hp hf hadm Hfields)) hΓ hΓ' W hΔ ha hb Ea Eb).1 hAB
      have HE := HE.of_l henv hΓ ha
      obtain ⟨rawArgs, Es, Eargs⟩ := ProofShape.liftN_const_spine_inv Ea
      let ps₀ := rawArgs.take info.nparams
      let fs₀ := rawArgs.drop info.nparams
      have Hps : ps₀.map (fun a => a.liftN n k) = ps := by
        simp only [ps₀, List.map_take, ← Eargs, ← hp, List.take_left]
      have Hfs : fs₀.map (fun a => a.liftN n k) = fields := by
        simp only [fs₀, List.map_drop, ← Eargs, ← hp, List.drop_left]
      have hp₀ : ps₀.length = info.nparams := by simpa only [List.length_map, hp] using congrArg List.length Hps
      have hf₀ : fs₀.length = info.numFields := by simpa only [List.length_map, hf] using congrArg List.length Hfs
      have Hsplit : rawArgs = ps₀ ++ fs₀ := (List.take_append_drop info.nparams rawArgs).symm
      rw [Hsplit] at Es
      rw [Es]
      apply ProofShape.JointCheck.structFields hi hx hp₀ hf₀ hadm
      intro i hj hn
      have hj' : i < fields.length := by omega
      have Ei : (fs₀[i]).liftN n k = fields[i] := by simp only [← Hfs, List.getElem_map]
      have hnraw : fields[i] ≠ ProofShape.proof := by
        intro E
        exact hn (ProofShape.liftN_inj.1 (Ei.trans E))
      obtain ⟨x, X, hxt, hpt, Ex⟩ := proofErase_equal_structure_field_realize hΓ HE hi hx hp₀ hf₀ hadm Es hj
      have hnx : ¬ IsProof Γ x := fun H => hn (Ex.symm.trans (proofErase_eq_proof.2 H))
      have hnp : ¬ IsProof Γ (.proj family i b) := fun H => hnx (isProof_of_common_type hΓ hpt hxt H)
      have Eproj : (proofErase Γ (.proj family i b)).liftN n k = .proj family i major := by
        rw [show proofErase Γ (.proj family i b) = .proj family i (proofErase Γ b) from if_neg hnp]
        simp only [ProofShape.liftN, Eb]
      have C := (ihfields i hj' hnraw hΓ hΓ' W hΔ hxt hpt
        (by simpa only [Ex] using Ei) Eproj).1 ⟨_, hxt.isType henv hΓ |>.choose_spec⟩
      simpa only [Ex, show proofErase Γ (.proj family i b) = .proj family i (proofErase Γ b) from if_neg hnp] using C
    · intro hm; cases hm
  | etaLams HD Hη ihD =>
    rename_i mode
    intro Γ Γ' k a b A B hΓ hΓ' W hΔ ha hb Ea Eb
    rw [← Ea, ← Eb] at Hη
    obtain ⟨_, _, haE, EaD, _⟩ := ProofShape.liftN_lam_inv Ea
    obtain ⟨_, _, hbE, EbD, _⟩ := ProofShape.liftN_lam_inv Eb
    obtain ⟨D, body, rfl, hna, ED, _⟩ := erase_lam_inv haE
    obtain ⟨D', body', rfl, hnb, ED', _⟩ := erase_lam_inv hbE
    rw [← ED] at EaD
    rw [← ED'] at EbD
    obtain ⟨⟨_, hD⟩, _, hbody⟩ := ha.lam_inv henv hΓ
    obtain ⟨⟨_, hD'⟩, _, hbody'⟩ := hb.lam_inv henv hΓ
    have CD := (ihD hΓ hΓ' W hΔ hD hD' EaD EbD).2 rfl
      (not_isProof_of_sort hΓ hD) (not_isProof_of_sort hΓ hD')
    have Hη := Hη.imp (fun H => H.of_liftN) (fun H => H.of_liftN)
    simp only [proofErase, if_neg hna, if_neg hnb] at Hη ⊢
    have C := ProofShape.JointCheck.etaLams (Step := Target) (mode := mode) CD Hη
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
  | carrierChecked HC ih =>
    intro Γ Γ' k A a b hΓ hΓ' W ha hb EΔ Eα Ea Eb
    obtain ⟨_, hA⟩ := ha.isType henv hΓ
    exact .carrierChecked ((ih hΓ hΓ' W EΔ ha hb Ea Eb).1 (.refl ⟨_, hA⟩))
  | carrierSubsingleton H =>
    intro Γ Γ' k A a b hΓ hΓ' W ha hb EΔ Eα Ea Eb
    rw [← Eα] at H
    exact .carrierSubsingleton (subsingleton_descend H)
  | carrierFunction S H ih =>
    intro Γ Γ' k A a b hΓ hΓ' W ha hb EΔ Eα Ea Eb
    obtain ⟨_, _, ET, ED, EB⟩ := ProofShape.liftN_forallE_inv Eα
    obtain ⟨D, B, rfl, hnT, ED', EB'⟩ := erase_forallE_inv ET
    rw [← ED'] at ED
    rw [← EB'] at EB
    obtain ⟨_, hT⟩ := ha.isType henv hΓ
    obtain ⟨⟨_, hD₀⟩, _, _⟩ := hT.forallE_inv henv
    have hD := ProofShape.DomainSort.descend (by simpa only [EΔ, ED] using S) hΓ hΓ' W hD₀
    by_cases hpa : IsProof Γ a
    · obtain ⟨P, haP, hP⟩ := hpa
      have hpb : IsProof Γ b := ⟨P, hb.defeqU_r henv hΓ (ha.uniqU henv hΓ haP), hP⟩
      rw [proofErase_eq_proof.2 ⟨P, haP, hP⟩, proofErase_eq_proof.2 hpb]
      exact .carrierChecked (.leaf .refl)
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
    rw [proofErase_eta_body hΓ hD ha hpa, proofErase_eta_body hΓ hD hb hpb] at HI
    rw [show proofErase Γ (.forallE D B) = .forallE (proofErase Γ D) (proofErase (D :: Γ) B) from if_neg hnT]
    exact .carrierFunction (.of_typed hΓ hD) HI
  | carrierSymm H ih =>
    intro Γ Γ' k A a b hΓ hΓ' W ha hb EΔ Eα Ea Eb
    exact .carrierSymm (ih hΓ hΓ' W hb ha EΔ Eα Eb Ea)
  | carrierCompute R H ih =>
    intro Γ Γ' k A a b hΓ hΓ' W ha hb EΔ Eα Ea Eb
    rw [← Eα] at R
    obtain ⟨u, hA⟩ := ha.isType henv hΓ
    obtain ⟨A', HE, RC, EA'⟩ := proofErase_scoped_compute_certificate_descend hstep hΓ hΓ' W hA EΔ R
    exact .carrierCompute RC (ih hΓ hΓ' W (HE.defeq ha) (HE.defeq hb) EΔ EA' Ea Eb)
  | carrierReduce Ra Rb H ih =>
    intro Γ Γ' k A a b hΓ hΓ' W ha hb EΔ Eα Ea Eb
    rw [← Ea] at Ra
    rw [← Eb] at Rb
    obtain ⟨a', HA, RA, EA⟩ := proofErase_scoped_compute_certificate_descend hstep hΓ hΓ' W ha EΔ Ra
    obtain ⟨b', HB, RB, EB⟩ := proofErase_scoped_compute_certificate_descend hstep hΓ hΓ' W hb EΔ Rb
    have HI := ih hΓ hΓ' W HA.hasType.2 HB.hasType.2 EΔ Eα EA EB
    exact .carrierReduce RA RB HI
  | carrierIntro hi hx hp hadm Hfields ihfields =>
    intro Γ Γ' k A a b hΓ hΓ' W ha hb EΔ Eα Ea Eb
    rename_i family info ls Δ sa sb ps
    have HE := (joint_check_descent hstep.descent (.carrierIntro hi hx hp hadm Hfields)) hΓ hΓ' W ha hb EΔ Eα Ea Eb
    have HE := HE.of_l henv hΓ ha
    obtain ⟨rawArgs, Es, Eargs⟩ := ProofShape.liftN_const_spine_inv Eα
    obtain ⟨args, rfl, Eoriginal⟩ := proofErase_const_spine_inv Es
    rw [Eoriginal] at Eargs
    have hlen : args.length = info.nparams := by
      have Hlen := congrArg List.length Eargs
      simpa only [List.length_map, hp] using Hlen.symm
    have hexpa := (StructureReplay.expansion_typed_iff henv hΓ hi hlen hx ha).2 hadm
    rw [Es, Eoriginal]
    apply ProofShape.JointCheck.carrierIntro hi hx (by simp only [List.length_map, hlen]) hadm
    intro i hj HP
    obtain ⟨F₀, hia, hib⟩ := structure_equal_projection_typings hΓ HE hexpa hj
    have hpa : ¬ IsProof Γ (.proj family i a) := fun H =>
      HP (StructureReplay.ProofField.of_projection hΓ hi hlen hj hexpa H)
    have hpb : ¬ IsProof Γ (.proj family i b) := fun H => hpa (isProof_of_common_type hΓ hib hia H)
    have Epa : (proofErase Γ (.proj family i a)).liftN n k = .proj family i sa := by
      rw [show proofErase Γ (.proj family i a) = .proj family i (proofErase Γ a) from if_neg hpa]
      simp only [ProofShape.liftN, Ea]
    have Epb : (proofErase Γ (.proj family i b)).liftN n k = .proj family i sb := by
      rw [show proofErase Γ (.proj family i b) = .proj family i (proofErase Γ b) from if_neg hpb]
      simp only [ProofShape.liftN, Eb]
    have C := (ihfields i hj HP hΓ hΓ' W EΔ hia hib Epa Epb).1 ⟨_, hia.isType henv hΓ |>.choose_spec⟩
    simpa only [show proofErase Γ (.proj family i a) = .proj family i (proofErase Γ a) from if_neg hpa,
      show proofErase Γ (.proj family i b) = .proj family i (proofErase Γ b) from if_neg hpb] using C
  | carrierNested hi hx hp hadm HT Hfields ihfields =>
    intro Γ Γ' k A a b hΓ hΓ' W ha hb EΔ Eα Ea Eb
    rename_i family info ls doms result Δ ps sa sb
    have HE := (joint_check_descent hstep.descent (.carrierNested hi hx hp hadm HT Hfields)) hΓ hΓ' W ha hb EΔ Eα Ea Eb
    have HE := HE.of_l henv hΓ ha
    obtain ⟨rawArgs, Es, Eargs⟩ := ProofShape.liftN_const_spine_inv Eα
    obtain ⟨args, rfl, Eoriginal⟩ := proofErase_const_spine_inv Es
    rw [Eoriginal] at Eargs
    have hlen : args.length = info.nparams := by
      have Hlen := congrArg List.length Eargs
      simpa only [List.length_map, hp] using Hlen.symm
    have hexpa := (StructureReplay.expansion_typed_iff henv hΓ hi hlen hx ha).2 hadm
    rw [Es, Eoriginal]
    apply ProofShape.JointCheck.carrierNested hi hx (by simp only [List.length_map, hlen]) hadm HT
    intro i hj HP
    obtain ⟨F₀, hia, hib⟩ := structure_equal_projection_typings hΓ HE hexpa hj
    have hpa : ¬ IsProof Γ (.proj family i a) := fun H =>
      HP (StructureReplay.ProofField.of_projection hΓ hi hlen hj hexpa H)
    have hpb : ¬ IsProof Γ (.proj family i b) := fun H => hpa (isProof_of_common_type hΓ hib hia H)
    have Epa : (proofErase Γ (.proj family i a)).liftN n k = .proj family i sa := by
      rw [show proofErase Γ (.proj family i a) = .proj family i (proofErase Γ a) from if_neg hpa]
      simp only [ProofShape.liftN, Ea]
    have Epb : (proofErase Γ (.proj family i b)).liftN n k = .proj family i sb := by
      rw [show proofErase Γ (.proj family i b) = .proj family i (proofErase Γ b) from if_neg hpb]
      simp only [ProofShape.liftN, Eb]
    obtain ⟨hj', F, hiaF, EF⟩ := proofErase_projection_at_recovered_family hΓ hi HT hia hpa ha
    have hibF := hib.defeqU_r henv hΓ (hia.uniqU henv hΓ hiaF)
    have EF' : proofErase Γ F = ProofShape.projectionType family info doms i hj'
        (args.map (proofErase Γ)) (proofErase Γ a) := by
      simpa only [ProofShape.projectionType, List.map_take] using EF
    have EFlift : (proofErase Γ F).liftN n k =
        ProofShape.projectionType family info doms i hj' ps sa := by
      rw [EF', ProofShape.projectionType_liftN HT hj' (by simp [hlen]), ← Eargs, Ea]
    have C := ihfields i hj HP hΓ hΓ' W hiaF hibF EΔ EFlift Epa Epb
    simpa only [EF', show proofErase Γ (.proj family i a) = .proj family i (proofErase Γ a) from if_neg hpa,
      show proofErase Γ (.proj family i b) = .proj family i (proofErase Γ b) from if_neg hpb] using C

/-- A lower typed comparison retains its mode and a full Target certificate.
Common checking uses equality of the supplied types; inferred checking uses
non-proofness of both independently typed endpoints. -/
theorem proofErase_joint_compare_certificate_descend
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Target)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (hΔ : proofEraseCtx Γ' = Δ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ProofShape.JointCompare Step Δ mode
      ((proofErase Γ a).liftN n k) ((proofErase Γ b).liftN n k)) :
    (env.IsDefEqU univs Γ A B →
      ProofShape.JointCompare Target (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b)) ∧
    (mode = false → ¬ IsProof Γ a → ¬ IsProof Γ b →
      ProofShape.JointCompare Target (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b)) :=
  joint_check_certificate_descend hstep H hΓ hΓ' W hΔ ha hb rfl rfl

/-- Explicit-carrier descent retains the exact lower carrier and recursively
checked fields, including dependent projection recipes and function eta. -/
theorem proofErase_joint_carrier_certificate_descend
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Target)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : ProofShape.JointCarrierGuard Step (proofEraseCtx Γ')
      ((proofErase Γ A).liftN n k) ((proofErase Γ a).liftN n k) ((proofErase Γ b).liftN n k)) :
    ProofShape.JointCarrierGuard Target (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ a) (proofErase Γ b) :=
  joint_check_certificate_descend hstep H hΓ hΓ' W ha hb rfl rfl rfl rfl

end Lean4Lean.VEnv.Strengthening
