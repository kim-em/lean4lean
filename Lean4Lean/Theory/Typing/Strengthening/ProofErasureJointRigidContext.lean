import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRigidOracleRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointTransport

/-! # Typed joint checking through rigid oracle changes

Rigid terminal replacements preserve the exact domains used by application
recovery. Typed induction transports both comparison and carrier checking,
including function bodies and dependent structure fields.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private infer_raw common_raw carrier_raw domain_sort_raw lambda_common_context
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointTransport
open private oracle_cons_change
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRigidOracleRecovery
variable [Params]

private theorem sort_context (_hΓ : OnCtx Γ (env.IsType univs))
    (W : IsDefEqCtx env univs [] Γ Γ') (EΓ : proofEraseCtx Γ = Δ)
    (S : DomainSort Δ A u) : DomainSort (proofEraseCtx Γ') A u := by
  have H := ContextSubstitution.sort (ContextSubstitution.of_defeqCtx (by trivial) W) (EΓ ▸ S)
  simpa only [ProofShape.subst_id] using H

private theorem compute_context
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (W : IsDefEqCtx env univs [] Γ Γ') (EΓ : proofEraseCtx Γ = Δ)
    (R : ScopedCompute Step Δ A B) : ScopedCompute Step (proofEraseCtx Γ') A B := by
  exact (EΓ ▸ R).defeqCtx hsubst (by trivial) W

private theorem oracle_cons_typed
    (hΓ : OnCtx Γ (env.IsType univs)) (W : IsDefEqCtx env univs [] Γ Γ')
    (hD : env.HasType univs Γ D (.sort u))
    (ED : proofErase Γ D = d)
    (HO : ∀ i, RigidResultChange (contextOracle Δ i) (contextOracle (proofEraseCtx Γ') i)) :
    ∀ i, RigidResultChange (contextOracle (d :: Δ) i)
      (contextOracle (proofEraseCtx (D :: Γ')) i) := by
  simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using oracle_cons_change HO

/-- Transport target for typed endpoints. Carrier syntax stays fixed while
actual contexts change by equality and their oracles by rigid replacement. -/
def JointRigidOracleResult
    (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (kind : JointCheckKind) (sa sb : ProofShape) : Prop :=
  match kind with
  | .compare mode => ∀ {Γ Γ' a b A}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ a A → env.HasType univs Γ b A → proofEraseCtx Γ = Δ →
      proofErase Γ a = sa → proofErase Γ b = sb → IsDefEqCtx env univs [] Γ Γ' →
      (∀ i, RigidResultChange (contextOracle Δ i) (contextOracle (proofEraseCtx Γ') i)) →
      JointCompare Step (proofEraseCtx Γ') mode sa sb
  | .carrier α => ∀ {Γ Γ' a b A}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ a A → env.HasType univs Γ b A → proofEraseCtx Γ = Δ →
      proofErase Γ A = α → proofErase Γ a = sa → proofErase Γ b = sb →
      IsDefEqCtx env univs [] Γ Γ' →
      (∀ i, RigidResultChange (contextOracle Δ i) (contextOracle (proofEraseCtx Γ') i)) →
      JointCarrierGuard Step (proofEraseCtx Γ') α sa sb

/-- All typed joint constructors survive rigid oracle replacement. The
application case uses typed Pi recovery to retain its original argument domain;
no carrier-domain re-synthesis or semantic head exposure premise is needed. -/
theorem ProofShape.JointCheck.rigid_oracles
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : JointCheck Step Δ kind sa sb) : JointRigidOracleResult Step Δ kind sa sb := by
  induction H with
  | leaf H =>
    intro Γ Γ' a b A hΓ ha hb EΓ Ea Eb W HO
    exact .leaf H
  | app HF HX ihf ihx =>
    intro Γ Γ' a b A hΓ ha hb EΓ Ea Eb W HO
    obtain ⟨f, x, rfl, hna, Ef, Ex⟩ := erase_app_inv Ea
    obtain ⟨g, y, rfl, hnb, Eg, Ey⟩ := erase_app_inv Eb
    obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
    obtain ⟨_, _, hg, hy⟩ := hb.app_inv henv hΓ
    have HE := infer_raw hstep HF hΓ hf hg EΓ Ef Eg
      (not_isProof_fn hΓ hf hx hna) (not_isProof_fn hΓ hg hy hnb)
    have hy' := argument_at_displayed_domain hΓ hg HE.hasType.2 hy
    exact .app (ihf hΓ hf HE.hasType.2 EΓ Ef Eg W HO) (ihx hΓ hx hy' EΓ Ex Ey W HO)
  | appCarrier R HF HX ihf ihx =>
    intro Γ Γ' a b A hΓ ha hb EΓ Ea Eb W HO
    obtain ⟨f, x, rfl, hna, Ef, Ex⟩ := erase_app_inv Ea
    obtain ⟨g, y, rfl, hnb, Eg, Ey⟩ := erase_app_inv Eb
    obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
    obtain ⟨_, _, hg, hy⟩ := hb.app_inv henv hΓ
    have HE := infer_raw hstep HF hΓ hf hg EΓ Ef Eg
      (not_isProof_fn hΓ hf hx hna) (not_isProof_fn hΓ hg hy hnb)
    obtain ⟨D, C, hfPi, ED, EC⟩ := proofErase_scoped_recovered_pi_descend hstep hΓ hΓ
      (show Ctx.LiftN 0 0 Γ Γ from .zero []) hf
      (by simpa only [ProofShape.liftN_zero, EΓ, Ef] using R)
    have hgPi := (show env.IsDefEqU univs Γ f g from ⟨_, HE⟩).of_l henv hΓ hfPi |>.hasType.2
    have hxD := argument_at_displayed_domain hΓ hf hfPi hx
    have hyD := argument_at_displayed_domain hΓ hg hgPi hy
    simp only [ProofShape.liftN_zero] at ED EC
    obtain ⟨B', R'⟩ := proofErase_recovery_rigid_oracles_pi hstep hhead hsubst hΓ hfPi W
      (by simpa only [EΓ] using HO) (by simpa only [EΓ, Ef] using R)
    rw [Ef] at R'
    exact .appCarrier R' (ihf hΓ hf HE.hasType.2 EΓ Ef Eg W HO)
      (ihx hΓ hxD hyD EΓ ED Ex Ey W HO)
  | proj HM ihm =>
    intro Γ Γ' a b A hΓ ha hb EΓ Ea Eb W HO
    obtain ⟨m, rfl, hn, Em⟩ := erase_proj_inv Ea
    obtain ⟨m', rfl, hn', Em'⟩ := erase_proj_inv Eb
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm', _, _⟩ := hb.proj_inv henv hΓ
    have HE := infer_raw hstep HM hΓ hm.hasType.2 hm'.hasType.2 EΓ Em Em'
      (not_isProof_major hΓ ha hn) (not_isProof_major hΓ hb hn')
    exact .proj (ihm hΓ hm.hasType.2 HE.hasType.2 EΓ Em Em' W HO)
  | lam HD HB ihD ihB =>
    intro Γ Γ' a b A hΓ ha hb EΓ Ea Eb W HO
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HB' := ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED])
      Ebody Ebody' (.succ W hD) (oracle_cons_typed hΓ W hD ED HO)
    apply JointCheck.lam (ihD hΓ hD hD' EΓ ED ED' W HO)
    simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using HB'
  | lamSorted SD SD' HD HB ihD ihB =>
    intro Γ Γ' a b A hΓ ha hb EΓ Ea Eb W HO
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HB' := ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED])
      Ebody Ebody' (.succ W hD) (oracle_cons_typed hΓ W hD ED HO)
    apply JointCheck.lamSorted (sort_context hΓ W EΓ SD) (sort_context hΓ W EΓ SD') (ihD hΓ hD hD' EΓ ED ED' W HO)
    simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using HB'
  | lamCommon HB ihB =>
    intro Γ Γ' a b A hΓ ha hb EΓ Ea Eb W HO
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HB' := ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED])
      Ebody Ebody' (.succ W hD) (oracle_cons_typed hΓ W hD ED HO)
    apply JointCheck.lamCommon
    simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using HB'
  | etaLams HD Hη ihD =>
    intro Γ Γ' a b A hΓ ha hb EΓ Ea Eb W HO
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    exact .etaLams (ihD hΓ hD hD' EΓ ED ED' W HO) (Hη.imp (fun H => H) (fun H => H))
  | forallE HD HC ihD ihC =>
    intro Γ Γ' a b A hΓ ha hb EΓ Ea Eb W HO
    obtain ⟨D, C, rfl, _, ED, EC⟩ := erase_forallE_inv Ea
    obtain ⟨D', C', rfl, _, ED', EC'⟩ := erase_forallE_inv Eb
    obtain ⟨⟨u, hD⟩, _, hC⟩ := ha.forallE_inv henv
    obtain ⟨⟨_, hD'⟩, _, hC'⟩ := hb.forallE_inv henv
    have HDD := infer_raw hstep HD hΓ hD hD' EΓ ED ED'
      (not_isProof_of_sort hΓ hD) (not_isProof_of_sort hΓ hD')
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have hctx := IsDefEqCtx.succ .zero HDD.symm
    have Ectx := proofErase_defeqCtx (Γ₁ := D' :: Γ) ⟨hΓ, _, hD'⟩ hctx hC'
    rw [Ectx] at EC'
    have hC' := hC'.defeqDFC henv hctx
    have EΓD := congr (congrArg List.cons ED) EΓ
    change proofEraseCtx (D :: Γ) = _ at EΓD
    have HCC := infer_raw hstep HC hΓD hC hC' EΓD EC EC'
      (not_isProof_of_sort hΓD hC) (not_isProof_of_sort hΓD hC')
    apply JointCheck.forallE (ihD hΓ hD HDD.hasType.2 EΓ ED ED' W HO)
    simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using
      (ihC hΓD hC HCC.hasType.2 EΓD EC EC' (.succ W hD) (oracle_cons_typed hΓ W hD ED HO))
  | forallSorted SD SD' HD SC SC' HC ihD ihC =>
    intro Γ Γ' a b A hΓ ha hb EΓ Ea Eb W HO
    obtain ⟨D, C, rfl, _, ED, EC⟩ := erase_forallE_inv Ea
    obtain ⟨D', C', rfl, _, ED', EC'⟩ := erase_forallE_inv Eb
    obtain ⟨⟨_, hD⟩, _, hC⟩ := ha.forallE_inv henv
    obtain ⟨⟨_, hD'⟩, _, hC'⟩ := hb.forallE_inv henv
    have hD := domain_sort_raw SD hΓ hD EΓ ED
    have hD' := domain_sort_raw SD' hΓ hD' EΓ ED'
    have HDD := common_raw hstep HD hΓ hD hD' EΓ ED ED'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, hD⟩
    have hctx := IsDefEqCtx.succ .zero HDD.symm
    have Ectx := proofErase_defeqCtx (Γ₁ := D' :: Γ) ⟨hΓ, _, hD'⟩ hctx hC'
    rw [Ectx] at EC'
    have hC' := hC'.defeqDFC henv hctx
    have EΓD := congr (congrArg List.cons ED) EΓ
    change proofEraseCtx (D :: Γ) = _ at EΓD
    have hC := domain_sort_raw SC hΓD hC EΓD EC
    have hC' := domain_sort_raw SC' hΓD hC' EΓD EC'
    apply JointCheck.forallSorted (sort_context hΓ W EΓ SD) (sort_context hΓ W EΓ SD') (ihD hΓ hD hD' EΓ ED ED' W HO)
      (by simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using sort_context hΓD (.succ W hD) EΓD SC)
      (by simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using sort_context hΓD (.succ W hD) EΓD SC')
    simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using
      (ihC hΓD hC hC' EΓD EC EC' (.succ W hD) (oracle_cons_typed hΓ W hD ED HO))
  | etaBodyL SD HB ihB =>
    intro Γ Γ' a b A hΓ ha hb EΓ Ea Eb W HO
    obtain ⟨D, body, rfl, hn, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨⟨_, hD⟩, C, hbody⟩ := ha.lam_inv henv hΓ
    have hD := domain_sort_raw SD hΓ hD EΓ ED
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, hD⟩
    have hfPi := hb.defeqU_r henv hΓ (ha.uniqU henv hΓ (HasType.lam hD hbody))
    have hnf : ¬ IsProof Γ b := by
      rintro ⟨P, hfP, hP⟩
      exact hn ⟨P, ha.defeqU_r henv hΓ (hb.uniqU henv hΓ hfP), hP⟩
    have hη : env.HasType univs (D :: Γ) (.app b.lift (.bvar 0)) C := by
      simpa only [lift, VExpr.liftN, inst_liftN_bvar] using HasType.app (hfPi.weak henv (B := D)) (.bvar .zero)
    have Eη := proofErase_eta_body hΓ hD hfPi hnf
    rw [Eb] at Eη
    apply JointCheck.etaBodyL (sort_context hΓ W EΓ SD)
    simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using
      ihB hΓD hbody hη (by simp only [proofEraseCtx, EΓ, ED]) Ebody Eη (.succ W hD) (oracle_cons_typed hΓ W hD ED HO)
  | etaBodyR SD HB ihB =>
    intro Γ Γ' a b A hΓ ha hb EΓ Ea Eb W HO
    obtain ⟨D, body, rfl, hn, ED, Ebody⟩ := erase_lam_inv Eb
    obtain ⟨⟨_, hD⟩, C, hbody⟩ := hb.lam_inv henv hΓ
    have hD := domain_sort_raw SD hΓ hD EΓ ED
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, hD⟩
    have hfPi := ha.defeqU_r henv hΓ (hb.uniqU henv hΓ (HasType.lam hD hbody))
    have hnf : ¬ IsProof Γ a := by
      rintro ⟨P, hfP, hP⟩
      exact hn ⟨P, hb.defeqU_r henv hΓ (ha.uniqU henv hΓ hfP), hP⟩
    have hη : env.HasType univs (D :: Γ) (.app a.lift (.bvar 0)) C := by
      simpa only [lift, VExpr.liftN, inst_liftN_bvar] using HasType.app (hfPi.weak henv (B := D)) (.bvar .zero)
    have Eη := proofErase_eta_body hΓ hD hfPi hnf
    rw [Ea] at Eη
    apply JointCheck.etaBodyR (sort_context hΓ W EΓ SD)
    simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using
      ihB hΓD hη hbody (by simp only [proofEraseCtx, EΓ, ED]) Eη Ebody (.succ W hD) (oracle_cons_typed hΓ W hD ED HO)
  | @structFields Δ family info ls ps fields major hi hx hp hf hadm Hfields ihfields =>
    intro Γ Γ' a b A hΓ ha hb EΓ Ea Eb W HO
    have HE := common_raw hstep (.structFields hi hx hp hf hadm Hfields) hΓ ha hb EΓ Ea Eb
    apply JointCheck.structFields hi hx hp
      hf hadm
    intro i hj hn
    obtain ⟨x, X, hxt, hpt, Ex⟩ := proofErase_equal_structure_field_realize hΓ HE hi hx hp hf hadm Ea hj
    have hnx : ¬ IsProof Γ x := fun H => hn (Ex.symm.trans (proofErase_eq_proof.2 H))
    have hnp : ¬ IsProof Γ (.proj family i b) := by
      rintro ⟨P, hpP, hP⟩
      exact hnx ⟨P, hxt.defeqU_r henv hΓ (hpt.uniqU henv hΓ hpP), hP⟩
    have Ep : proofErase Γ (.proj family i b) = .proj family i major := by
      rw [show proofErase Γ (.proj family i b) = .proj family i (proofErase Γ b) from if_neg hnp, Eb]
    exact ihfields i hj hn hΓ hxt hpt EΓ Ex Ep W HO
  | compute Ra Rb HC ih =>
    intro Γ Γ' a b A hΓ ha hb EΓ Ea Eb W HO
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea Ra
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb Rb
    exact .compute (compute_context hsubst W EΓ Ra)
      (compute_context hsubst W EΓ Rb)
      (ih hΓ HA.hasType.2 HB.hasType.2 EΓ EA EB W HO)
  | symm HC ih =>
    intro Γ Γ' a b A hΓ ha hb EΓ Ea Eb W HO
    exact .symm (ih hΓ hb ha EΓ Eb Ea W HO)
  | carrierChecked HC ih =>
    intro Γ Γ' a b A hΓ ha hb EΓ Eα Ea Eb W HO
    exact .carrierChecked (ih hΓ ha hb EΓ Ea Eb W HO)
  | carrierSubsingleton HS =>
    intro Γ Γ' a b A hΓ ha hb EΓ Eα Ea Eb W HO
    exact .carrierSubsingleton HS
  | carrierSymm HC ih =>
    intro Γ Γ' a b A hΓ ha hb EΓ Eα Ea Eb W HO
    exact .carrierSymm (ih hΓ hb ha EΓ Eα Eb Ea W HO)
  | carrierCompute RC HC ih =>
    intro Γ Γ' a b A hΓ ha hb EΓ Eα Ea Eb W HO
    obtain ⟨u, hA⟩ := ha.isType henv hΓ
    obtain ⟨A', HE, EA⟩ := proofErase_scoped_compute_realize hstep hΓ hA EΓ Eα RC
    exact .carrierCompute (compute_context hsubst W EΓ RC)
      (ih hΓ (HE.defeq ha) (HE.defeq hb) EΓ EA Ea Eb W HO)
  | carrierReduce Ra Rb HC ih =>
    intro Γ Γ' a b A hΓ ha hb EΓ Eα Ea Eb W HO
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea Ra
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb Rb
    exact .carrierReduce (compute_context hsubst W EΓ Ra) (compute_context hsubst W EΓ Rb)
      (ih hΓ HA.hasType.2 HB.hasType.2 EΓ Eα EA EB W HO)
  | carrierFunction SD HC ih =>
    intro Γ Γ' a b A hΓ ha hb EΓ Eα Ea Eb W HO
    obtain ⟨D, C, rfl, _, ED, EC⟩ := erase_forallE_inv Eα
    obtain ⟨_, hPi⟩ := ha.isType henv hΓ
    obtain ⟨⟨_, hD⟩, _, _⟩ := hPi.forallE_inv henv
    have hD := domain_sort_raw SD hΓ hD EΓ ED
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, hD⟩
    by_cases hpa : IsProof Γ a
    · obtain ⟨P, haP, hP⟩ := hpa
      have hpb : IsProof Γ b := ⟨P, hb.defeqU_r henv hΓ (ha.uniqU henv hΓ haP), hP⟩
      rw [← Ea, ← Eb, proofErase_eq_proof.2 ⟨P, haP, hP⟩, proofErase_eq_proof.2 hpb]
      exact .carrierChecked (.leaf .refl)
    have hpb : ¬ IsProof Γ b := by
      rintro ⟨P, hbP, hP⟩
      exact hpa ⟨P, ha.defeqU_r henv hΓ (hb.uniqU henv hΓ hbP), hP⟩
    have hfa : env.HasType univs (D :: Γ) (.app a.lift (.bvar 0)) C := by
      simpa only [lift, VExpr.liftN, inst_liftN_bvar] using HasType.app (ha.weak henv) (.bvar .zero)
    have hfb : env.HasType univs (D :: Γ) (.app b.lift (.bvar 0)) C := by
      simpa only [lift, VExpr.liftN, inst_liftN_bvar] using HasType.app (hb.weak henv) (.bvar .zero)
    have Efa := proofErase_eta_body hΓ hD ha hpa
    have Efb := proofErase_eta_body hΓ hD hb hpb
    rw [Ea] at Efa
    rw [Eb] at Efb
    have H' := ih hΓD hfa hfb (by simp only [proofEraseCtx, EΓ, ED]) EC Efa Efb
      (.succ W hD) (oracle_cons_typed hΓ W hD ED HO)
    apply JointCheck.carrierFunction (sort_context hΓ W EΓ SD)
    simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using H'
  | @carrierIntro family info ls Δ sa sb ps hi hx hp hadm Hfields ihfields =>
    intro Γ Γ' a b A hΓ ha hb EΓ Eα Ea Eb W HO
    have HE := carrier_raw hstep (.carrierIntro hi hx hp hadm Hfields) hΓ ha hb EΓ Eα Ea Eb
    obtain ⟨args, rfl, Eargs⟩ := proofErase_const_spine_inv Eα
    have hlen : args.length = info.nparams := by
      have HH := congrArg List.length Eargs
      simp only [List.length_map] at HH
      omega
    have hexpa := (StructureReplay.expansion_typed_iff henv hΓ hi hlen hx ha).2 hadm
    apply JointCheck.carrierIntro hi hx hp hadm
    intro i hj hn
    obtain ⟨F, hia, hib⟩ := structure_equal_projection_typings hΓ HE hexpa hj
    have hpa : ¬ IsProof Γ (.proj family i a) := fun H =>
      hn (StructureReplay.ProofField.of_projection hΓ hi hlen hj hexpa H)
    have hpb : ¬ IsProof Γ (.proj family i b) := by
      rintro ⟨P, hibP, hP⟩
      exact hpa ⟨P, hia.defeqU_r henv hΓ (hib.uniqU henv hΓ hibP), hP⟩
    have Epa : proofErase Γ (.proj family i a) = .proj family i sa := by
      rw [show proofErase Γ (.proj family i a) = .proj family i (proofErase Γ a) from if_neg hpa, Ea]
    have Epb : proofErase Γ (.proj family i b) = .proj family i sb := by
      rw [show proofErase Γ (.proj family i b) = .proj family i (proofErase Γ b) from if_neg hpb, Eb]
    exact ihfields i hj hn hΓ hia hib EΓ Epa Epb W HO
  | @carrierNested family info ls doms result Δ ps sa sb hi hx hp hadm HT Hfields ihfields =>
    intro Γ Γ' a b A hΓ ha hb EΓ Eα Ea Eb W HO
    have HE := carrier_raw hstep (.carrierNested hi hx hp hadm HT Hfields) hΓ ha hb EΓ Eα Ea Eb
    obtain ⟨args, rfl, Eargs⟩ := proofErase_const_spine_inv Eα
    have hlen : args.length = info.nparams := by
      have HH := congrArg List.length Eargs
      simp only [List.length_map] at HH
      omega
    have hexpa := (StructureReplay.expansion_typed_iff henv hΓ hi hlen hx ha).2 hadm
    apply JointCheck.carrierNested hi hx hp hadm HT
    intro i hj hn
    obtain ⟨F, hia, hib⟩ := structure_equal_projection_typings hΓ HE hexpa hj
    have hpa : ¬ IsProof Γ (.proj family i a) := fun H =>
      hn (StructureReplay.ProofField.of_projection hΓ hi hlen hj hexpa H)
    have hpb : ¬ IsProof Γ (.proj family i b) := by
      rintro ⟨P, hibP, hP⟩
      exact hpa ⟨P, hia.defeqU_r henv hΓ (hib.uniqU henv hΓ hibP), hP⟩
    obtain ⟨hj', F', hiaF, EF⟩ := proofErase_projection_at_recovered_family hΓ hi HT hia hpa ha
    have hibF := hib.defeqU_r henv hΓ (hia.uniqU henv hΓ hiaF)
    have EF' : proofErase Γ F' = projectionType family info doms i hj' ps sa := by
      simpa only [projectionType, List.map_take, ← Eargs, Ea] using EF
    have Epa : proofErase Γ (.proj family i a) = .proj family i sa := by
      rw [show proofErase Γ (.proj family i a) = .proj family i (proofErase Γ a) from if_neg hpa, Ea]
    have Epb : proofErase Γ (.proj family i b) = .proj family i sb := by
      rw [show proofErase Γ (.proj family i b) = .proj family i (proofErase Γ b) from if_neg hpb, Eb]
    exact ihfields i hj hn hΓ hiaF hibF EΓ EF' Epa Epb W HO

/-- Replacing one binder by an equal closed rigid type transports both typed
joint modes. In carrier mode the original actual carrier is retained; its
erasure agrees in the two equal contexts. -/
theorem proofErase_joint_closed_binder
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hr : env.Rigid family) (hΓ : OnCtx Γ (env.IsType univs))
    (HE : env.IsDefEq univs Γ A (.const family []) (.sort u))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T) :
    (JointCompare Step (proofEraseCtx (A :: Γ)) mode
        (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) →
      JointCompare Step (proofEraseCtx (.const family [] :: Γ)) mode
        (proofErase (.const family [] :: Γ) a) (proofErase (.const family [] :: Γ) b)) ∧
    (JointCarrierGuard Step (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) T)
        (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) →
      JointCarrierGuard Step (proofEraseCtx (.const family [] :: Γ))
        (proofErase (.const family [] :: Γ) T)
        (proofErase (.const family [] :: Γ) a) (proofErase (.const family [] :: Γ) b)) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HE.hasType.1⟩
  have W : IsDefEqCtx env univs [] (A :: Γ) (.const family [] :: Γ) := .succ (.refl hΓ) HE
  have HO : ∀ i, RigidResultChange (contextOracle (proofEraseCtx (A :: Γ)) i)
      (contextOracle (proofEraseCtx (.const family [] :: Γ)) i) := by
    intro i
    cases i with
    | zero =>
      change RigidResultChange ((proofErase Γ A).liftN 1) ((proofErase Γ (.const family [])).liftN 1)
      rw [show proofErase Γ (.const family []) = .const family [] from
        if_neg (not_isProof_of_sort hΓ HE.hasType.2)]
      exact .closed hr
    | succ i => exact .refl
  constructor
  · intro H
    have H' := H.rigid_oracles hstep hsubst hhead hΓA ha hb rfl rfl rfl W HO
    rwa [proofErase_defeqCtx hΓA W ha, proofErase_defeqCtx hΓA W hb] at H'
  · intro H
    have H' := H.rigid_oracles hstep hsubst hhead hΓA ha hb rfl rfl rfl rfl W HO
    rwa [proofErase_defeqCtx hΓA W (ha.isType henv hΓA).choose_spec,
      proofErase_defeqCtx hΓA W ha, proofErase_defeqCtx hΓA W hb] at H'

/-- Certified primitives discharge the soundness and closure premises of
closed rigid binder transport for both typed joint modes. -/
theorem proofErase_certified_joint_closed_binder
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hr : env.Rigid family) (hΓ : OnCtx Γ (env.IsType univs))
    (HE : env.IsDefEq univs Γ A (.const family []) (.sort u))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T) :
    (JointCompare (ErasedBetaStableJoint D) (proofEraseCtx (A :: Γ)) mode
        (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) →
      JointCompare (ErasedBetaStableJoint D) (proofEraseCtx (.const family [] :: Γ)) mode
        (proofErase (.const family [] :: Γ) a) (proofErase (.const family [] :: Γ) b)) ∧
    (JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) T)
        (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) →
      JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx (.const family [] :: Γ))
        (proofErase (.const family [] :: Γ) T)
        (proofErase (.const family [] :: Γ) a) (proofErase (.const family [] :: Γ) b)) :=
  proofErase_joint_closed_binder (erased_beta_stable_joint_descent heq hs)
    erased_beta_stable_joint_head (erased_beta_stable_joint_subst heq hs) hr hΓ HE ha hb

end Lean4Lean.VEnv.Strengthening
