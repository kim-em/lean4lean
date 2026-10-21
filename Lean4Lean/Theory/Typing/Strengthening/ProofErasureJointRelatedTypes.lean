import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRelatedRecovery

/-! # All joint checking from local type-relation laws

The local laws suffice for simultaneous recovery, context and carrier
transport. Record parameters may change for any registered family satisfying
the field-recipe law, including templates dependent on previous projections.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private infer_raw common_raw carrier_raw domain_sort_raw lambda_common_context
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointTransport
open private oracle_cons_related
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRelatedRecovery
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

private theorem oracle_cons_typed (L : TypeChangeLaws Step Rel)
    (hΓ : OnCtx Γ (env.IsType univs)) (W : IsDefEqCtx env univs [] Γ Γ')
    (hD : env.HasType univs Γ D (.sort u))
    (ED : proofErase Γ D = d)
    (HO : ∀ i, Rel k (contextOracle Δ i) (contextOracle (proofEraseCtx Γ') i)) :
    ∀ i, Rel (k + 1) (contextOracle (d :: Δ) i)
      (contextOracle (proofEraseCtx (D :: Γ')) i) := by
  simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using oracle_cons_related L HO

/-- Simultaneous transport target for a proposed relation on types. Actual
context conversion and type equality are supplied separately from that relation.
Expression endpoints stay fixed while oracles and carrier types may change. -/
def JointRelatedResult (Rel : Nat → ProofShape → ProofShape → Prop)
    (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (kind : JointCheckKind) (sa sb : ProofShape) : Prop :=
  match kind with
  | .compare mode => ∀ {Γ Γ' a b A k}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ a A → env.HasType univs Γ b A → proofEraseCtx Γ = Δ →
      proofErase Γ a = sa → proofErase Γ b = sb → IsDefEqCtx env univs [] Γ Γ' →
      (∀ i, Rel k (contextOracle Δ i) (contextOracle (proofEraseCtx Γ') i)) →
      JointCompare Step (proofEraseCtx Γ') mode sa sb
  | .carrier α => ∀ {Γ Γ' a b A k}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ a A → env.HasType univs Γ b A → proofEraseCtx Γ = Δ →
      proofErase Γ A = α → proofErase Γ a = sa → proofErase Γ b = sb →
      IsDefEqCtx env univs [] Γ Γ' →
      (∀ i, Rel k (contextOracle Δ i) (contextOracle (proofEraseCtx Γ') i)) →
      ∀ {B}, env.IsDefEqU univs Γ A B → Rel k α (proofErase Γ B) →
      JointCarrierGuard Step (proofEraseCtx Γ') (proofErase Γ B) sa sb

/-- Local structural type-relation laws imply transport for every joint
constructor. Recovery is derived from the same laws. The smaller carrier
derivations handle changed application domains and dependent record fields;
no global recovery, comparison or carrier transport is assumed. -/
theorem ProofShape.JointCheck.related_types
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (L : TypeChangeLaws Step Rel)
    (H : JointCheck Step Δ kind sa sb) : JointRelatedResult Rel Step Δ kind sa sb := by
  induction H with
  | leaf H =>
    intro Γ Γ' a b A k hΓ ha hb EΓ Ea Eb W HO
    exact .leaf H
  | app HF HX ihf ihx =>
    intro Γ Γ' a b A k hΓ ha hb EΓ Ea Eb W HO
    obtain ⟨f, x, rfl, hna, Ef, Ex⟩ := erase_app_inv Ea
    obtain ⟨g, y, rfl, hnb, Eg, Ey⟩ := erase_app_inv Eb
    obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
    obtain ⟨_, _, hg, hy⟩ := hb.app_inv henv hΓ
    have HE := infer_raw hstep HF hΓ hf hg EΓ Ef Eg
      (not_isProof_fn hΓ hf hx hna) (not_isProof_fn hΓ hg hy hnb)
    have hy' := argument_at_displayed_domain hΓ hg HE.hasType.2 hy
    exact .app (ihf hΓ hf HE.hasType.2 EΓ Ef Eg W HO) (ihx hΓ hx hy' EΓ Ex Ey W HO)
  | appCarrier R HF HX ihf ihx =>
    intro Γ Γ' a b A k hΓ ha hb EΓ Ea Eb W HO
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
    obtain ⟨out', R', RT⟩ := proofErase_recovery_type_change hstep hsubst L R
      hΓ hfPi EΓ Ef W HO
    obtain ⟨A', B', rfl, RA, _⟩ := L.pi_inv RT
    have hΓ' := (W.symm henv.ordered).isType
    have hf' := hfPi.defeqDFC henv W
    have Ef' := (proofErase_defeqCtx hΓ W hfPi).symm.trans Ef
    obtain ⟨D', C', hfPi', ED', EC'⟩ := proofErase_scoped_recovered_pi_descend hstep hΓ' hΓ'
      (show Ctx.LiftN 0 0 Γ' Γ' from .zero []) hf'
      (by simpa only [ProofShape.liftN_zero, Ef'] using R')
    simp only [ProofShape.liftN_zero] at ED EC ED' EC'
    have hfPi'' := hfPi'.defeqDFC henv (W.symm henv.ordered)
    obtain ⟨⟨u, HDD⟩, _⟩ := (hfPi.uniqU henv hΓ hfPi'').forallE_inv henv hΓ
    have EDu := (proofErase_defeqCtx hΓ W HDD.hasType.2).trans ED'
    have HX' := ihx hΓ hxD hyD EΓ ED Ex Ey W HO HDD.toU (EDu.symm ▸ RA)
    rw [EDu] at HX'
    exact .appCarrier R' (ihf hΓ hf HE.hasType.2 EΓ Ef Eg W HO) HX'
  | proj HM ihm =>
    intro Γ Γ' a b A k hΓ ha hb EΓ Ea Eb W HO
    obtain ⟨m, rfl, hn, Em⟩ := erase_proj_inv Ea
    obtain ⟨m', rfl, hn', Em'⟩ := erase_proj_inv Eb
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm', _, _⟩ := hb.proj_inv henv hΓ
    have HE := infer_raw hstep HM hΓ hm.hasType.2 hm'.hasType.2 EΓ Em Em'
      (not_isProof_major hΓ ha hn) (not_isProof_major hΓ hb hn')
    exact .proj (ihm hΓ hm.hasType.2 HE.hasType.2 EΓ Em Em' W HO)
  | lam HD HB ihD ihB =>
    intro Γ Γ' a b A k hΓ ha hb EΓ Ea Eb W HO
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HB' := ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED])
      Ebody Ebody' (.succ W hD) (oracle_cons_typed L hΓ W hD ED HO)
    apply JointCheck.lam (ihD hΓ hD hD' EΓ ED ED' W HO)
    simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using HB'
  | lamSorted SD SD' HD HB ihD ihB =>
    intro Γ Γ' a b A k hΓ ha hb EΓ Ea Eb W HO
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HB' := ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED])
      Ebody Ebody' (.succ W hD) (oracle_cons_typed L hΓ W hD ED HO)
    apply JointCheck.lamSorted (sort_context hΓ W EΓ SD) (sort_context hΓ W EΓ SD') (ihD hΓ hD hD' EΓ ED ED' W HO)
    simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using HB'
  | lamCommon HB ihB =>
    intro Γ Γ' a b A k hΓ ha hb EΓ Ea Eb W HO
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HB' := ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED])
      Ebody Ebody' (.succ W hD) (oracle_cons_typed L hΓ W hD ED HO)
    apply JointCheck.lamCommon
    simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using HB'
  | etaLams HD Hη ihD =>
    intro Γ Γ' a b A k hΓ ha hb EΓ Ea Eb W HO
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    exact .etaLams (ihD hΓ hD hD' EΓ ED ED' W HO) (Hη.imp (fun H => H) (fun H => H))
  | forallE HD HC ihD ihC =>
    intro Γ Γ' a b A k hΓ ha hb EΓ Ea Eb W HO
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
      (ihC hΓD hC HCC.hasType.2 EΓD EC EC' (.succ W hD) (oracle_cons_typed L hΓ W hD ED HO))
  | forallSorted SD SD' HD SC SC' HC ihD ihC =>
    intro Γ Γ' a b A k hΓ ha hb EΓ Ea Eb W HO
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
      (ihC hΓD hC hC' EΓD EC EC' (.succ W hD) (oracle_cons_typed L hΓ W hD ED HO))
  | etaBodyL SD HB ihB =>
    intro Γ Γ' a b A k hΓ ha hb EΓ Ea Eb W HO
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
      ihB hΓD hbody hη (by simp only [proofEraseCtx, EΓ, ED]) Ebody Eη (.succ W hD) (oracle_cons_typed L hΓ W hD ED HO)
  | etaBodyR SD HB ihB =>
    intro Γ Γ' a b A k hΓ ha hb EΓ Ea Eb W HO
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
      ihB hΓD hη hbody (by simp only [proofEraseCtx, EΓ, ED]) Eη Ebody (.succ W hD) (oracle_cons_typed L hΓ W hD ED HO)
  | @structFields Δ family info ls ps fields major hi hx hp hf hadm Hfields ihfields =>
    intro Γ Γ' a b A k hΓ ha hb EΓ Ea Eb W HO
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
    intro Γ Γ' a b A k hΓ ha hb EΓ Ea Eb W HO
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea Ra
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb Rb
    exact .compute (compute_context hsubst W EΓ Ra)
      (compute_context hsubst W EΓ Rb)
      (ih hΓ HA.hasType.2 HB.hasType.2 EΓ EA EB W HO)
  | symm HC ih =>
    intro Γ Γ' a b A k hΓ ha hb EΓ Ea Eb W HO
    exact .symm (ih hΓ hb ha EΓ Eb Ea W HO)
  | carrierChecked HC ih =>
    intro Γ Γ' a b A k hΓ ha hb EΓ Eα Ea Eb W HO B HAB HT
    exact .carrierChecked (ih hΓ ha hb EΓ Ea Eb W HO)
  | carrierSubsingleton HS =>
    intro Γ Γ' a b A k hΓ ha hb EΓ Eα Ea Eb W HO B HAB HT
    exact .carrierSubsingleton (L.subsingleton HT HS)
  | carrierSymm HC ih =>
    intro Γ Γ' a b A k hΓ ha hb EΓ Eα Ea Eb W HO B HAB HT
    exact .carrierSymm (ih hΓ hb ha EΓ Eα Eb Ea W HO HAB HT)
  | carrierCompute RC HC ih =>
    intro Γ Γ' a b A k hΓ ha hb EΓ Eα Ea Eb W HO B HAB HT
    obtain ⟨u, hA⟩ := ha.isType henv hΓ
    have HAB := HAB.of_l henv hΓ hA
    obtain ⟨A', HE, EA⟩ := proofErase_scoped_compute_realize hstep hΓ hA EΓ Eα RC
    obtain ⟨target, RB, HR⟩ := L.compute HT hΓ HAB Eα rfl
      (by simpa only [EΓ] using RC)
    obtain ⟨B', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ HAB.hasType.2 rfl rfl RB
    have HC' := ih hΓ (HE.defeq ha) (HE.defeq hb) EΓ EA Ea Eb W HO
      ((HE.symm.trans HAB).trans HB).toU (EB.symm ▸ HR)
    rw [EB] at HC'
    exact .carrierCompute (compute_context hsubst W rfl RB) HC'
  | carrierReduce Ra Rb HC ih =>
    intro Γ Γ' a b A k hΓ ha hb EΓ Eα Ea Eb W HO B HAB HT
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea Ra
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb Rb
    exact .carrierReduce (compute_context hsubst W EΓ Ra) (compute_context hsubst W EΓ Rb)
      (ih hΓ HA.hasType.2 HB.hasType.2 EΓ Eα EA EB W HO HAB HT)
  | carrierFunction SD HC ih =>
    intro Γ Γ' a b A k hΓ ha hb EΓ Eα Ea Eb W HO B HAB HT
    obtain ⟨rawD', rawC', ET, HD, HB⟩ := L.pi_inv HT
    obtain ⟨D, C, rfl, _, ED, EC⟩ := erase_forallE_inv Eα
    obtain ⟨D', C', rfl, _, ED', EC'⟩ := erase_forallE_inv ET
    obtain ⟨_, hPi⟩ := ha.isType henv hΓ
    obtain ⟨⟨_, hD⟩, _, _⟩ := hPi.forallE_inv henv
    have hD := domain_sort_raw SD hΓ hD EΓ ED
    obtain ⟨⟨_, Hdom⟩, ⟨_, Hcod⟩⟩ := HAB.forallE_inv henv hΓ
    have Hdom := Hdom.toU.of_l henv hΓ hD
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, hD⟩
    have W' := IsDefEqCtx.succ W Hdom
    have hctx := IsDefEqCtx.succ .zero Hdom
    have Ebody := (proofErase_defeqCtx hΓD hctx Hcod.hasType.2).trans EC'
    have EDom := (proofErase_defeqCtx hΓ W Hdom.hasType.2).symm.trans ED'
    have HO' : ∀ i, Rel (k + 1)
        (contextOracle (proofEraseCtx (D :: Γ)) i)
        (contextOracle (proofEraseCtx (D' :: Γ')) i) := by
      intro i
      cases i with
      | zero =>
        change Rel _ ((proofErase Γ D).liftN 1) ((proofErase Γ' D').liftN 1)
        rw [ED, EDom]
        exact L.shift HD
      | succ i =>
        change Rel _ ((contextOracle (proofEraseCtx Γ) i).liftN 1)
          ((contextOracle (proofEraseCtx Γ') i).liftN 1)
        rw [EΓ]
        exact L.shift (HO i)
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
    have H' := ih hΓD hfa hfb (by simp only [proofEraseCtx, EΓ, ED]) EC Efa Efb W'
      (by simpa only [proofEraseCtx, EΓ, ED] using HO') Hcod.toU (Ebody.symm ▸ HB)
    rw [Ebody] at H'
    rw [ET]
    apply JointCheck.carrierFunction ⟨Γ', D', (W.symm henv.ordered).isType, rfl,
      Hdom.hasType.2.defeqDFC henv W, EDom⟩
    simpa only [proofEraseCtx, EDom] using H'
  | @carrierIntro family info ls Δ sa sb ps hi hx hp hadm Hfields ihfields =>
    intro Γ Γ' a b A k hΓ ha hb EΓ Eα Ea Eb W HO B HAB HTy
    obtain ⟨ps', ET, hlen'⟩ := L.record hi HTy
    rw [ET]
    have HE := carrier_raw hstep (.carrierIntro hi hx hp hadm Hfields) hΓ ha hb EΓ Eα Ea Eb
    obtain ⟨args, rfl, Eargs⟩ := proofErase_const_spine_inv Eα
    have hlen : args.length = info.nparams := by
      have HH := congrArg List.length Eargs
      simp only [List.length_map] at HH
      omega
    have hexpa := (StructureReplay.expansion_typed_iff henv hΓ hi hlen hx ha).2 hadm
    apply JointCheck.carrierIntro hi hx (hlen'.trans hp) hadm
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
    intro Γ Γ' a b A k hΓ ha hb EΓ Eα Ea Eb W HO B HAB HTy
    obtain ⟨ps', ET, hlen'⟩ := L.record hi HTy
    have Hrecipes := L.field hi HT (ET ▸ HTy)
    rw [ET]
    obtain ⟨argsB, rfl, EargsB⟩ := proofErase_const_spine_inv ET
    have haB := ha.defeqU_r henv hΓ HAB
    have HE := carrier_raw hstep (.carrierNested hi hx hp hadm HT Hfields) hΓ ha hb EΓ Eα Ea Eb
    obtain ⟨args, rfl, Eargs⟩ := proofErase_const_spine_inv Eα
    have hlen : args.length = info.nparams := by
      have HH := congrArg List.length Eargs
      simp only [List.length_map] at HH
      omega
    have hexpa := (StructureReplay.expansion_typed_iff henv hΓ hi hlen hx ha).2 hadm
    apply JointCheck.carrierNested hi hx (hlen'.trans hp) hadm HT
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
    obtain ⟨hjB, FB, hiaB, EFB⟩ := proofErase_projection_at_recovered_family hΓ hi HT hia hpa haB
    have EFB' : proofErase Γ FB = projectionType family info doms i hjB ps' sa := by
      simpa only [projectionType, List.map_take, ← EargsB, Ea] using EFB
    have HR := Hrecipes i hj' sa
    rw [← EF', ← EFB'] at HR
    have H' := ihfields i hj hn hΓ hiaF hibF EΓ EF' Epa Epb W HO
      (hiaF.uniqU henv hΓ hiaB) (EF' ▸ HR)
    simpa only [EFB'] using H'

/-- In a fixed context, the local laws suffice to reindex every typed carrier
along the proposed type relation and an independently supplied actual equality. -/
theorem proofErase_joint_related_carrier
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (L : TypeChangeLaws Step Rel)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (HAB : env.IsDefEqU univs Γ A B)
    (HT : Rel k (proofErase Γ A) (proofErase Γ B))
    (H : JointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ A)
      (proofErase Γ a) (proofErase Γ b)) :
    JointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ B)
      (proofErase Γ a) (proofErase Γ b) :=
  H.related_types hstep hsubst L hΓ ha hb rfl rfl rfl rfl
    (.refl hΓ) (fun _ => L.refl) HAB HT

/-- A binder whose types satisfy the relation may be changed in every typed
body comparison. Only forward context conversion is used. No monotonicity or
symmetry of the proposed relation is required. -/
theorem proofErase_joint_related_context
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (L : TypeChangeLaws Step Rel)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HT : Rel k (proofErase Γ A) (proofErase Γ B))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : JointCompare Step (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    JointCompare Step (proofEraseCtx (B :: Γ)) mode
      (proofErase (B :: Γ) a) (proofErase (B :: Γ) b) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  have W : IsDefEqCtx env univs [] (A :: Γ) (B :: Γ) := .succ (.refl hΓ) HAB
  have HO : ∀ i, Rel (k + 1) (contextOracle (proofEraseCtx (A :: Γ)) i)
      (contextOracle (proofEraseCtx (B :: Γ)) i) := by
    intro i
    cases i with
    | zero => exact L.shift HT
    | succ i => exact L.refl
  have HC := H.related_types hstep hsubst L hΓA ha hb rfl rfl rfl W HO
  rwa [proofErase_defeqCtx hΓA W ha, proofErase_defeqCtx hΓA W hb] at HC

end Lean4Lean.VEnv.Strengthening
