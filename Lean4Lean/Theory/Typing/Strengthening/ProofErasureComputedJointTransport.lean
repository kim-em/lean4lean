import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointFieldRealization
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointDescent

/-! # A shared typed transport induction for joint checking

Context transport, computation transport, and selected-domain transport are
separate inputs. Native recovery may be replaced by computation of a lambda
at the exact selected domain. The computed-domain rule itself transports
recursively without an additional recovery premise.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

private theorem infer_raw (hstep : ErasedScopedPrimitiveDescent Step)
    (H : ComputedJointCompare Step Δ false sa sb) (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb)
    (hna : ¬ IsProof Γ a) (hnb : ¬ IsProof Γ b) : env.IsDefEq univs Γ a b A :=
  ((proofErase_computed_joint_compare_reflect hstep hΓ ha hb
    (by simpa only [EΓ, Ea, Eb] using H)).2 rfl hna hnb).of_l henv hΓ ha

private theorem common_raw (hstep : ErasedScopedPrimitiveDescent Step)
    (H : ComputedJointCompare Step Δ mode sa sb) (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb) :
    env.IsDefEq univs Γ a b A :=
  ((proofErase_computed_joint_compare_reflect hstep hΓ ha hb
    (by simpa only [EΓ, Ea, Eb] using H)).1 ⟨_, ha.isType henv hΓ |>.choose_spec⟩).of_l henv hΓ ha

private theorem carrier_raw (hstep : ErasedScopedPrimitiveDescent Step)
    (H : ComputedJointCarrierGuard Step Δ α sa sb) (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (EΓ : proofEraseCtx Γ = Δ) (Eα : proofErase Γ A = α)
    (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb) : env.IsDefEq univs Γ a b A :=
  proofErase_computed_joint_carrier_reflect hstep hΓ ha hb (by simpa only [EΓ, Eα, Ea, Eb] using H)

private theorem domain_sort_raw (S : DomainSort Δ raw u)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ A (.sort v))
    (EΓ : proofEraseCtx Γ = Δ) (EA : proofErase Γ A = raw) : env.HasType univs Γ A (.sort u) :=
  DomainSort.descend (by simpa only [ProofShape.liftN_zero, EΓ, EA] using S)
    hΓ hΓ (show Ctx.LiftN 0 0 Γ Γ from .zero []) ht

private theorem lambda_common_context (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ (.lam D a) T) (hb : env.HasType univs Γ (.lam D' b) T) :
    ∃ u C, env.HasType univs Γ D (.sort u) ∧ env.HasType univs Γ D' (.sort u) ∧
      env.HasType univs (D :: Γ) a C ∧ env.HasType univs (D :: Γ) b C ∧
      proofErase (D' :: Γ) b = proofErase (D :: Γ) b := by
  obtain ⟨⟨u, hD⟩, C, hbody⟩ := ha.lam_inv henv hΓ
  obtain ⟨⟨v, hD'⟩, C', hbody'⟩ := hb.lam_inv henv hΓ
  have HPi := (ha.uniqU henv hΓ (HasType.lam hD hbody)).symm.trans henv hΓ
    (hb.uniqU henv hΓ (HasType.lam hD' hbody'))
  obtain ⟨⟨_, HDD⟩, _, HCC⟩ := HPi.forallE_inv henv hΓ
  have HD := (show env.IsDefEqU univs Γ D D' from ⟨_, HDD⟩).of_l henv hΓ hD
  have hctx := IsDefEqCtx.succ .zero HD.symm
  have EB := proofErase_defeqCtx (Γ₁ := D' :: Γ) ⟨hΓ, v, hD'⟩ hctx hbody'
  exact ⟨u, C, hD, HD.hasType.2, hbody,
    HCC.symm.defeq (hbody'.defeqDFC henv hctx), EB⟩

/-- Typed interpretation of joint checking transport in each checking mode. -/
def ComputedJointTransportResult (Transport : List ProofShape → List ProofShape → ProofShape.Subst → Prop)
    (Target : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (kind : JointCheckKind) (sa sb : ProofShape) : Prop :=
  match kind with
  | .compare mode => ∀ {Γ a b A Δ' τ}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ a A → env.HasType univs Γ b A → proofEraseCtx Γ = Δ →
      proofErase Γ a = sa → proofErase Γ b = sb → Transport Δ Δ' τ →
      ComputedJointCompare Target Δ' mode (sa.subst τ) (sb.subst τ)
  | .carrier α => ∀ {Γ a b A Δ' τ}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ a A → env.HasType univs Γ b A → proofEraseCtx Γ = Δ →
      proofErase Γ A = α → proofErase Γ a = sa → proofErase Γ b = sb →
      Transport Δ Δ' τ → ComputedJointCarrierGuard Target Δ' (α.subst τ) (sa.subst τ) (sb.subst τ)

/-- One induction handles every joint checking constructor. The supplied
application case preserves the selected domain by native recovery or lambda
computation. Both comparison and carrier premises are transported recursively,
including beneath arbitrarily many computed-domain applications. -/
theorem ProofShape.ComputedJointCheck.transport
    (Transport : List ProofShape → List ProofShape → ProofShape.Subst → Prop)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hcons : ∀ {Δ Δ' τ A}, Transport Δ Δ' τ → Transport (A :: Δ) (A.subst τ :: Δ') τ.lift)
    (hsort : ∀ {Δ Δ' τ A u}, Transport Δ Δ' τ → DomainSort Δ A u → DomainSort Δ' (A.subst τ) u)
    (hcompute : ∀ {Γ Δ Δ' τ e T source out}, ScopedCompute Step Δ source out →
      OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      proofEraseCtx Γ = Δ → proofErase Γ e = source → Transport Δ Δ' τ →
      ScopedCompute Target Δ' (source.subst τ) (out.subst τ))
    (happ : ∀ {Γ Δ' τ f D C A B}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ f (.forallE D C) → ¬ IsProof Γ f →
      ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) (.forallE A B) →
      Transport (proofEraseCtx Γ) Δ' τ →
      ScopedTypeRecovery Target Δ' ((proofErase Γ f).subst τ)
        (.forallE (A.subst τ) (B.subst τ.lift)) ∨
      ∃ body, ScopedCompute Target Δ' ((proofErase Γ f).subst τ) (.lam (A.subst τ) body))
    (H : ComputedJointCheck Step Δ kind sa sb) : ComputedJointTransportResult Transport Target Δ kind sa sb := by
  induction H with
  | leaf H =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
    exact .leaf H.subst
  | app HF HX ihf ihx =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
    obtain ⟨f, x, rfl, hna, Ef, Ex⟩ := erase_app_inv Ea
    obtain ⟨g, y, rfl, hnb, Eg, Ey⟩ := erase_app_inv Eb
    obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
    obtain ⟨_, _, hg, hy⟩ := hb.app_inv henv hΓ
    have HE := infer_raw hstep HF hΓ hf hg EΓ Ef Eg
      (not_isProof_fn hΓ hf hx hna) (not_isProof_fn hΓ hg hy hnb)
    have hy' := argument_at_displayed_domain hΓ hg HE.hasType.2 hy
    exact .app (ihf hΓ hf HE.hasType.2 EΓ Ef Eg W) (ihx hΓ hx hy' EΓ Ex Ey W)
  | appCarrier R HF HX ihf ihx =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
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
    have HX' := ihx hΓ hxD hyD EΓ (by simpa only [ProofShape.liftN_zero] using ED) Ex Ey W
    have HF' := ihf hΓ hf HE.hasType.2 EΓ Ef Eg W
    rcases happ hΓ hfPi (not_isProof_fn hΓ hf hx hna)
        (by simpa only [EΓ, Ef] using R) (by simpa only [EΓ] using W) with
      HR | ⟨body, RF⟩
    · exact .appCarrier (by simpa only [Ef] using HR) HF' HX'
    · exact .appComputed (by simpa only [Ef] using RF) HF' HX'
  | appComputed RF HF HX ihf ihx =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
    obtain ⟨f, x, rfl, hna, Ef, Ex⟩ := erase_app_inv Ea
    obtain ⟨g, y, rfl, hnb, Eg, Ey⟩ := erase_app_inv Eb
    obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
    obtain ⟨_, _, hg, hy⟩ := hb.app_inv henv hΓ
    have HE := infer_raw hstep HF hΓ hf hg EΓ Ef Eg
      (not_isProof_fn hΓ hf hx hna) (not_isProof_fn hΓ hg hy hnb)
    obtain ⟨f', HE', EF'⟩ := proofErase_scoped_compute_realize hstep hΓ hf EΓ Ef RF
    obtain ⟨D, body, rfl, _, ED, _⟩ := erase_lam_inv EF'
    obtain ⟨⟨_, hD⟩, _, hbody⟩ := HE'.hasType.2.lam_inv henv hΓ
    have hfPi := (HE'.toU.of_r henv hΓ (HasType.lam hD hbody)).hasType.1
    have hgPi := HE.toU.of_l henv hΓ hfPi |>.hasType.2
    have hxD := argument_at_displayed_domain hΓ hf hfPi hx
    have hyD := argument_at_displayed_domain hΓ hg hgPi hy
    exact .appComputed (hcompute RF hΓ hf EΓ Ef W)
      (ihf hΓ hf HE.hasType.2 EΓ Ef Eg W) (ihx hΓ hxD hyD EΓ ED Ex Ey W)
  | proj HM ihm =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
    obtain ⟨m, rfl, hn, Em⟩ := erase_proj_inv Ea
    obtain ⟨m', rfl, hn', Em'⟩ := erase_proj_inv Eb
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm', _, _⟩ := hb.proj_inv henv hΓ
    have HE := infer_raw hstep HM hΓ hm.hasType.2 hm'.hasType.2 EΓ Em Em'
      (not_isProof_major hΓ ha hn) (not_isProof_major hΓ hb hn')
    exact .proj (ihm hΓ hm.hasType.2 HE.hasType.2 EΓ Em Em' W)
  | lam HD HB ihD ihB =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HB' := ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED]) Ebody Ebody' (hcons W)
    exact .lam (ihD hΓ hD hD' EΓ ED ED' W) HB'
  | lamSorted SD SD' HD HB ihD ihB =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HB' := ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED]) Ebody Ebody' (hcons W)
    exact .lamSorted (hsort W SD) (hsort W SD') (ihD hΓ hD hD' EΓ ED ED' W) HB'
  | lamCommon HB ihB =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HB' := ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED]) Ebody Ebody' (hcons W)
    exact .lamCommon HB'
  | etaLams HD Hη ihD =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    exact .etaLams (ihD hΓ hD hD' EΓ ED ED' W) (Hη.imp (fun H => H.subst) (fun H => H.subst))
  | forallE HD HC ihD ihC =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
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
    exact .forallE (ihD hΓ hD HDD.hasType.2 EΓ ED ED' W)
      (ihC hΓD hC HCC.hasType.2 EΓD EC EC' (hcons W))
  | forallSorted SD SD' HD SC SC' HC ihD ihC =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
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
    exact .forallSorted (hsort W SD) (hsort W SD') (ihD hΓ hD hD' EΓ ED ED' W)
      (hsort (hcons W) SC) (hsort (hcons W) SC')
      (ihC hΓD hC hC' EΓD EC EC' (hcons W))
  | etaBodyL SD HB ihB =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
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
    apply ComputedJointCheck.etaBodyL (hsort W SD)
    simpa only [ProofShape.subst, etaArgument_subst, ProofShape.lift_subst_lift] using
      ihB hΓD hbody hη (by simp only [proofEraseCtx, EΓ, ED]) Ebody Eη (hcons W)
  | etaBodyR SD HB ihB =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
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
    apply ComputedJointCheck.etaBodyR (hsort W SD)
    simpa only [ProofShape.subst, etaArgument_subst, ProofShape.lift_subst_lift] using
      ihB hΓD hη hbody (by simp only [proofEraseCtx, EΓ, ED]) Eη Ebody (hcons W)
  | @structFields Δ family info ls ps fields major hi hx hp hf hadm Hfields ihfields =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
    have HE := common_raw hstep (.structFields hi hx hp hf hadm Hfields) hΓ ha hb EΓ Ea Eb
    simp only [ProofShape.subst_mkApps, ProofShape.subst, List.map_append]
    apply ComputedJointCheck.structFields hi hx (by simpa only [List.length_map] using hp)
      (by simpa only [List.length_map] using hf) hadm
    intro i hj hn
    have hj₀ : i < fields.length := by simpa only [List.length_map] using hj
    have hn₀ : fields[i] ≠ .proof := by
      intro HE
      apply hn
      simp only [List.getElem_map, HE, ProofShape.subst]
    obtain ⟨x, X, hxt, hpt, Ex⟩ := proofErase_equal_structure_field_realize hΓ HE hi hx hp hf hadm Ea hj₀
    have hnx : ¬ IsProof Γ x := fun H => hn₀ (Ex.symm.trans (proofErase_eq_proof.2 H))
    have hnp : ¬ IsProof Γ (.proj family i b) := by
      rintro ⟨P, hpP, hP⟩
      exact hnx ⟨P, hxt.defeqU_r henv hΓ (hpt.uniqU henv hΓ hpP), hP⟩
    have Ep : proofErase Γ (.proj family i b) = .proj family i major := by
      rw [show proofErase Γ (.proj family i b) = .proj family i (proofErase Γ b) from if_neg hnp, Eb]
    simpa only [List.getElem_map, ProofShape.subst] using
      ihfields i hj₀ hn₀ hΓ hxt hpt EΓ Ex Ep W
  | compute Ra Rb HC ih =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea Ra
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb Rb
    exact .compute (hcompute Ra hΓ ha EΓ Ea W)
      (hcompute Rb hΓ hb EΓ Eb W)
      (ih hΓ HA.hasType.2 HB.hasType.2 EΓ EA EB W)
  | symm HC ih =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
    exact .symm (ih hΓ hb ha EΓ Eb Ea W)
  | carrierChecked HC ih =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Eα Ea Eb W
    exact .carrierChecked (ih hΓ ha hb EΓ Ea Eb W)
  | carrierSubsingleton HS =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Eα Ea Eb W
    exact .carrierSubsingleton (HS.subst τ)
  | carrierSymm HC ih =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Eα Ea Eb W
    exact .carrierSymm (ih hΓ hb ha EΓ Eα Eb Ea W)
  | carrierCompute RC HC ih =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Eα Ea Eb W
    obtain ⟨u, hA⟩ := ha.isType henv hΓ
    obtain ⟨A', HE, EA⟩ := proofErase_scoped_compute_realize hstep hΓ hA EΓ Eα RC
    exact .carrierCompute (hcompute RC hΓ hA EΓ Eα W)
      (ih hΓ (HE.defeq ha) (HE.defeq hb) EΓ EA Ea Eb W)
  | carrierReduce Ra Rb HC ih =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Eα Ea Eb W
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea Ra
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb Rb
    exact .carrierReduce (hcompute Ra hΓ ha EΓ Ea W)
      (hcompute Rb hΓ hb EΓ Eb W)
      (ih hΓ HA.hasType.2 HB.hasType.2 EΓ Eα EA EB W)
  | carrierFunction SD HC ih =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Eα Ea Eb W
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
    apply ComputedJointCheck.carrierFunction (hsort W SD)
    simpa only [ProofShape.subst, etaArgument_subst, ProofShape.lift_subst_lift] using
      ih hΓD hfa hfb (by simp only [proofEraseCtx, EΓ, ED]) EC Efa Efb (hcons W)
  | @carrierIntro family info ls Δ sa sb ps hi hx hp hadm Hfields ihfields =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Eα Ea Eb W
    have HE := carrier_raw hstep (.carrierIntro hi hx hp hadm Hfields) hΓ ha hb EΓ Eα Ea Eb
    obtain ⟨args, rfl, Eargs⟩ := proofErase_const_spine_inv Eα
    have hlen : args.length = info.nparams := by
      have HH := congrArg List.length Eargs
      simp only [List.length_map] at HH
      omega
    have hexpa := (StructureReplay.expansion_typed_iff henv hΓ hi hlen hx ha).2 hadm
    simp only [ProofShape.subst_mkApps, ProofShape.subst]
    apply ComputedJointCheck.carrierIntro hi hx (by simpa only [List.length_map] using hp) hadm
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
    exact ihfields i hj hn hΓ hia hib EΓ Epa Epb W
  | @carrierNested family info ls doms result Δ ps sa sb hi hx hp hadm HT Hfields ihfields =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Eα Ea Eb W
    have HE := carrier_raw hstep (.carrierNested hi hx hp hadm HT Hfields) hΓ ha hb EΓ Eα Ea Eb
    obtain ⟨args, rfl, Eargs⟩ := proofErase_const_spine_inv Eα
    have hlen : args.length = info.nparams := by
      have HH := congrArg List.length Eargs
      simp only [List.length_map] at HH
      omega
    have hexpa := (StructureReplay.expansion_typed_iff henv hΓ hi hlen hx ha).2 hadm
    simp only [ProofShape.subst_mkApps, ProofShape.subst]
    apply ComputedJointCheck.carrierNested hi hx (by simpa only [List.length_map] using hp) hadm HT
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
    simpa only [projectionType_subst (args := ps) HT _ (by omega), ProofShape.subst] using
      ihfields i hj hn hΓ hiaF hibF EΓ EF' Epa Epb W


end Lean4Lean.VEnv.Strengthening
