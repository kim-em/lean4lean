import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedFullContext

/-! # Full aligned comparison under typed certificate transport

This induction isolates native recovery, computed guards and recovered checking
as transport inputs. It includes recursive native-type alignment, all sorted
binders, eta bodies and retained structure fields. The inputs must be discharged
for a concrete substitution class; this is not a completeness assumption.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private domain_sort_raw lambda_common_context
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointTransport
open private infer_aligned common_aligned
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedFullContext
variable [Params]

/-- Every full aligned constructor transports once the underlying computation,
native recovery, recovered comparison and computed carrier certificates do.
The callbacks operate on actual source typings, including realized native types;
no raw untyped carrier substitution or semantic re-synthesis is requested. -/
theorem ProofShape.CarrierAlignedCompare.transport_native
    (Transport : List ProofShape → List ProofShape → ProofShape.Subst → Prop)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hcons : ∀ {Δ Δ' τ A}, Transport Δ Δ' τ → Transport (A :: Δ) (A.subst τ :: Δ') τ.lift)
    (hsort : ∀ {Δ Δ' τ A u}, Transport Δ Δ' τ → DomainSort Δ A u → DomainSort Δ' (A.subst τ) u)
    (hcompute : ∀ {Γ Δ Δ' τ e T source out}, ScopedCompute Step Δ source out →
      OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      proofEraseCtx Γ = Δ → proofErase Γ e = source → Transport Δ Δ' τ →
      ScopedCompute Target Δ' (source.subst τ) (out.subst τ))
    (hrecovery : ∀ {Γ Δ Δ' τ e T source out}, ScopedTypeRecovery Step Δ source out →
      OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      proofEraseCtx Γ = Δ → proofErase Γ e = source → Transport Δ Δ' τ →
      ScopedTypeRecovery Target Δ' (source.subst τ) (out.subst τ))
    (hguard : ∀ {Γ Δ Δ' τ a b A α sa sb}, ComputedJointCarrierGuard Step Δ α sa sb →
      OnCtx Γ (env.IsType univs) → env.HasType univs Γ a A → env.HasType univs Γ b A →
      proofEraseCtx Γ = Δ → proofErase Γ A = α → proofErase Γ a = sa → proofErase Γ b = sb →
      Transport Δ Δ' τ → ComputedJointCarrierGuard Target Δ' (α.subst τ) (sa.subst τ) (sb.subst τ))
    (hrecovered : ∀ {Γ Δ Δ' τ a b A mode sa sb}, CarrierRecoveredCompare Step Δ mode sa sb →
      OnCtx Γ (env.IsType univs) → env.HasType univs Γ a A → env.HasType univs Γ b A →
      proofEraseCtx Γ = Δ → proofErase Γ a = sa → proofErase Γ b = sb → Transport Δ Δ' τ →
      CarrierRecoveredCompare Target Δ' mode (sa.subst τ) (sb.subst τ))
    (H : CarrierAlignedCompare Step Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb)
    (W : Transport Δ Δ' τ) :
    CarrierAlignedCompare Target Δ' mode (sa.subst τ) (sb.subst τ) := by
  induction H generalizing Γ a b A Δ' τ with
  | base H => exact .base (hrecovered H hΓ ha hb EΓ Ea Eb W)
  | commonCarrier RA HC =>
    obtain ⟨A₀, ha₀, EA₀⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ ha (by simpa only [EΓ, Ea] using RA)
    have hb₀ := hb.defeqU_r henv hΓ (ha.uniqU henv hΓ ha₀)
    exact .commonCarrier (hrecovery RA hΓ ha EΓ Ea W)
      (hguard HC hΓ ha₀ hb₀ EΓ EA₀ Ea Eb W)
  | aligned RA RB HT HC ihT =>
    obtain ⟨A₀, ha₀, EA₀⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ ha (by simpa only [EΓ, Ea] using RA)
    obtain ⟨B₀, hb₀, EB₀⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ hb (by simpa only [EΓ, Eb] using RB)
    obtain ⟨_, hA₀⟩ := ha₀.isType henv hΓ
    have HAB := (ha₀.uniqU henv hΓ ha).trans henv hΓ (hb.uniqU henv hΓ hb₀)
    have hB₀ := (HAB.of_l henv hΓ hA₀).hasType.2
    exact .aligned
      (hrecovery RA hΓ ha EΓ Ea W)
      (hrecovery RB hΓ hb EΓ Eb W)
      (ihT hΓ hA₀ hB₀ EΓ EA₀ EB₀ W)
      (hguard HC hΓ ha₀ (hb.defeqU_r henv hΓ (ha.uniqU henv hΓ ha₀)) EΓ EA₀ Ea Eb W)
  | recover RA RB HT HC ihT ihC =>
    obtain ⟨A₀, ha₀, EA₀⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ ha (by simpa only [EΓ, Ea] using RA)
    obtain ⟨B₀, hb₀, EB₀⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ hb (by simpa only [EΓ, Eb] using RB)
    obtain ⟨_, hA₀⟩ := ha₀.isType henv hΓ
    have HAB := (ha₀.uniqU henv hΓ ha).trans henv hΓ (hb.uniqU henv hΓ hb₀)
    have hB₀ := (HAB.of_l henv hΓ hA₀).hasType.2
    exact .recover
      (hrecovery RA hΓ ha EΓ Ea W)
      (hrecovery RB hΓ hb EΓ Eb W)
      (ihT hΓ hA₀ hB₀ EΓ EA₀ EB₀ W) (ihC hΓ ha hb EΓ Ea Eb W)
  | app HF HX ihf ihx =>
    obtain ⟨f, x, rfl, hna, Ef, Ex⟩ := erase_app_inv Ea
    obtain ⟨g, y, rfl, hnb, Eg, Ey⟩ := erase_app_inv Eb
    obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
    obtain ⟨_, _, hg, hy⟩ := hb.app_inv henv hΓ
    have HE := infer_aligned hstep HF hΓ hf hg EΓ Ef Eg
      (not_isProof_fn hΓ hf hx hna) (not_isProof_fn hΓ hg hy hnb)
    have hy' := argument_at_displayed_domain hΓ hg HE.hasType.2 hy
    exact .app (ihf hΓ hf HE.hasType.2 EΓ Ef Eg W) (ihx hΓ hx hy' EΓ Ex Ey W)
  | proj HM ihm =>
    obtain ⟨m, rfl, hn, Em⟩ := erase_proj_inv Ea
    obtain ⟨m', rfl, hn', Em'⟩ := erase_proj_inv Eb
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm', _, _⟩ := hb.proj_inv henv hΓ
    have HE := infer_aligned hstep HM hΓ hm.hasType.2 hm'.hasType.2 EΓ Em Em'
      (not_isProof_major hΓ ha hn) (not_isProof_major hΓ hb hn')
    exact .proj (ihm hΓ hm.hasType.2 HE.hasType.2 EΓ Em Em' W)
  | lam HD HB ihD ihB =>
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HB' := ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED]) Ebody Ebody' (hcons W)
    exact .lam (ihD hΓ hD hD' EΓ ED ED' W) HB'
  | lamSorted SD SD' HD HB ihD ihB =>
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HB' := ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED]) Ebody Ebody' (hcons W)
    exact .lamSorted (hsort W SD) (hsort W SD') (ihD hΓ hD hD' EΓ ED ED' W) HB'
  | lamCommon HB ihB =>
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HB' := ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED]) Ebody Ebody' (hcons W)
    exact .lamCommon HB'
  | etaLams HD Hη ihD =>
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    exact .etaLams (ihD hΓ hD hD' EΓ ED ED' W) (Hη.imp (fun H => H.subst) (fun H => H.subst))
  | forallE HD HC ihD ihC =>
    obtain ⟨D, C, rfl, _, ED, EC⟩ := erase_forallE_inv Ea
    obtain ⟨D', C', rfl, _, ED', EC'⟩ := erase_forallE_inv Eb
    obtain ⟨⟨u, hD⟩, _, hC⟩ := ha.forallE_inv henv
    obtain ⟨⟨_, hD'⟩, _, hC'⟩ := hb.forallE_inv henv
    have HDD := infer_aligned hstep HD hΓ hD hD' EΓ ED ED'
      (not_isProof_of_sort hΓ hD) (not_isProof_of_sort hΓ hD')
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have hctx := IsDefEqCtx.succ .zero HDD.symm
    have Ectx := proofErase_defeqCtx (Γ₁ := D' :: Γ) ⟨hΓ, _, hD'⟩ hctx hC'
    rw [Ectx] at EC'
    have hC' := hC'.defeqDFC henv hctx
    have EΓD := congr (congrArg List.cons ED) EΓ
    change proofEraseCtx (D :: Γ) = _ at EΓD
    have HCC := infer_aligned hstep HC hΓD hC hC' EΓD EC EC'
      (not_isProof_of_sort hΓD hC) (not_isProof_of_sort hΓD hC')
    exact .forallE (ihD hΓ hD HDD.hasType.2 EΓ ED ED' W)
      (ihC hΓD hC HCC.hasType.2 EΓD EC EC' (hcons W))
  | forallSorted SD SD' HD SC SC' HC ihD ihC =>
    obtain ⟨D, C, rfl, _, ED, EC⟩ := erase_forallE_inv Ea
    obtain ⟨D', C', rfl, _, ED', EC'⟩ := erase_forallE_inv Eb
    obtain ⟨⟨_, hD⟩, _, hC⟩ := ha.forallE_inv henv
    obtain ⟨⟨_, hD'⟩, _, hC'⟩ := hb.forallE_inv henv
    have hD := domain_sort_raw SD hΓ hD EΓ ED
    have hD' := domain_sort_raw SD' hΓ hD' EΓ ED'
    have HDD := common_aligned hstep HD hΓ hD hD' EΓ ED ED'
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
    apply CarrierAlignedCompare.etaBodyL (hsort W SD)
    simpa only [ProofShape.subst, etaArgument_subst, ProofShape.lift_subst_lift] using
      ihB hΓD hbody hη (by simp only [proofEraseCtx, EΓ, ED]) Ebody Eη (hcons W)
  | etaBodyR SD HB ihB =>
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
    apply CarrierAlignedCompare.etaBodyR (hsort W SD)
    simpa only [ProofShape.subst, etaArgument_subst, ProofShape.lift_subst_lift] using
      ihB hΓD hη hbody (by simp only [proofEraseCtx, EΓ, ED]) Eη Ebody (hcons W)
  | @structFields Δ family info ls ps fields major hi hx hp hf hadm Hfields ihfields =>
    have HE := common_aligned hstep (.structFields hi hx hp hf hadm Hfields) hΓ ha hb EΓ Ea Eb
    simp only [ProofShape.subst_mkApps, ProofShape.subst, List.map_append]
    apply CarrierAlignedCompare.structFields hi hx (by simpa only [List.length_map] using hp)
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
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea Ra
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb Rb
    exact .compute (hcompute Ra hΓ ha EΓ Ea W)
      (hcompute Rb hΓ hb EΓ Eb W)
      (ih hΓ HA.hasType.2 HB.hasType.2 EΓ EA EB W)
  | symm HC ih =>
    exact .symm (ih hΓ hb ha EΓ Eb Ea W)

end Lean4Lean.VEnv.Strengthening
