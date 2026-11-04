import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedLevelUnionClosure

/-! # Exact native outputs and full aligned comparison across contexts

Explicit universe computation restores the original native output after
structural context variation. The complete aligned comparison grammar can then
transport without changing its independently recovered carrier endpoints.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private domain_sort_raw lambda_common_context
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointTransport
open private sort_context recovery_context compute_context oracle_cons_typed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedJointVariants
open private native_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedRecoveryVariants
variable [Params]

/-- Structural context variation preserves a native recovery certificate's
literal output when explicit universe computation is available. The conversion
back targets the original actual carrier, typed in the new context. -/
theorem proofErase_carrier_aligned_recovery_exact_context
    (hstep : ErasedScopedPrimitiveDescent Step) (hsim : StructuralVariantCompute Step)
    (hlevel : ∀ {Δ a b}, LevelPrimitive univs a b → ScopedCompute Step Δ a b)
    (R : ScopedTypeRecovery Step Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : List.Forall₂ StructuralVariant Δ (proofEraseCtx Γ')) :
    ScopedTypeRecovery Step (proofEraseCtx Γ') source out := by
  obtain ⟨A, htA, EA⟩ := native_type hstep hΓ ht (by simpa only [EΓ, Ee] using R)
  obtain ⟨_, hA⟩ := htA.isType henv hΓ
  obtain ⟨out', R', V⟩ := recovery_context hstep hsim R hΓ ht EΓ Ee W HO
  have hΓ' := (W.symm henv.ordered).isType
  have EA' := (proofErase_defeqCtx hΓ W hA).symm.trans EA
  have RL := (proofErase_carrier_aligned_variant_level_compute
    (by simpa only [EA'] using V.symm) hΓ' (hA.defeqDFC henv W)).scoped
      (Δ := proofEraseCtx Γ') hlevel
  exact R'.convert (by simpa only [EA'] using RL)

private theorem common_aligned (hstep : ErasedScopedPrimitiveDescent Step)
    (H : CarrierAlignedCompare Step Δ mode sa sb) (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb) :
    env.IsDefEq univs Γ a b A := by
  have HH := proofErase_carrier_aligned_compare_descend hstep hΓ hΓ (Ctx.LiftN.zero []) rfl ha hb
    (by simpa only [List.length_nil, ProofShape.liftN_zero, EΓ, Ea, Eb] using H)
  exact (HH.1 ⟨_, (ha.isType henv hΓ).choose_spec⟩).of_l henv hΓ ha

private theorem infer_aligned (hstep : ErasedScopedPrimitiveDescent Step)
    (H : CarrierAlignedCompare Step Δ false sa sb) (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb)
    (hna : ¬ IsProof Γ a) (hnb : ¬ IsProof Γ b) : env.IsDefEq univs Γ a b A := by
  have HH := proofErase_carrier_aligned_compare_descend hstep hΓ hΓ (Ctx.LiftN.zero []) rfl ha hb
    (by simpa only [List.length_nil, ProofShape.liftN_zero, EΓ, Ea, Eb] using H)
  exact (HH.2 rfl hna hnb).of_l henv hΓ ha

private theorem guard_context
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hctx : StructuralVariantComputeContext Step) (hsim : StructuralVariantCompute Step)
    (HC : ComputedJointCarrierGuard Step Δ α sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (EΓ : proofEraseCtx Γ = Δ) (EA : proofErase Γ A = α)
    (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb)
    (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : List.Forall₂ StructuralVariant Δ (proofEraseCtx Γ')) :
    ComputedJointCarrierGuard Step (proofEraseCtx Γ') α sa sb := by
  have H := HC.structural_variant hstep hctx hsim hΓ ha hb EΓ EA Ea Eb W HO
    ⟨_, (ha.isType henv hΓ).choose_spec⟩ (EA ▸ StructuralVariant.refl)
  simpa only [EA] using H

/-- Every aligned comparison constructor, including recursive inferred native
carrier alignment, sorted binders, eta bodies and record fields, transports
through structural context variation with unchanged raw endpoints. -/
theorem ProofShape.CarrierAlignedCompare.structural_context
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hctx : StructuralVariantComputeContext Step) (hsim : StructuralVariantCompute Step)
    (hlevel : ∀ {Δ a b}, LevelPrimitive univs a b → ScopedCompute Step Δ a b)
    (H : CarrierAlignedCompare Step Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb)
    (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : List.Forall₂ StructuralVariant Δ (proofEraseCtx Γ')) :
    CarrierAlignedCompare Step (proofEraseCtx Γ') mode sa sb := by
  induction H generalizing Γ Γ' a b A with
  | base H => exact .base (H.structural_context hstep hctx hsim hlevel hΓ ha hb EΓ Ea Eb W HO)
  | commonCarrier RA HC =>
    obtain ⟨A₀, ha₀, EA₀⟩ := native_type hstep hΓ ha (by simpa only [EΓ, Ea] using RA)
    have hb₀ := hb.defeqU_r henv hΓ (ha.uniqU henv hΓ ha₀)
    exact .commonCarrier (proofErase_carrier_aligned_recovery_exact_context hstep hsim hlevel RA hΓ ha EΓ Ea W HO)
      (guard_context hstep hctx hsim HC hΓ ha₀ hb₀ EΓ EA₀ Ea Eb W HO)
  | aligned RA RB HT HC ihT =>
    obtain ⟨A₀, ha₀, EA₀⟩ := native_type hstep hΓ ha (by simpa only [EΓ, Ea] using RA)
    obtain ⟨B₀, hb₀, EB₀⟩ := native_type hstep hΓ hb (by simpa only [EΓ, Eb] using RB)
    obtain ⟨_, hA₀⟩ := ha₀.isType henv hΓ
    have HAB := (ha₀.uniqU henv hΓ ha).trans henv hΓ (hb.uniqU henv hΓ hb₀)
    have hB₀ := (HAB.of_l henv hΓ hA₀).hasType.2
    exact .aligned
      (proofErase_carrier_aligned_recovery_exact_context hstep hsim hlevel RA hΓ ha EΓ Ea W HO)
      (proofErase_carrier_aligned_recovery_exact_context hstep hsim hlevel RB hΓ hb EΓ Eb W HO)
      (ihT hΓ hA₀ hB₀ EΓ EA₀ EB₀ W HO)
      (guard_context hstep hctx hsim HC hΓ ha₀ (hb.defeqU_r henv hΓ (ha.uniqU henv hΓ ha₀)) EΓ EA₀ Ea Eb W HO)
  | recover RA RB HT HC ihT ihC =>
    obtain ⟨A₀, ha₀, EA₀⟩ := native_type hstep hΓ ha (by simpa only [EΓ, Ea] using RA)
    obtain ⟨B₀, hb₀, EB₀⟩ := native_type hstep hΓ hb (by simpa only [EΓ, Eb] using RB)
    obtain ⟨_, hA₀⟩ := ha₀.isType henv hΓ
    have HAB := (ha₀.uniqU henv hΓ ha).trans henv hΓ (hb.uniqU henv hΓ hb₀)
    have hB₀ := (HAB.of_l henv hΓ hA₀).hasType.2
    exact .recover
      (proofErase_carrier_aligned_recovery_exact_context hstep hsim hlevel RA hΓ ha EΓ Ea W HO)
      (proofErase_carrier_aligned_recovery_exact_context hstep hsim hlevel RB hΓ hb EΓ Eb W HO)
      (ihT hΓ hA₀ hB₀ EΓ EA₀ EB₀ W HO) (ihC hΓ ha hb EΓ Ea Eb W HO)
  | app HF HX ihf ihx =>
    obtain ⟨f, x, rfl, hna, Ef, Ex⟩ := erase_app_inv Ea
    obtain ⟨g, y, rfl, hnb, Eg, Ey⟩ := erase_app_inv Eb
    obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
    obtain ⟨_, _, hg, hy⟩ := hb.app_inv henv hΓ
    have HE := infer_aligned hstep HF hΓ hf hg EΓ Ef Eg
      (not_isProof_fn hΓ hf hx hna) (not_isProof_fn hΓ hg hy hnb)
    have hy' := argument_at_displayed_domain hΓ hg HE.hasType.2 hy
    exact .app (ihf hΓ hf HE.hasType.2 EΓ Ef Eg W HO) (ihx hΓ hx hy' EΓ Ex Ey W HO)
  | proj HM ihm =>
    obtain ⟨m, rfl, hn, Em⟩ := erase_proj_inv Ea
    obtain ⟨m', rfl, hn', Em'⟩ := erase_proj_inv Eb
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm', _, _⟩ := hb.proj_inv henv hΓ
    have HE := infer_aligned hstep HM hΓ hm.hasType.2 hm'.hasType.2 EΓ Em Em'
      (not_isProof_major hΓ ha hn) (not_isProof_major hΓ hb hn')
    exact .proj (ihm hΓ hm.hasType.2 HE.hasType.2 EΓ Em Em' W HO)
  | lam HD HB ihD ihB =>
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HB' := ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED])
      Ebody Ebody' (.succ W hD) (oracle_cons_typed hΓ W hD ED HO)
    apply CarrierAlignedCompare.lam (ihD hΓ hD hD' EΓ ED ED' W HO)
    simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using HB'
  | lamSorted SD SD' HD HB ihD ihB =>
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HB' := ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED])
      Ebody Ebody' (.succ W hD) (oracle_cons_typed hΓ W hD ED HO)
    apply CarrierAlignedCompare.lamSorted (sort_context hΓ W EΓ SD) (sort_context hΓ W EΓ SD') (ihD hΓ hD hD' EΓ ED ED' W HO)
    simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using HB'
  | lamCommon HB ihB =>
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HB' := ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED])
      Ebody Ebody' (.succ W hD) (oracle_cons_typed hΓ W hD ED HO)
    apply CarrierAlignedCompare.lamCommon
    simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using HB'
  | etaLams HD Hη ihD =>
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    exact .etaLams (ihD hΓ hD hD' EΓ ED ED' W HO) (Hη.imp (fun H => H) (fun H => H))
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
    apply CarrierAlignedCompare.forallE (ihD hΓ hD HDD.hasType.2 EΓ ED ED' W HO)
    simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using
      (ihC hΓD hC HCC.hasType.2 EΓD EC EC' (.succ W hD) (oracle_cons_typed hΓ W hD ED HO))
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
    apply CarrierAlignedCompare.forallSorted (sort_context hΓ W EΓ SD) (sort_context hΓ W EΓ SD') (ihD hΓ hD hD' EΓ ED ED' W HO)
      (by simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using sort_context hΓD (.succ W hD) EΓD SC)
      (by simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using sort_context hΓD (.succ W hD) EΓD SC')
    simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using
      (ihC hΓD hC hC' EΓD EC EC' (.succ W hD) (oracle_cons_typed hΓ W hD ED HO))
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
    apply CarrierAlignedCompare.etaBodyL (sort_context hΓ W EΓ SD)
    simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using
      ihB hΓD hbody hη (by simp only [proofEraseCtx, EΓ, ED]) Ebody Eη (.succ W hD) (oracle_cons_typed hΓ W hD ED HO)
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
    apply CarrierAlignedCompare.etaBodyR (sort_context hΓ W EΓ SD)
    simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using
      ihB hΓD hη hbody (by simp only [proofEraseCtx, EΓ, ED]) Eη Ebody (.succ W hD) (oracle_cons_typed hΓ W hD ED HO)
  | @structFields Δ family info ls ps fields major hi hx hp hf hadm Hfields ihfields =>
    have HE := common_aligned hstep (.structFields hi hx hp hf hadm Hfields) hΓ ha hb EΓ Ea Eb
    apply CarrierAlignedCompare.structFields hi hx hp
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
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea Ra
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb Rb
    exact .compute (compute_context hctx hΓ ha W HO EΓ Ea Ra)
      (compute_context hctx hΓ hb W HO EΓ Eb Rb)
      (ih hΓ HA.hasType.2 HB.hasType.2 EΓ EA EB W HO)
  | symm HC ih =>
    exact .symm (ih hΓ hb ha EΓ Eb Ea W HO)

/-- Endpoint universe variants compare by converting back to the typed original
endpoints, without changing any recursive comparison certificate. -/
theorem ProofShape.CarrierAlignedCompare.structural_endpoints
    (hlevel : ∀ {Δ a b}, LevelPrimitive univs a b → ScopedCompute Step Δ a b)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b))
    (VA : StructuralVariant sa (proofErase Γ a))
    (VB : StructuralVariant sb (proofErase Γ b)) :
    CarrierAlignedCompare Step (proofEraseCtx Γ) mode sa sb :=
  .compute ((proofErase_carrier_aligned_variant_level_compute VA hΓ ha).scoped hlevel)
    ((proofErase_carrier_aligned_variant_level_compute VB hΓ hb).scoped hlevel) H

/-- Full aligned comparison transports at every finite level-extended stage;
source and target terms may also differ by structural universe variants. -/
theorem proofErase_carrier_aligned_level_stage_full_variant
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (HO : List.Forall₂ StructuralVariant (proofEraseCtx Γ) (proofEraseCtx Γ'))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (VA : StructuralVariant sa (proofErase Γ a))
    (VB : StructuralVariant sb (proofErase Γ b))
    (H : CarrierAlignedCompare (ErasedLevelRecoveredStage D stage) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b)) :
    CarrierAlignedCompare (ErasedLevelRecoveredStage D stage) (proofEraseCtx Γ') mode sa sb := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedLevelRecoveredStage D stage) :=
    erased_level_recovered_stage_descent heq hs stage
  have W := proofErase_carrier_aligned_context_variant_defeq (Step := ErasedLevelRecoveredStage D stage)
    hstep hΓ hΓ' HO
  have H' := H.structural_context hstep (structuralVariantComputeContext_level_stage heq hs stage)
    (structuralVariantCompute_level_stage heq hs stage)
    (fun H => .base (erased_level_primitive_into_stage H stage)) hΓ ha hb rfl rfl rfl W HO
  have EA := proofErase_defeqCtx hΓ W ha
  have EB := proofErase_defeqCtx hΓ W hb
  exact CarrierAlignedCompare.structural_endpoints (fun H => .base (erased_level_primitive_into_stage H stage))
    hΓ' (ha.defeqDFC henv W) (hb.defeqDFC henv W)
    (by simpa only [← EA, ← EB] using H') (by simpa only [← EA] using VA) (by simpa only [← EB] using VB)

/-- The closed union supports the entire aligned comparison grammar through
structural context and endpoint variation, with no simulation assumption. -/
theorem proofErase_carrier_aligned_level_union_full_variant
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (HO : List.Forall₂ StructuralVariant (proofEraseCtx Γ) (proofEraseCtx Γ'))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (VA : StructuralVariant sa (proofErase Γ a))
    (VB : StructuralVariant sb (proofErase Γ b))
    (H : CarrierAlignedCompare (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b)) :
    CarrierAlignedCompare (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ') mode sa sb := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedLevelRecoveredUnion D) :=
    erased_level_recovered_union_descent heq hs
  have W := proofErase_carrier_aligned_context_variant_defeq (Step := ErasedLevelRecoveredUnion D)
    hstep hΓ hΓ' HO
  have H' := H.structural_context hstep (structuralVariantComputeContext_level_union heq hs)
    (structuralVariantCompute_level_union heq hs) (fun H => .base ⟨0, .inr H⟩)
    hΓ ha hb rfl rfl rfl W HO
  have EA := proofErase_defeqCtx hΓ W ha
  have EB := proofErase_defeqCtx hΓ W hb
  exact CarrierAlignedCompare.structural_endpoints (fun H => .base ⟨0, .inr H⟩)
    hΓ' (ha.defeqDFC henv W) (hb.defeqDFC henv W)
    (by simpa only [← EA, ← EB] using H') (by simpa only [← EA] using VA) (by simpa only [← EB] using VB)

/-- Native recovery retains its exact output under structural context changes
at any finite stage, with all interface premises discharged. -/
theorem proofErase_carrier_aligned_level_stage_exact_recovery
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (HO : List.Forall₂ StructuralVariant (proofEraseCtx Γ) (proofEraseCtx Γ'))
    (ht : env.HasType univs Γ e T)
    (R : ScopedTypeRecovery (ErasedLevelRecoveredStage D stage) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ScopedTypeRecovery (ErasedLevelRecoveredStage D stage) (proofEraseCtx Γ') (proofErase Γ' e) out := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedLevelRecoveredStage D stage) :=
    erased_level_recovered_stage_descent heq hs stage
  have W := proofErase_carrier_aligned_context_variant_defeq (Step := ErasedLevelRecoveredStage D stage)
    hstep hΓ hΓ' HO
  have R' := proofErase_carrier_aligned_recovery_exact_context hstep
    (structuralVariantCompute_level_stage heq hs stage)
    (fun H => .base (erased_level_primitive_into_stage H stage)) R hΓ ht rfl rfl W HO
  simpa only [proofErase_defeqCtx hΓ W ht] using R'

end Lean4Lean.VEnv.Strengthening
