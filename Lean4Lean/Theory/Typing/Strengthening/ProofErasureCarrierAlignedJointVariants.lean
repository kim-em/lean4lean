import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedRecoveryVariants
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedRecordTransfer
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointTransport

/-! # Joint checking across universe variants of contexts and carriers

Comparison and carrier transport recurse together. Native application recovery
may select a variant domain, and function guards extend the context with that
changed domain. Concrete core computation supplies both computation interfaces.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private infer_raw common_raw carrier_raw domain_sort_raw lambda_common_context
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointTransport
open private variant_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedPrimitiveVariants
open private variant_family_levels
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedRecordTransfer
variable [Params]

/-- Exact endpoint transport of computation under an actually equal context
whose raw entries vary structurally. Concrete core paths discharge this directly. -/
def StructuralVariantComputeContext (Step : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ Γ' e T Δ source out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
    IsDefEqCtx env univs [] Γ Γ' → List.Forall₂ StructuralVariant Δ (proofEraseCtx Γ') →
    proofEraseCtx Γ = Δ → proofErase Γ e = source → ScopedCompute Step Δ source out →
    ScopedCompute Step (proofEraseCtx Γ') source out

/-- Core computation is context independent even beneath binders. -/
theorem structuralVariantComputeContext_core :
    StructuralVariantComputeContext (fun _ => ErasedIotaPrimitive D) := by
  intro Γ Γ' e T Δ source out hΓ ht W HO EΓ Ee R
  exact R.core_forget.scoped (fun H => .base H)

private theorem sort_context (_hΓ : OnCtx Γ (env.IsType univs))
    (W : IsDefEqCtx env univs [] Γ Γ') (EΓ : proofEraseCtx Γ = Δ)
    (S : DomainSort Δ A u) : DomainSort (proofEraseCtx Γ') A u := by
  have H := ContextSubstitution.sort (ContextSubstitution.of_defeqCtx (by trivial) W) (EΓ ▸ S)
  simpa only [ProofShape.subst_id] using H

private theorem compute_context (HC : StructuralVariantComputeContext Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : List.Forall₂ StructuralVariant Δ (proofEraseCtx Γ'))
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (R : ScopedCompute Step Δ source out) : ScopedCompute Step (proofEraseCtx Γ') source out :=
  HC hΓ ht W HO EΓ Ee R

private theorem oracle_cons_typed
    (hΓ : OnCtx Γ (env.IsType univs)) (W : IsDefEqCtx env univs [] Γ Γ')
    (hD : env.HasType univs Γ D (.sort u)) (ED : proofErase Γ D = d)
    (HO : List.Forall₂ StructuralVariant Δ (proofEraseCtx Γ')) :
    List.Forall₂ StructuralVariant (d :: Δ) (proofEraseCtx (D :: Γ')) := by
  simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using
    List.Forall₂.cons StructuralVariant.refl HO

private theorem recovery_context
    (hstep : ErasedScopedPrimitiveDescent Step) (hsim : StructuralVariantCompute Step)
    (R : ScopedTypeRecovery Step Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : List.Forall₂ StructuralVariant Δ (proofEraseCtx Γ')) :
    ∃ out', ScopedTypeRecovery Step (proofEraseCtx Γ') source out' ∧ StructuralVariant out out' := by
  have hΓ' := (W.symm henv.ordered).isType
  have Ee' := (proofErase_defeqCtx hΓ W ht).symm.trans Ee
  obtain ⟨out', R', V⟩ := proofErase_carrier_aligned_recovery_variant hstep hsim R hΓ hΓ'
    ht (ht.defeqDFC henv W) EΓ Ee HO (by rw [Ee']; exact .refl)
  exact ⟨out', by simpa only [Ee'] using R', V⟩

/-- Simultaneous comparison and carrier transport. Raw endpoints are unchanged;
actual context conversion and structural variants justify changing the carrier. -/
def ComputedJointVariantResult
    (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (kind : JointCheckKind) (sa sb : ProofShape) : Prop :=
  match kind with
  | .compare mode => ∀ {Γ Γ' a b A}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ a A → env.HasType univs Γ b A → proofEraseCtx Γ = Δ →
      proofErase Γ a = sa → proofErase Γ b = sb → IsDefEqCtx env univs [] Γ Γ' →
      List.Forall₂ StructuralVariant Δ (proofEraseCtx Γ') →
      ComputedJointCompare Step (proofEraseCtx Γ') mode sa sb
  | .carrier α => ∀ {Γ Γ' a b A}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ a A → env.HasType univs Γ b A → proofEraseCtx Γ = Δ →
      proofErase Γ A = α → proofErase Γ a = sa → proofErase Γ b = sb →
      IsDefEqCtx env univs [] Γ Γ' →
      List.Forall₂ StructuralVariant Δ (proofEraseCtx Γ') →
      ∀ {B}, env.IsDefEqU univs Γ A B → StructuralVariant α (proofErase Γ B) →
      ComputedJointCarrierGuard Step (proofEraseCtx Γ') (proofErase Γ B) sa sb

/-- Every existing computed joint constructor transports through structural
universe variants of context entries and carriers. Function domains and nested
record recipes may both change. The two computation interfaces remain explicit;
core computation satisfies them without additional semantic assumptions. -/
theorem ProofShape.ComputedJointCheck.structural_variant
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hctx : StructuralVariantComputeContext Step) (hsim : StructuralVariantCompute Step)
    (H : ComputedJointCheck Step Δ kind sa sb) : ComputedJointVariantResult Step Δ kind sa sb := by
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
    obtain ⟨out', R', RT⟩ := recovery_context hstep hsim R
      hΓ hfPi EΓ Ef W HO
    obtain ⟨A', B', rfl, RA, _⟩ := variant_forallE_inv RT
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
  | appComputed RF HF HX ihf ihx =>
    intro Γ Γ' a b A hΓ ha hb EΓ Ea Eb W HO
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
    exact .appComputed (compute_context hctx hΓ hf W HO EΓ Ef RF)
      (ihf hΓ hf HE.hasType.2 EΓ Ef Eg W HO)
      (by simpa only [ED] using (ihx hΓ hxD hyD EΓ ED Ex Ey W HO
        ⟨_, hD⟩ (ED ▸ StructuralVariant.refl)))
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
    apply ComputedJointCheck.lam (ihD hΓ hD hD' EΓ ED ED' W HO)
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
    apply ComputedJointCheck.lamSorted (sort_context hΓ W EΓ SD) (sort_context hΓ W EΓ SD') (ihD hΓ hD hD' EΓ ED ED' W HO)
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
    apply ComputedJointCheck.lamCommon
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
    apply ComputedJointCheck.forallE (ihD hΓ hD HDD.hasType.2 EΓ ED ED' W HO)
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
    apply ComputedJointCheck.forallSorted (sort_context hΓ W EΓ SD) (sort_context hΓ W EΓ SD') (ihD hΓ hD hD' EΓ ED ED' W HO)
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
    apply ComputedJointCheck.etaBodyL (sort_context hΓ W EΓ SD)
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
    apply ComputedJointCheck.etaBodyR (sort_context hΓ W EΓ SD)
    simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using
      ihB hΓD hη hbody (by simp only [proofEraseCtx, EΓ, ED]) Eη Ebody (.succ W hD) (oracle_cons_typed hΓ W hD ED HO)
  | @structFields Δ family info ls ps fields major hi hx hp hf hadm Hfields ihfields =>
    intro Γ Γ' a b A hΓ ha hb EΓ Ea Eb W HO
    have HE := common_raw hstep (.structFields hi hx hp hf hadm Hfields) hΓ ha hb EΓ Ea Eb
    apply ComputedJointCheck.structFields hi hx hp
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
    exact .compute (compute_context hctx hΓ ha W HO EΓ Ea Ra)
      (compute_context hctx hΓ hb W HO EΓ Eb Rb)
      (ih hΓ HA.hasType.2 HB.hasType.2 EΓ EA EB W HO)
  | symm HC ih =>
    intro Γ Γ' a b A hΓ ha hb EΓ Ea Eb W HO
    exact .symm (ih hΓ hb ha EΓ Eb Ea W HO)
  | carrierChecked HC ih =>
    intro Γ Γ' a b A hΓ ha hb EΓ Eα Ea Eb W HO B HAB HT
    exact .carrierChecked (ih hΓ ha hb EΓ Ea Eb W HO)
  | carrierSubsingleton HS =>
    intro Γ Γ' a b A hΓ ha hb EΓ Eα Ea Eb W HO B HAB HT
    exact .carrierSubsingleton (HS.variant HT)
  | carrierSymm HC ih =>
    intro Γ Γ' a b A hΓ ha hb EΓ Eα Ea Eb W HO B HAB HT
    exact .carrierSymm (ih hΓ hb ha EΓ Eα Eb Ea W HO HAB HT)
  | carrierCompute RC HC ih =>
    intro Γ Γ' a b A hΓ ha hb EΓ Eα Ea Eb W HO B HAB HT
    obtain ⟨u, hA⟩ := ha.isType henv hΓ
    have HAB := HAB.of_l henv hΓ hA
    obtain ⟨A', HE, EA⟩ := proofErase_scoped_compute_realize hstep hΓ hA EΓ Eα RC
    obtain ⟨target, RB, HR⟩ := hsim hΓ hΓ hA HAB.hasType.2 (.rfl (fun _ _ => .refl))
      (by simpa only [EΓ, Eα] using RC) (by simpa only [Eα] using HT)
    obtain ⟨B', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ HAB.hasType.2 rfl rfl RB
    have HC' := ih hΓ (HE.defeq ha) (HE.defeq hb) EΓ EA Ea Eb W HO
      ((HE.symm.trans HAB).trans HB).toU (EB.symm ▸ HR)
    rw [EB] at HC'
    exact .carrierCompute (compute_context hctx hΓ HAB.hasType.2 W (by simpa only [EΓ] using HO) rfl rfl RB) HC'
  | carrierReduce Ra Rb HC ih =>
    intro Γ Γ' a b A hΓ ha hb EΓ Eα Ea Eb W HO B HAB HT
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea Ra
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb Rb
    exact .carrierReduce (compute_context hctx hΓ ha W HO EΓ Ea Ra) (compute_context hctx hΓ hb W HO EΓ Eb Rb)
      (ih hΓ HA.hasType.2 HB.hasType.2 EΓ Eα EA EB W HO HAB HT)
  | carrierFunction SD HC ih =>
    intro Γ Γ' a b A hΓ ha hb EΓ Eα Ea Eb W HO B HAB HT
    obtain ⟨rawD', rawC', ET, HD, HB⟩ := variant_forallE_inv HT
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
    have HO' : List.Forall₂ StructuralVariant
        (proofEraseCtx (D :: Γ)) (proofEraseCtx (D' :: Γ')) := by
      simp only [proofEraseCtx, ED, EDom, EΓ]
      exact .cons HD HO
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
    apply ComputedJointCheck.carrierFunction ⟨Γ', D', (W.symm henv.ordered).isType, rfl,
      Hdom.hasType.2.defeqDFC henv W, EDom⟩
    simpa only [proofEraseCtx, EDom] using H'
  | @carrierIntro family info ls Δ sa sb ps hi hx hp hadm Hfields ihfields =>
    intro Γ Γ' a b A hΓ ha hb EΓ Eα Ea Eb W HO B HAB HTy
    obtain ⟨_, hA⟩ := ha.isType henv hΓ
    have hB := (HAB.of_l henv hΓ hA).hasType.2
    obtain ⟨ls', ps', EB, HP, hw, hw', hl, HL⟩ := variant_family_levels hi hΓ hA hB Eα HTy
    have hadm' : (info.resultLevel.inst ls').IsNeverZero ∨ StructureReplay.ProofFields env univs info ls' := by
      rcases hadm with hz | hp
      · exact .inl (hz.of_equiv (VLevel.inst_congr rfl HL))
      · exact .inr (hp.level_congr henv hi hw hw' hl HL)
    rw [EB]
    have HE := carrier_raw hstep (.carrierIntro hi hx hp hadm Hfields) hΓ ha hb EΓ Eα Ea Eb
    obtain ⟨args, rfl, Eargs⟩ := proofErase_const_spine_inv Eα
    have hlen : args.length = info.nparams := by
      have HH := congrArg List.length Eargs
      simp only [List.length_map] at HH
      omega
    have hexpa := (StructureReplay.expansion_typed_iff henv hΓ hi hlen hx ha).2 hadm
    apply ComputedJointCheck.carrierIntro hi hx (HP.length_eq.symm.trans hp) hadm'
    intro i hj hn'
    have hn : ¬ StructureReplay.ProofField env univs info ls i :=
      fun HF => hn' (HF.congr_levels hi hw hw' hl HL)
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
    intro Γ Γ' a b A hΓ ha hb EΓ EA Ea Eb W HO B HAB V
    obtain ⟨_, hA⟩ := ha.isType henv hΓ
    have hB := (HAB.of_l henv hΓ hA).hasType.2
    have Hsource : ComputedJointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ A)
        (proofErase Γ a) (proofErase Γ b) := by
      simpa only [EΓ, EA, Ea, Eb] using (ComputedJointCheck.carrierNested hi hx hp hadm HT Hfields)
    have HE := proofErase_computed_joint_carrier_reflect hstep hΓ ha hb Hsource
    have hat := ha.defeqU_r henv hΓ HAB
    obtain ⟨ls', ps', EB, HP, hw, hw', hl, HL⟩ := variant_family_levels hi hΓ hA hB EA V
    obtain ⟨args, rfl, Eargs⟩ := proofErase_const_spine_inv EA
    obtain ⟨args', rfl, Eargs'⟩ := proofErase_const_spine_inv EB
    have hlen : args.length = info.nparams := by
      have := congrArg List.length Eargs
      simp only [List.length_map] at this
      omega
    have hexpa := (StructureReplay.expansion_typed_iff henv hΓ hi hlen hx ha).2 hadm
    obtain ⟨doms', result', HT'⟩ := projection_telescope_exists hi hw'
    have hadm' : (info.resultLevel.inst ls').IsNeverZero ∨ StructureReplay.ProofFields env univs info ls' := by
      rcases hadm with hz | hp
      · exact .inl (hz.of_equiv (VLevel.inst_congr rfl HL))
      · exact .inr (hp.level_congr henv hi hw hw' hl HL)
    rw [EB]
    apply ComputedJointCheck.carrierNested hi hx (HP.length_eq.symm.trans hp) hadm' HT'
    intro i hj hn'
    have hn : ¬ StructureReplay.ProofField env univs info ls i :=
      fun HF => hn' (HF.congr_levels hi hw hw' hl HL)
    obtain ⟨F, hia, hib⟩ := structure_equal_projection_typings hΓ HE hexpa hj
    have hpa : ¬ IsProof Γ (.proj family i a) :=
      fun H => hn (StructureReplay.ProofField.of_projection hΓ hi hlen hj hexpa H)
    have hpb : ¬ IsProof Γ (.proj family i b) := by
      rintro ⟨P, hibP, hP⟩
      exact hpa ⟨P, hia.defeqU_r henv hΓ (hib.uniqU henv hΓ hibP), hP⟩
    obtain ⟨hjs, Fs, hiaFs, EFs⟩ := proofErase_projection_at_recovered_family hΓ hi HT hia hpa ha
    have hibFs := hib.defeqU_r henv hΓ (hia.uniqU henv hΓ hiaFs)
    have EFs' : proofErase Γ Fs = projectionType family info doms i hjs ps sa := by
      simpa only [projectionType, List.map_take, ← Eargs, Ea] using EFs
    obtain ⟨hjt, Ft, hiaFt, EFt⟩ := proofErase_projection_at_recovered_family hΓ hi HT' hia hpa hat
    have EFt' : proofErase Γ Ft = projectionType family info doms' i hjt ps' sa := by
      simpa only [projectionType, List.map_take, ← Eargs', Ea] using EFt
    obtain ⟨vt, hFt⟩ := hiaFt.isType henv hΓ
    have VF := proofErase_carrier_aligned_projection_type_parameter_variant (m := sa) HT HT' hw hw' HL hjs hjt HP
    have Epa : proofErase Γ (.proj family i a) = .proj family i sa := by
      rw [show proofErase Γ (.proj family i a) = .proj family i (proofErase Γ a) from if_neg hpa, Ea]
    have Epb : proofErase Γ (.proj family i b) = .proj family i sb := by
      rw [show proofErase Γ (.proj family i b) = .proj family i (proofErase Γ b) from if_neg hpb, Eb]
    have HF := ihfields i hj hn hΓ hiaFs hibFs EΓ EFs' Epa Epb W HO
      (hiaFs.uniqU henv hΓ hiaFt) (by simpa only [EFt'] using VF)
    rwa [EFt'] at HF

end Lean4Lean.VEnv.Strengthening
