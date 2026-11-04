import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedEtaSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedTypedExposure

/-! # Paired substitution of the full scoped comparison

The source includes recursive eta bodies, sorted binders and structure-field
checks. The two image maps may have nonjoining inferred-related images. Their
actual interpretations are converted beneath binders. Source computation uses
a typed primitive-substitution interface; the primitive-free corollaries discharge
that interface directly. Concrete core primitives are handled separately.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private infer_raw common_raw domain_sort_raw lambda_common_context
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointTransport
variable [Params]

private theorem empty_descent : ErasedScopedPrimitiveDescent (fun _ _ _ => False) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht H
  exact H.elim

private theorem source_infer (hsource : ErasedScopedPrimitiveDescent Source) (H : ScopedCompare Source Δ false sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb)
    (hna : ¬ IsProof Γ a) (hnb : ¬ IsProof Γ b) : env.IsDefEq univs Γ a b A :=
  infer_raw hsource H.joint.computed hΓ ha hb EΓ Ea Eb hna hnb

private theorem source_common (hsource : ErasedScopedPrimitiveDescent Source) (H : ScopedCompare Source Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb) :
    env.IsDefEq univs Γ a b A :=
  common_raw hsource H.joint.computed hΓ ha hb EΓ Ea Eb

private theorem left_sort (W : CarrierAlignedSubstitution Step Γ Γ₀ σ φ ρ τ)
    (EΓ : proofEraseCtx Γ = Δ) (S : DomainSort Δ A u) : DomainSort (proofEraseCtx Γ₀) (A.subst ρ) u :=
  ContextSubstitution.sort (ContextSubstitution.of_typed W.target_wf W.left W.left_erasure) (EΓ.symm ▸ S)

private theorem right_sort (W : CarrierAlignedSubstitution Step Γ Γ₀ σ φ ρ τ)
    (EΓ : proofEraseCtx Γ = Δ) (S : DomainSort Δ A u) : DomainSort (proofEraseCtx Γ₀) (A.subst τ) u :=
  ContextSubstitution.sort (ContextSubstitution.of_typed W.target_wf W.right W.right_erasure) (EΓ.symm ▸ S)

private theorem inferred_mode (H : CarrierAlignedCompare Step Δ false a b) :
    CarrierAlignedCompare Step Δ mode a b := by
  cases mode
  · exact H
  · exact H.common

private def ScopedPairedResult (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (mode : Bool) (sa sb : ProofShape) : Prop :=
  ∀ {Γ a b A Γ₀ σ φ ρ τ}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ a A → env.HasType univs Γ b A → proofEraseCtx Γ = Δ →
    proofErase Γ a = sa → proofErase Γ b = sb → CarrierAlignedSubstitution Step Γ Γ₀ σ φ ρ τ →
    CarrierAlignedCompare Step (proofEraseCtx Γ₀) mode (sa.subst ρ) (sb.subst τ)

private theorem scoped_paired_transport
    (hsource : ErasedScopedPrimitiveDescent Source)
    (hsubst : ErasedPrimitiveSubstitutionTo Source Step)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (H : ScopedCompare Source Δ mode sa sb) : ScopedPairedResult Step Δ mode sa sb := by
  induction H with
  | leaf H =>
    intro Γ a b A Γ₀ σ φ ρ τ hΓ ha hb EΓ Ea Eb W
    cases H with
    | refl => exact inferred_mode (by simpa only [Ea] using
        proofErase_carrier_aligned_subst_images hrename W.target_wf W.left ha W.left_erasure W.images)
    | sort H => exact .computed (.leaf (.sort H))
    | const H => exact .computed (.leaf (.const H))
    | etaL H =>
      simpa only [Ea, Eb] using proofErase_carrier_aligned_eta_subst_images hrename W ha hb
        (by simpa only [Ea, Eb] using H)
    | etaR H =>
      have HC := proofErase_carrier_aligned_eta_subst_images hrename W.symm hb ha
        (by simpa only [Ea, Eb] using H)
      simpa only [Ea, Eb] using HC.symm
  | app HF HX ihf ihx =>
    intro Γ a b A Γ₀ σ φ ρ τ hΓ ha hb EΓ Ea Eb W
    obtain ⟨f, x, rfl, hna, Ef, Ex⟩ := erase_app_inv Ea
    obtain ⟨g, y, rfl, hnb, Eg, Ey⟩ := erase_app_inv Eb
    obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
    obtain ⟨_, _, hg, hy⟩ := hb.app_inv henv hΓ
    have HE := source_infer hsource HF hΓ hf hg EΓ Ef Eg
      (not_isProof_fn hΓ hf hx hna) (not_isProof_fn hΓ hg hy hnb)
    have hy' := argument_at_displayed_domain hΓ hg HE.hasType.2 hy
    exact .app (ihf hΓ hf HE.hasType.2 EΓ Ef Eg W) (ihx hΓ hx hy' EΓ Ex Ey W)
  | proj HM ihm =>
    intro Γ a b A Γ₀ σ φ ρ τ hΓ ha hb EΓ Ea Eb W
    obtain ⟨m, rfl, hn, Em⟩ := erase_proj_inv Ea
    obtain ⟨m', rfl, hn', Em'⟩ := erase_proj_inv Eb
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm', _, _⟩ := hb.proj_inv henv hΓ
    have HE := source_infer hsource HM hΓ hm.hasType.2 hm'.hasType.2 EΓ Em Em'
      (not_isProof_major hΓ ha hn) (not_isProof_major hΓ hb hn')
    exact .proj (ihm hΓ hm.hasType.2 HE.hasType.2 EΓ Em Em' W)
  | lam HD HB ihD ihB =>
    intro Γ a b A Γ₀ σ φ ρ τ hΓ ha hb EΓ Ea Eb W
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HB' := ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED]) Ebody Ebody' (W.cons hstep hrename hD)
    simp only [proofEraseCtx, proofErase_subst_with W.target_wf W.left hD W.left_erasure, ED] at HB'
    exact .lam (ihD hΓ hD hD' EΓ ED ED' W) HB'
  | lamSorted SD SD' HD HB ihD ihB =>
    intro Γ a b A Γ₀ σ φ ρ τ hΓ ha hb EΓ Ea Eb W
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HB' := ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED]) Ebody Ebody' (W.cons hstep hrename hD)
    simp only [proofEraseCtx, proofErase_subst_with W.target_wf W.left hD W.left_erasure, ED] at HB'
    exact .lamSorted (left_sort W EΓ SD) (right_sort W EΓ SD') (ihD hΓ hD hD' EΓ ED ED' W) HB'
  | lamCommon HB ihB =>
    intro Γ a b A Γ₀ σ φ ρ τ hΓ ha hb EΓ Ea Eb W
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HB' := ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED]) Ebody Ebody' (W.cons hstep hrename hD)
    simp only [proofEraseCtx, proofErase_subst_with W.target_wf W.left hD W.left_erasure, ED] at HB'
    exact .lamCommon HB'
  | forallE HD HC ihD ihC =>
    intro Γ a b A Γ₀ σ φ ρ τ hΓ ha hb EΓ Ea Eb W
    obtain ⟨D, C, rfl, _, ED, EC⟩ := erase_forallE_inv Ea
    obtain ⟨D', C', rfl, _, ED', EC'⟩ := erase_forallE_inv Eb
    obtain ⟨⟨u, hD⟩, _, hC⟩ := ha.forallE_inv henv
    obtain ⟨⟨_, hD'⟩, _, hC'⟩ := hb.forallE_inv henv
    have HDD := source_infer hsource HD hΓ hD hD' EΓ ED ED'
      (not_isProof_of_sort hΓ hD) (not_isProof_of_sort hΓ hD')
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have hctx := IsDefEqCtx.succ .zero HDD.symm
    have Ectx := proofErase_defeqCtx (Γ₁ := D' :: Γ) ⟨hΓ, _, hD'⟩ hctx hC'
    rw [Ectx] at EC'
    have hC' := hC'.defeqDFC henv hctx
    have EΓD := congr (congrArg List.cons ED) EΓ
    change proofEraseCtx (D :: Γ) = _ at EΓD
    have HCC := source_infer hsource HC hΓD hC hC' EΓD EC EC'
      (not_isProof_of_sort hΓD hC) (not_isProof_of_sort hΓD hC')
    apply CarrierAlignedCompare.forallE (ihD hΓ hD HDD.hasType.2 EΓ ED ED' W)
    simpa only [proofEraseCtx, proofErase_subst_with W.target_wf W.left hD W.left_erasure, ED] using
      (ihC hΓD hC HCC.hasType.2 EΓD EC EC' (W.cons hstep hrename hD))
  | forallSorted SD SD' HD SC SC' HC ihD ihC =>
    intro Γ a b A Γ₀ σ φ ρ τ hΓ ha hb EΓ Ea Eb W
    obtain ⟨D, C, rfl, _, ED, EC⟩ := erase_forallE_inv Ea
    obtain ⟨D', C', rfl, _, ED', EC'⟩ := erase_forallE_inv Eb
    obtain ⟨⟨_, hD⟩, _, hC⟩ := ha.forallE_inv henv
    obtain ⟨⟨_, hD'⟩, _, hC'⟩ := hb.forallE_inv henv
    have hD := domain_sort_raw SD hΓ hD EΓ ED
    have hD' := domain_sort_raw SD' hΓ hD' EΓ ED'
    have HDD := source_common hsource HD hΓ hD hD' EΓ ED ED'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, hD⟩
    have hctx := IsDefEqCtx.succ .zero HDD.symm
    have Ectx := proofErase_defeqCtx (Γ₁ := D' :: Γ) ⟨hΓ, _, hD'⟩ hctx hC'
    rw [Ectx] at EC'
    have hC' := hC'.defeqDFC henv hctx
    have EΓD := congr (congrArg List.cons ED) EΓ
    change proofEraseCtx (D :: Γ) = _ at EΓD
    have hC := domain_sort_raw SC hΓD hC EΓD EC
    have hC' := domain_sort_raw SC' hΓD hC' EΓD EC'
    have WL := W.cons hstep hrename hD
    have HC' := ihC hΓD hC hC' EΓD EC EC' WL
    have SL := left_sort WL EΓD SC
    have SR := right_sort WL EΓD SC'
    simp only [proofEraseCtx, proofErase_subst_with W.target_wf W.left hD W.left_erasure, ED] at HC' SL SR
    exact .forallSorted (left_sort W EΓ SD) (right_sort W EΓ SD') (ihD hΓ hD hD' EΓ ED ED' W) SL SR HC'
  | etaBodyL SD HB ihB =>
    intro Γ a b A Γ₀ σ φ ρ τ hΓ ha hb EΓ Ea Eb W
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
    apply CarrierAlignedCompare.etaBodyL (left_sort W EΓ SD)
    simpa only [proofEraseCtx, proofErase_subst_with W.target_wf W.left hD W.left_erasure, ED, ProofShape.subst, etaArgument_subst, ProofShape.lift_subst_lift] using
      ihB hΓD hbody hη (by simp only [proofEraseCtx, EΓ, ED]) Ebody Eη (W.cons hstep hrename hD)
  | etaBodyR SD HB ihB =>
    intro Γ a b A Γ₀ σ φ ρ τ hΓ ha hb EΓ Ea Eb W
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
    apply CarrierAlignedCompare.etaBodyR (right_sort W EΓ SD)
    simpa only [proofEraseCtx, proofErase_subst_with W.target_wf W.right hD W.right_erasure, ED, ProofShape.subst, etaArgument_subst, ProofShape.lift_subst_lift] using
      ihB hΓD hη hbody (by simp only [proofEraseCtx, EΓ, ED]) Eη Ebody (W.cons_right hstep hrename hD)
  | @structFields Δ family info ls ps fields major hi hx hp hf hadm Hfields ihfields =>
    intro Γ a b A Γ₀ σ φ ρ τ hΓ ha hb EΓ Ea Eb W
    have HE := source_common hsource (.structFields hi hx hp hf hadm Hfields) hΓ ha hb EΓ Ea Eb
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
  | etaLams HD Hη ihD =>
    intro Γ a b A Γ₀ σ φ ρ τ hΓ ha hb EΓ Ea Eb W
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    have Ebody₀ := Ebody'
    rw [Ectx] at Ebody'
    have WL := W.cons hstep hrename hD
    have HD' := ihD hΓ hD hD' EΓ ED ED' W
    apply CarrierAlignedCompare.lam HD'
    have HB : CarrierAlignedCompare Step (proofEraseCtx (D.subst σ :: Γ₀)) false
        ((proofErase (D :: Γ) body).subst ρ.lift) ((proofErase (D :: Γ) body').subst τ.lift) := by
      rcases Hη with HE | HE
      · have RB := proofErase_eta_lambda_bodies_beta hΓ ha hb (by simpa only [Ea, Eb] using HE)
        rw [Ectx] at RB
        exact .compute (.beta RB.subst) .refl
          (proofErase_carrier_aligned_subst_images hrename WL.target_wf WL.left hbody' WL.left_erasure WL.images)
      · have RC := proofErase_eta_lambda_bodies_beta hΓ hb ha (by simpa only [Ea, Eb] using HE)
        rw [Ectx] at RC
        exact .compute .refl (.beta RC.subst)
          (proofErase_carrier_aligned_subst_images hrename WL.target_wf WL.left hbody WL.left_erasure WL.images)
    simpa only [proofEraseCtx, proofErase_subst_with W.target_wf W.left hD W.left_erasure, ED, Ebody, Ebody'] using inferred_mode HB
  | compute Ra Rb HC ih =>
    intro Γ a b A Γ₀ σ φ ρ τ hΓ ha hb EΓ Ea Eb W
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hsource hΓ ha EΓ Ea Ra
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hsource hΓ hb EΓ Eb Rb
    have WL : ContextSubstitution (proofEraseCtx Γ) (proofEraseCtx Γ₀) ρ :=
      ContextSubstitution.of_typed W.target_wf W.left W.left_erasure
    have WR : ContextSubstitution (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ :=
      ContextSubstitution.of_typed W.target_wf W.right W.right_erasure
    exact .compute (Ra.subst_typed hsource hsubst hΓ ha EΓ Ea (by rw [← EΓ]; exact WL))
      (Rb.subst_typed hsource hsubst hΓ hb EΓ Eb (by rw [← EΓ]; exact WR))
      (ih hΓ HA.hasType.2 HB.hasType.2 EΓ EA EB W)
  | symm HC ih =>
    intro Γ a b A Γ₀ σ φ ρ τ hΓ ha hb EΓ Ea Eb W
    exact .symm (ih hΓ hb ha EΓ Eb Ea W.symm)

/-- The complete scoped comparison transports under paired maps when each
source primitive has a proved typed substitution simulation. This explicit
primitive interface is independent of the body comparison being transported. -/
theorem proofErase_carrier_aligned_scoped_paired_substitution_with_primitives
    (hsource : ErasedScopedPrimitiveDescent Source)
    (hsubst : ErasedPrimitiveSubstitutionTo Source Step)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ → Step Δ' (a.subst τ) (b.subst τ))
    (W : CarrierAlignedSubstitution Step Γ Γ₀ σ φ ρ τ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : ScopedCompare Source (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b)) :
    CarrierAlignedCompare Step (proofEraseCtx Γ₀) mode
      (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst φ)) := by
  rw [proofErase_subst_with W.target_wf W.left ha W.left_erasure,
    proofErase_subst_with W.target_wf W.right hb W.right_erasure]
  exact scoped_paired_transport hsource hsubst hstep hrename H W.left.wf ha hb rfl rfl rfl W

/-- Every primitive-free scoped comparison survives paired interpreted
substitution at inferred-related images. Recursive eta, structure fields and
sorted binders are included; no native image recovery or body-join premise is
required. Source computations here are beta-only. -/
theorem proofErase_carrier_aligned_scoped_paired_substitution
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (W : CarrierAlignedSubstitution Step Γ Γ₀ σ φ ρ τ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : ScopedCompare (fun _ _ _ => False) (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b)) :
    CarrierAlignedCompare Step (proofEraseCtx Γ₀) mode
      (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst φ)) := by
  rw [proofErase_subst_with W.target_wf W.left ha W.left_erasure,
    proofErase_subst_with W.target_wf W.right hb W.right_erasure]
  exact scoped_paired_transport empty_descent (by intro Γ Γ₀ σ τ e T out hΓ₀ W E ht H; exact H.elim)
    hstep hrename H W.left.wf ha hb rfl rfl rfl W

/-- Two actual arguments of one declared domain give paired interpreted maps
as soon as their erased images compare in inferred mode. -/
theorem CarrierAlignedSubstitution.inst
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) false (proofErase Γ x) (proofErase Γ y)) :
    CarrierAlignedSubstitution Step (A :: Γ) Γ (VExpr.Subst.one x) (VExpr.Subst.one y)
      (ProofShape.Subst.one (proofErase Γ x)) (ProofShape.Subst.one (proofErase Γ y)) := by
  refine ⟨hΓA.1, (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx,
    (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := y) (A₀ := A)).substEq hΓA hy,
    erasedSubstAgreement_one hΓA hx, erasedSubstAgreement_one hΓA hy, ?_⟩
  intro i
  cases i with
  | zero => exact H
  | succ i => exact .computed (.leaf .refl)

/-- Full primitive-free scoped body checking instantiates at two related
arguments. No recovery at the assigned domain or join of the images is needed. -/
theorem proofErase_carrier_aligned_scoped_paired_inst
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (Himages : CarrierAlignedCompare Step (proofEraseCtx Γ) false (proofErase Γ x) (proofErase Γ y))
    (H : ScopedCompare (fun _ _ _ => False) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    CarrierAlignedCompare Step (proofEraseCtx Γ) mode (proofErase Γ (a.inst x)) (proofErase Γ (b.inst y)) := by
  simpa only [VExpr.inst_eq] using proofErase_carrier_aligned_scoped_paired_substitution hstep hrename
    (CarrierAlignedSubstitution.inst hΓA hx hy Himages) ha hb H

end Lean4Lean.VEnv.Strengthening
