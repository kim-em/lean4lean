import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSemanticRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCertifiedChecking
import Lean4Lean.Theory.Typing.Strengthening.StructureEtaUniverses

/-! # Joint checking under semantic context and carrier conversion

Head exposure remains an explicit premise. The mutual induction transports
checking through actual context conversion and changes carrier types by
ordinary typed equality. No arbitrary assigned-type recovery is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private infer_raw common_raw carrier_raw domain_sort_raw lambda_common_context
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointTransport
open private compute_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSemanticRecovery
variable [Params]

private theorem sort_convert
    (_hΓ : OnCtx Γ (env.IsType univs)) (W : IsDefEqCtx env univs [] Γ Γ')
    (EΓ : proofEraseCtx Γ = Δ) (S : DomainSort Δ A u) :
    DomainSort (proofEraseCtx Γ') A u := by
  rw [← EΓ] at S
  simpa only [ProofShape.subst_id] using
    ContextSubstitution.sort (ContextSubstitution.of_defeqCtx (by trivial) W) S

private theorem compute_convert
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (W : IsDefEqCtx env univs [] Γ Γ') (EΓ : proofEraseCtx Γ = Δ)
    (R : ScopedCompute Step Δ a b) : ScopedCompute Step (proofEraseCtx Γ') a b := by
  rw [← EΓ] at R
  exact R.defeqCtx hsubst (by trivial) W

private theorem record_conversion_metadata
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : args.length = info.nparams) (hp' : args'.length = info.nparams)
    (hx : info.nindices = 0)
    (ha : env.HasType univs Γ a (VExpr.mkApps (.const family ls) args))
    (ha' : env.HasType univs Γ a (VExpr.mkApps (.const family ls') args'))
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls) :
    ((info.resultLevel.inst ls').IsNeverZero ∨ StructureReplay.ProofFields env univs info ls') ∧
      (∀ i, i < info.numFields → StructureReplay.ProofField env univs info ls i →
        StructureReplay.ProofField env univs info ls' i) := by
  have hexp := (StructureReplay.expansion_typed_iff henv hΓ hi hp hx ha).2 hadm
  have hexp' := hexp.defeqU_r henv hΓ (ha.uniqU henv hΓ ha')
  obtain ⟨hw, hl, hw', Hls⟩ := StructureReplay.constructor_levels henv hΓ hi
    (by simp only [List.length_append, List.length_map, List.length_range, hp]) hexp'
  have hadm' : (info.resultLevel.inst ls').IsNeverZero ∨ StructureReplay.ProofFields env univs info ls' := by
    rcases hadm with H | H
    · exact .inl (H.of_equiv (VLevel.inst_congr rfl Hls))
    · exact .inr (H.level_congr henv hi hw hw' hl Hls)
  refine ⟨hadm', ?_⟩
  intro i hj HF
  exact StructureReplay.ProofField.of_projection hΓ hi hp' hj
    ((StructureReplay.expansion_typed_iff henv hΓ hi hp' hx ha').2 hadm')
    (HF.projection hΓ hi hp hexp)

/-- Simultaneous semantic transport of both checking modes. Expression
endpoints stay fixed; carrier checking also permits any ordinarily equal type
in the converted target context. -/
def JointSemanticConversionResult
    (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (kind : JointCheckKind) (sa sb : ProofShape) : Prop :=
  match kind with
  | .compare mode => ∀ {Γ a b A Γ'}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ a A → env.HasType univs Γ b A → proofEraseCtx Γ = Δ →
      proofErase Γ a = sa → proofErase Γ b = sb → IsDefEqCtx env univs [] Γ Γ' →
      JointCompare Step (proofEraseCtx Γ') mode sa sb
  | .carrier α => ∀ {Γ a b A Γ'}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ a A → env.HasType univs Γ b A → proofEraseCtx Γ = Δ →
      proofErase Γ A = α → proofErase Γ a = sa → proofErase Γ b = sb →
      IsDefEqCtx env univs [] Γ Γ' → ∀ U v, env.HasType univs Γ' U (.sort v) →
      env.IsDefEqU univs Γ' A U → JointCarrierGuard Step (proofEraseCtx Γ') (proofErase Γ' U) sa sb

/-- Semantic head exposure and exact primitive context transport suffice for
joint checking through context and carrier conversion. The application case
selects a newly recovered Pi and invokes the smaller argument-guard induction
at its native domain. Head exposure itself is still an unproved premise. -/
theorem ProofShape.JointCheck.semantic_conversion
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (Hheads : ScopedSemanticHeadExposure Step)
    (H : JointCheck Step Δ kind sa sb) : JointSemanticConversionResult Step Δ kind sa sb := by
  induction H with
  | leaf H =>
    intro Γ a b A Γ' hΓ ha hb EΓ Ea Eb W
    exact .leaf H
  | app HF HX ihf ihx =>
    intro Γ a b A Γ' hΓ ha hb EΓ Ea Eb W
    obtain ⟨f, x, rfl, hna, Ef, Ex⟩ := erase_app_inv Ea
    obtain ⟨g, y, rfl, hnb, Eg, Ey⟩ := erase_app_inv Eb
    obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
    obtain ⟨_, _, hg, hy⟩ := hb.app_inv henv hΓ
    have HE := infer_raw hstep HF hΓ hf hg EΓ Ef Eg
      (not_isProof_fn hΓ hf hx hna) (not_isProof_fn hΓ hg hy hnb)
    have hy' := argument_at_displayed_domain hΓ hg HE.hasType.2 hy
    exact .app (ihf hΓ hf HE.hasType.2 EΓ Ef Eg W) (ihx hΓ hx hy' EΓ Ex Ey W)
  | appCarrier R HF HX ihf ihx =>
    intro Γ a b A Γ' hΓ ha hb EΓ Ea Eb W
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
    have hΓ' := (W.symm henv.ordered).isType
    have hf' := hfPi.defeqDFC henv W
    have hnf' : ¬ IsProof Γ' f := mt (isProof_defeqCtx W).2 (not_isProof_fn hΓ hf hx hna)
    obtain ⟨out, RF⟩ := Hheads.recovery_exists hstep hΓ' hf' hnf'
    obtain ⟨rawD, rawC, RF⟩ := Hheads.recover_pi hstep hΓ' hf' RF
    obtain ⟨D', C', hfNew, ED', EC'⟩ := proofErase_scoped_recovered_pi_descend hstep hΓ' hΓ'
      (show Ctx.LiftN 0 0 Γ' Γ' from .zero []) hf'
      (by simpa only [ProofShape.liftN_zero] using RF)
    obtain ⟨⟨_, hD'⟩, _, _⟩ := (hfNew.isType henv hΓ').forallE_inv henv
    have HDD := (hf'.uniqU henv hΓ' hfNew).forallE_inv henv hΓ' |>.1
    have HX' := ihx hΓ hxD hyD EΓ (by simpa only [ProofShape.liftN_zero] using ED)
      Ex Ey W D' _ hD' ⟨_, HDD.choose_spec⟩
    rw [show proofErase Γ' f = _ from (proofErase_defeqCtx hΓ W hfPi).symm.trans Ef] at RF
    simp only [ProofShape.liftN_zero] at ED'
    rw [ED'] at HX'
    exact .appCarrier RF (ihf hΓ hf HE.hasType.2 EΓ Ef Eg W) HX'

  | proj HM ihm =>
    intro Γ a b A Γ' hΓ ha hb EΓ Ea Eb W
    obtain ⟨m, rfl, hn, Em⟩ := erase_proj_inv Ea
    obtain ⟨m', rfl, hn', Em'⟩ := erase_proj_inv Eb
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm', _, _⟩ := hb.proj_inv henv hΓ
    have HE := infer_raw hstep HM hΓ hm.hasType.2 hm'.hasType.2 EΓ Em Em'
      (not_isProof_major hΓ ha hn) (not_isProof_major hΓ hb hn')
    exact .proj (ihm hΓ hm.hasType.2 HE.hasType.2 EΓ Em Em' W)
  | lam HD HB ihD ihB =>
    intro Γ a b A Γ' hΓ ha hb EΓ Ea Eb W
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HB' := ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED]) Ebody Ebody' (.succ W hD)
    apply JointCheck.lam (ihD hΓ hD hD' EΓ ED ED' W)
    simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using HB'
  | lamSorted SD SD' HD HB ihD ihB =>
    intro Γ a b A Γ' hΓ ha hb EΓ Ea Eb W
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HB' := ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED]) Ebody Ebody' (.succ W hD)
    apply JointCheck.lamSorted (sort_convert hΓ W EΓ SD) (sort_convert hΓ W EΓ SD') (ihD hΓ hD hD' EΓ ED ED' W)
    simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using HB'
  | lamCommon HB ihB =>
    intro Γ a b A Γ' hΓ ha hb EΓ Ea Eb W
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HB' := ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED]) Ebody Ebody' (.succ W hD)
    apply JointCheck.lamCommon
    simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using HB'
  | etaLams HD Hη ihD =>
    intro Γ a b A Γ' hΓ ha hb EΓ Ea Eb W
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    exact .etaLams (ihD hΓ hD hD' EΓ ED ED' W) (Hη.imp (fun H => H) (fun H => H))
  | forallE HD HC ihD ihC =>
    intro Γ a b A Γ' hΓ ha hb EΓ Ea Eb W
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
    apply JointCheck.forallE (ihD hΓ hD HDD.hasType.2 EΓ ED ED' W)
    simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using
      ihC hΓD hC HCC.hasType.2 EΓD EC EC' (.succ W hD)
  | forallSorted SD SD' HD SC SC' HC ihD ihC =>
    intro Γ a b A Γ' hΓ ha hb EΓ Ea Eb W
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
    have SCt := sort_convert hΓD (.succ W hD) EΓD SC
    have SCt' := sort_convert hΓD (.succ W hD) EΓD SC'
    have HCt := ihC hΓD hC hC' EΓD EC EC' (.succ W hD)
    simp only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] at SCt SCt' HCt
    exact .forallSorted (sort_convert hΓ W EΓ SD) (sort_convert hΓ W EΓ SD')
      (ihD hΓ hD hD' EΓ ED ED' W) SCt SCt' HCt
  | etaBodyL SD HB ihB =>
    intro Γ a b A Γ' hΓ ha hb EΓ Ea Eb W
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
    apply JointCheck.etaBodyL (sort_convert hΓ W EΓ SD)
    simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using
      ihB hΓD hbody hη (by simp only [proofEraseCtx, EΓ, ED]) Ebody Eη (.succ W hD)
  | etaBodyR SD HB ihB =>
    intro Γ a b A Γ' hΓ ha hb EΓ Ea Eb W
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
    apply JointCheck.etaBodyR (sort_convert hΓ W EΓ SD)
    simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hD, ED] using
      ihB hΓD hη hbody (by simp only [proofEraseCtx, EΓ, ED]) Eη Ebody (.succ W hD)
  | @structFields Δ family info ls ps fields major hi hx hp hf hadm Hfields ihfields =>
    intro Γ a b A Γ' hΓ ha hb EΓ Ea Eb W
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
    exact ihfields i hj hn hΓ hxt hpt EΓ Ex Ep W
  | compute Ra Rb HC ih =>
    intro Γ a b A Γ' hΓ ha hb EΓ Ea Eb W
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea Ra
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb Rb
    exact .compute (compute_convert hsubst W EΓ Ra)
      (compute_convert hsubst W EΓ Rb)
      (ih hΓ HA.hasType.2 HB.hasType.2 EΓ EA EB W)
  | symm HC ih =>
    intro Γ a b A Γ' hΓ ha hb EΓ Ea Eb W
    exact .symm (ih hΓ hb ha EΓ Eb Ea W)
  | carrierChecked HC ih =>
    intro Γ a b A Γ' hΓ ha hb EΓ Eα Ea Eb W U v hU HAU
    exact .carrierChecked (ih hΓ ha hb EΓ Ea Eb W)
  | carrierSubsingleton HS =>
    intro Γ a b A Γ' hΓ ha hb EΓ Eα Ea Eb W U v hU HAU
    obtain ⟨u, hA⟩ := ha.isType henv hΓ
    have HS' : SubsingletonCarrier (proofErase Γ' A) := by
      rw [← proofErase_defeqCtx hΓ W hA, Eα]
      exact HS
    exact Hheads.subsingleton_guard hstep hsubst (W.symm henv.ordered).isType
      (hA.defeqDFC henv W) hU HAU HS'

  | carrierSymm HC ih =>
    intro Γ a b A Γ' hΓ ha hb EΓ Eα Ea Eb W U v hU HAU
    exact .carrierSymm (ih hΓ hb ha EΓ Eα Eb Ea W U v hU HAU)
  | carrierCompute RC HC ih =>
    intro Γ a b A Γ' hΓ ha hb EΓ Eα Ea Eb W U v hU HAU
    obtain ⟨u, hA⟩ := ha.isType henv hΓ
    obtain ⟨A', HE, EA⟩ := proofErase_scoped_compute_realize hstep hΓ hA EΓ Eα RC
    exact ih hΓ (HE.defeq ha) (HE.defeq hb) EΓ EA Ea Eb W U v hU
      ((show env.IsDefEqU univs Γ' A' A from ⟨_, HE.symm.defeqDFC henv W⟩).trans
        henv (W.symm henv.ordered).isType HAU)

  | carrierReduce Ra Rb HC ih =>
    intro Γ a b A Γ' hΓ ha hb EΓ Eα Ea Eb W U v hU HAU
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea Ra
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb Rb
    exact .carrierReduce (compute_convert hsubst W EΓ Ra)
      (compute_convert hsubst W EΓ Rb)
      (ih hΓ HA.hasType.2 HB.hasType.2 EΓ Eα EA EB W U v hU HAU)
  | carrierFunction SD HC ih =>
    intro Γ a b A Γ' hΓ ha hb EΓ Eα Ea Eb W U v hU HAU
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
    have hΓ' := (W.symm henv.ordered).isType
    obtain ⟨D', C', hPi', RP⟩ := Hheads.pi hΓ' hU HAU.symm
    have HPi := HAU.trans henv hΓ' (compute_eq hstep hΓ' hU hPi' RP)
    obtain ⟨⟨_, HDD⟩, _, HCC⟩ := HPi.forallE_inv henv hΓ'
    have HD := (show env.IsDefEqU univs Γ D D' from
      ⟨_, HDD.defeqDFC henv (W.symm henv.ordered)⟩).of_l henv hΓ hD
    have hD't := HD.hasType.2.defeqDFC henv W
    have WB : IsDefEqCtx env univs [] (D :: Γ) (D' :: Γ') := .succ W HD
    have HC' := HCC.defeqDFC henv (.succ .zero HDD)
    obtain ⟨_, _, hC'⟩ := hPi'.forallE_inv henv
    have HB := ih hΓD hfa hfb (by simp only [proofEraseCtx, EΓ, ED]) EC Efa Efb
      WB C' _ hC' ⟨_, HC'⟩
    rw [show proofErase Γ' (.forallE D' C') = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ' hPi')] at RP
    exact .carrierCompute RP (.carrierFunction (.of_typed hΓ' hD't) HB)

  | @carrierIntro family info ls Δ sa sb ps hi hx hp hadm Hfields ihfields =>
    intro Γ a b A Γ' hΓ ha hb EΓ Eα Ea Eb W U v hU HAU
    have HE := carrier_raw hstep (.carrierIntro hi hx hp hadm Hfields) hΓ ha hb EΓ Eα Ea Eb
    obtain ⟨args, rfl, Eargs⟩ := proofErase_const_spine_inv Eα
    have hlen : args.length = info.nparams := by
      have HH := congrArg List.length Eargs
      simp only [List.length_map] at HH
      omega
    have hexpa := (StructureReplay.expansion_typed_iff henv hΓ hi hlen hx ha).2 hadm
    have hΓ' := (W.symm henv.ordered).isType
    obtain ⟨ls', args', hF, RF⟩ := Hheads.family hΓ' hU hi HAU.symm
    have HAF := HAU.trans henv hΓ' (compute_eq hstep hΓ' hU hF RF)
    have hat := (ha.defeqDFC henv W).defeqU_r henv hΓ' HAF
    have hlen' : args'.length = info.nparams := by
      simpa only [hx, Nat.add_zero] using StructureReplay.family_arity henv hΓ' hi ⟨_, hF⟩
    obtain ⟨hadm', hflags⟩ := record_conversion_metadata hΓ' hi hlen hlen' hx
      (ha.defeqDFC henv W) hat hadm
    rw [proofErase_const_spine hΓ' hF (not_isProof_of_sort hΓ' hF)] at RF
    apply JointCheck.carrierCompute RF
    apply JointCheck.carrierIntro hi hx (by simpa only [List.length_map] using hlen') hadm'
    intro i hj hnt
    have hn : ¬ StructureReplay.ProofField env univs info ls i := fun HF => hnt (hflags i hj HF)
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
    intro Γ a b A Γ' hΓ ha hb EΓ Eα Ea Eb W U v hU HAU
    have HE := carrier_raw hstep (.carrierNested hi hx hp hadm HT Hfields) hΓ ha hb EΓ Eα Ea Eb
    obtain ⟨args, rfl, Eargs⟩ := proofErase_const_spine_inv Eα
    have hlen : args.length = info.nparams := by
      have HH := congrArg List.length Eargs
      simp only [List.length_map] at HH
      omega
    have hexpa := (StructureReplay.expansion_typed_iff henv hΓ hi hlen hx ha).2 hadm
    have hΓ' := (W.symm henv.ordered).isType
    obtain ⟨ls', args', hF, RF⟩ := Hheads.family hΓ' hU hi HAU.symm
    have HAF := HAU.trans henv hΓ' (compute_eq hstep hΓ' hU hF RF)
    have hat := (ha.defeqDFC henv W).defeqU_r henv hΓ' HAF
    have hlen' : args'.length = info.nparams := by
      simpa only [hx, Nat.add_zero] using StructureReplay.family_arity henv hΓ' hi ⟨_, hF⟩
    obtain ⟨hadm', hflags⟩ := record_conversion_metadata hΓ' hi hlen hlen' hx
      (ha.defeqDFC henv W) hat hadm
    rw [proofErase_const_spine hΓ' hF (not_isProof_of_sort hΓ' hF)] at RF
    obtain ⟨_, hhead⟩ := (show VExpr.WF env univs Γ' (VExpr.mkApps (.const family ls') args') from
      ⟨_, hF⟩).of_mkApps henv hΓ'
    obtain ⟨_, _, hw, _⟩ := HasType.const_inv henv hΓ' hhead
    obtain ⟨doms', result', HT'⟩ := projection_telescope_exists hi hw
    apply JointCheck.carrierCompute RF
    apply JointCheck.carrierNested hi hx (by simpa only [List.length_map] using hlen') hadm' HT'
    intro i hj hnt
    have hn : ¬ StructureReplay.ProofField env univs info ls i := fun HF => hnt (hflags i hj HF)
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
    have hpat : ¬ IsProof Γ' (.proj family i a) := mt (isProof_defeqCtx W).2 hpa
    obtain ⟨hjt, Ft, hiat, EFt⟩ := proofErase_projection_at_recovered_family hΓ' hi HT'
      (hia.defeqDFC henv W) hpat hat
    have Eat : proofErase Γ' a = sa := (proofErase_defeqCtx hΓ W ha).symm.trans Ea
    have EFt' : proofErase Γ' Ft = projectionType family info doms' i hjt
        (args'.map (proofErase Γ')) sa := by
      simpa only [projectionType, List.map_take, Eat] using EFt
    obtain ⟨vt, hFt⟩ := hiat.isType henv hΓ'
    have HFt := (hiaF.defeqDFC henv W).uniqU henv hΓ' hiat
    have Hfield := ihfields i hj hn hΓ hiaF hibF EΓ EF' Epa Epb W Ft vt hFt HFt
    rwa [EFt'] at Hfield

/-- Both comparison modes survive arbitrary ordinary context conversion under
semantic head exposure. No recovery output is prescribed in the new context. -/
theorem proofErase_joint_compare_context_of_heads
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (Hheads : ScopedSemanticHeadExposure Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (W : IsDefEqCtx env univs [] Γ Γ')
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : JointCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b)) :
    JointCompare Step (proofEraseCtx Γ') mode (proofErase Γ' a) (proofErase Γ' b) := by
  have HC := H.semantic_conversion hstep hsubst Hheads hΓ ha hb rfl rfl rfl W
  rwa [proofErase_defeqCtx hΓ W ha, proofErase_defeqCtx hΓ W hb] at HC

/-- Every joint carrier guard survives ordinary type conversion under semantic
head exposure, including general function and dependent record guards. This
is a conditional theorem, not an assertion of head adequacy for the joint union. -/
theorem proofErase_joint_carrier_convert_of_heads
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (Hheads : ScopedSemanticHeadExposure Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (HE : env.IsDefEqU univs Γ A B)
    (H : JointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ a) (proofErase Γ b)) :
    JointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ B) (proofErase Γ a) (proofErase Γ b) := by
  obtain ⟨u, hA⟩ := ha.isType henv hΓ
  exact H.semantic_conversion hstep hsubst Hheads hΓ ha hb rfl rfl rfl rfl
    (.refl hΓ) B u (HE.of_l henv hΓ hA).hasType.2 HE

/-- The certified primitive relation already supplies all computation and
context-transport assumptions of semantic carrier conversion. Only its head
exposure premise is additionally required. -/
theorem proofErase_certified_carrier_convert_of_heads
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (Hheads : ScopedSemanticHeadExposure (ErasedBetaStableJoint D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (HE : env.IsDefEqU univs Γ A B)
    (H : JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ a) (proofErase Γ b)) :
    JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ)
      (proofErase Γ B) (proofErase Γ a) (proofErase Γ b) :=
  proofErase_joint_carrier_convert_of_heads (erased_beta_stable_joint_descent heq hs)
    (erased_beta_stable_joint_subst heq hs) Hheads hΓ ha hb HE H

end Lean4Lean.VEnv.Strengthening
