import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreContextReduction

/-! # Simultaneous forward transport of core comparison and carrier guards

Context oracles and explicit carriers may both compute forward. Recovered
applications choose a new Pi, then invoke the carrier induction hypothesis at
its computed domain. Function carriers additionally reduce the fresh binder.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private infer_raw common_raw carrier_raw domain_sort_raw lambda_common_context
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointTransport
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private forall_parts projection_compute from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreRecoveryReduction
open private forget_scope from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreOracleReduction
variable [Params]

/-- Typed forward transport of comparison, or of a guard whose carrier may
also compute. The raw endpoints stay fixed in both modes. -/
def CoreCheckReductionResult (hq : QuotRegistered env)
    (Δ : List ProofShape) (kind : JointCheckKind) (sa sb : ProofShape) : Prop :=
  match kind with
  | .compare mode => ∀ {Γ a b A Δ'}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ a A → env.HasType univs Γ b A → proofEraseCtx Γ = Δ →
      proofErase Γ a = sa → proofErase Γ b = sb → ErasedQuotCore.ContextReduction hq Δ Δ' →
      JointCompare (fun _ => ErasedQuotCore.Step hq) Δ' mode sa sb
  | .carrier α => ∀ {Γ a b A Δ' target}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ a A → env.HasType univs Γ b A → proofEraseCtx Γ = Δ →
      proofErase Γ A = α → proofErase Γ a = sa → proofErase Γ b = sb →
      ErasedQuotCore.ContextReduction hq Δ Δ' → Compute (ErasedQuotCore.Step hq) α target →
      JointCarrierGuard (fun _ => ErasedQuotCore.Step hq) Δ' target sa sb

/-- All joint checking rules over the repaired ordinary core survive forward
oracle computation and, in carrier mode, forward computation of the carrier.
The proof treats recovered applications and recursive carrier guards together. -/
theorem ProofShape.JointCheck.quot_core_reduce_typed
    (hq : QuotRegistered env) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (H : JointCheck (fun _ => ErasedQuotCore.Step hq) Δ kind sa sb) :
    CoreCheckReductionResult hq Δ kind sa sb := by
  let hstep : ErasedScopedPrimitiveDescent (fun _ => ErasedQuotCore.Step hq) :=
    ErasedPrimitiveReplay.toDescent (ErasedQuotCore.sound hq) (erased_iota_replay (ErasedQuotCore.sound hq))
  induction H with
  | leaf H =>
    intro Γ a b A Δ' hΓ ha hb EΓ Ea Eb W
    exact .leaf H
  | app HF HX ihf ihx =>
    intro Γ a b A Δ' hΓ ha hb EΓ Ea Eb W
    obtain ⟨f, x, rfl, hna, Ef, Ex⟩ := erase_app_inv Ea
    obtain ⟨g, y, rfl, hnb, Eg, Ey⟩ := erase_app_inv Eb
    obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
    obtain ⟨_, _, hg, hy⟩ := hb.app_inv henv hΓ
    have HE := infer_raw hstep HF hΓ hf hg EΓ Ef Eg
      (not_isProof_fn hΓ hf hx hna) (not_isProof_fn hΓ hg hy hnb)
    have hy' := argument_at_displayed_domain hΓ hg HE.hasType.2 hy
    exact .app (ihf hΓ hf HE.hasType.2 EΓ Ef Eg W) (ihx hΓ hx hy' EΓ Ex Ey W)
  | appCarrier R HF HX ihf ihx =>
    intro Γ a b A Δ' hΓ ha hb EΓ Ea Eb W
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
    obtain ⟨A', B', R', HA, _⟩ := ErasedQuotCore.recovery_pi_oracle_reduce hq hcon hΓ hf
      (by simpa only [EΓ] using W.lookup) (by simpa only [EΓ, Ef] using R)
    exact .appCarrier (by simpa only [Ef] using R') (ihf hΓ hf HE.hasType.2 EΓ Ef Eg W)
      (ihx hΓ hxD hyD EΓ (by simpa only [ProofShape.liftN_zero] using ED) Ex Ey W HA)
  | proj HM ihm =>
    intro Γ a b A Δ' hΓ ha hb EΓ Ea Eb W
    obtain ⟨m, rfl, hn, Em⟩ := erase_proj_inv Ea
    obtain ⟨m', rfl, hn', Em'⟩ := erase_proj_inv Eb
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm', _, _⟩ := hb.proj_inv henv hΓ
    have HE := infer_raw hstep HM hΓ hm.hasType.2 hm'.hasType.2 EΓ Em Em'
      (not_isProof_major hΓ ha hn) (not_isProof_major hΓ hb hn')
    exact .proj (ihm hΓ hm.hasType.2 HE.hasType.2 EΓ Em Em' W)
  | lam HD HB ihD ihB =>
    intro Γ a b A Δ' hΓ ha hb EΓ Ea Eb W
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HB' := ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED]) Ebody Ebody' W.cons
    exact .lam (ihD hΓ hD hD' EΓ ED ED' W) HB'
  | lamSorted SD SD' HD HB ihD ihB =>
    intro Γ a b A Δ' hΓ ha hb EΓ Ea Eb W
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HB' := ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED]) Ebody Ebody' W.cons
    exact .lamSorted (W.sort SD) (W.sort SD') (ihD hΓ hD hD' EΓ ED ED' W) HB'
  | lamCommon HB ihB =>
    intro Γ a b A Δ' hΓ ha hb EΓ Ea Eb W
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HB' := ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED]) Ebody Ebody' W.cons
    exact .lamCommon HB'
  | etaLams HD Hη ihD =>
    intro Γ a b A Δ' hΓ ha hb EΓ Ea Eb W
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    exact .etaLams (ihD hΓ hD hD' EΓ ED ED' W) Hη
  | forallE HD HC ihD ihC =>
    intro Γ a b A Δ' hΓ ha hb EΓ Ea Eb W
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
      (ihC hΓD hC HCC.hasType.2 EΓD EC EC' W.cons)
  | forallSorted SD SD' HD SC SC' HC ihD ihC =>
    intro Γ a b A Δ' hΓ ha hb EΓ Ea Eb W
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
    exact .forallSorted (W.sort SD) (W.sort SD') (ihD hΓ hD hD' EΓ ED ED' W)
      (W.cons.sort SC) (W.cons.sort SC')
      (ihC hΓD hC hC' EΓD EC EC' W.cons)
  | etaBodyL SD HB ihB =>
    intro Γ a b A Δ' hΓ ha hb EΓ Ea Eb W
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
    apply JointCheck.etaBodyL (W.sort SD)
    exact
      ihB hΓD hbody hη (by simp only [proofEraseCtx, EΓ, ED]) Ebody Eη W.cons
  | etaBodyR SD HB ihB =>
    intro Γ a b A Δ' hΓ ha hb EΓ Ea Eb W
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
    apply JointCheck.etaBodyR (W.sort SD)
    exact
      ihB hΓD hη hbody (by simp only [proofEraseCtx, EΓ, ED]) Eη Ebody W.cons
  | @structFields Δ family info ls ps fields major hi hx hp hf hadm Hfields ihfields =>
    intro Γ a b A Δ' hΓ ha hb EΓ Ea Eb W
    have HE := common_raw hstep (.structFields hi hx hp hf hadm Hfields) hΓ ha hb EΓ Ea Eb
    apply JointCheck.structFields hi hx hp hf hadm
    intro i hj hn
    obtain ⟨x, X, hxt, hpt, Ex⟩ := proofErase_equal_structure_field_realize hΓ HE hi hx hp hf hadm Ea hj
    have hnx : ¬ IsProof Γ x := fun H => hn (Ex.symm.trans (proofErase_eq_proof.2 H))
    have hnp : ¬ IsProof Γ (.proj family i b) := by
      rintro ⟨P, hpP, hP⟩
      exact hnx ⟨P, hxt.defeqU_r henv hΓ (hpt.uniqU henv hΓ hpP), hP⟩
    have Ep : proofErase Γ (.proj family i b) = .proj family i major := by
      rw [show proofErase Γ (.proj family i b) = .proj family i (proofErase Γ b) from if_neg hnp, Eb]
    exact
      ihfields i hj hn hΓ hxt hpt EΓ Ex Ep W
  | compute Ra Rb HC ih =>
    intro Γ a b A Δ' hΓ ha hb EΓ Ea Eb W
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea Ra
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb Rb
    exact .compute ((forget_scope Ra).scoped (fun H => .base H))
      ((forget_scope Rb).scoped (fun H => .base H))
      (ih hΓ HA.hasType.2 HB.hasType.2 EΓ EA EB W)
  | symm HC ih =>
    intro Γ a b A Δ' hΓ ha hb EΓ Ea Eb W
    exact .symm (ih hΓ hb ha EΓ Eb Ea W)
  | carrierChecked HC ih =>
    intro Γ a b A Δ' target hΓ ha hb EΓ Eα Ea Eb W RC
    exact .carrierChecked (ih hΓ ha hb EΓ Ea Eb W)
  | carrierSubsingleton HS =>
    intro Γ a b A Δ' target hΓ ha hb EΓ Eα Ea Eb W RC
    exact .carrierSubsingleton (HS.quot_core_compute hq RC)
  | carrierSymm HC ih =>
    intro Γ a b A Δ' target hΓ ha hb EΓ Eα Ea Eb W RC
    exact .carrierSymm (ih hΓ hb ha EΓ Eα Eb Ea W RC)
  | carrierCompute Rold HC ih =>
    intro Γ a b A Δ' target hΓ ha hb EΓ Eα Ea Eb W RC
    obtain ⟨u, hA⟩ := ha.isType henv hΓ
    obtain ⟨A', HE, EA⟩ := proofErase_scoped_compute_realize hstep hΓ hA EΓ Eα Rold
    obtain ⟨shared, Htarget, Hmid⟩ := ErasedQuotCore.confluent hq hcon hΓ hA
      (by simpa only [Eα] using RC) (by simpa only [Eα] using forget_scope Rold)
    exact .carrierCompute (Htarget.scoped (fun H => .base H))
      (ih hΓ (HE.defeq ha) (HE.defeq hb) EΓ EA Ea Eb W Hmid)
  | carrierReduce Ra Rb HC ih =>
    intro Γ a b A Δ' target hΓ ha hb EΓ Eα Ea Eb W RC
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea Ra
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb Rb
    exact .carrierReduce ((forget_scope Ra).scoped (fun H => .base H))
      ((forget_scope Rb).scoped (fun H => .base H))
      (ih hΓ HA.hasType.2 HB.hasType.2 EΓ Eα EA EB W RC)
  | carrierFunction SD HC ih =>
    intro Γ a b A Δ' target hΓ ha hb EΓ Eα Ea Eb W RC
    obtain ⟨newD, newC, rfl, RD, RC'⟩ := forall_parts hq RC
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
    apply JointCheck.carrierFunction (ErasedQuotCore.domainSort_compute hq (W.sort SD) RD)
    exact
      ih hΓD hfa hfb (by simp only [proofEraseCtx, EΓ, ED]) EC Efa Efb (W.cons_compute RD) RC'
  | @carrierIntro family info ls Δ sa sb ps hi hx hp hadm Hfields ihfields =>
    intro Γ a b A Δ' target hΓ ha hb EΓ Eα Ea Eb W RC
    have RC' := RC.scoped (Step' := fun _ => ErasedQuotCore.Step hq) (Δ := Δ') (fun H => .base H)
    obtain ⟨ps', rfl, Hps⟩ := RC'.const_spine (fun H =>
      erased_iota_primitive_no_rigid (henv.projectionRigid hi)
        (ErasedQuotCore.no_rigid hq (henv.projectionRigid hi)) H (ProofShape.constHead_mkApps _ _))
    have HE := carrier_raw hstep (.carrierIntro hi hx hp hadm Hfields) hΓ ha hb EΓ Eα Ea Eb
    obtain ⟨args, rfl, Eargs⟩ := proofErase_const_spine_inv Eα
    have hlen : args.length = info.nparams := by
      have HH := congrArg List.length Eargs
      simp only [List.length_map] at HH
      omega
    have hexpa := (StructureReplay.expansion_typed_iff henv hΓ hi hlen hx ha).2 hadm
    apply JointCheck.carrierIntro hi hx (Hps.length_eq.symm.trans hp) hadm
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
    intro Γ a b A Δ' target hΓ ha hb EΓ Eα Ea Eb W RC
    have RC' := RC.scoped (Step' := fun _ => ErasedQuotCore.Step hq) (Δ := Δ') (fun H => .base H)
    obtain ⟨ps', rfl, Hps⟩ := RC'.const_spine (fun H =>
      erased_iota_primitive_no_rigid (henv.projectionRigid hi)
        (ErasedQuotCore.no_rigid hq (henv.projectionRigid hi)) H (ProofShape.constHead_mkApps _ _))
    have HE := carrier_raw hstep (.carrierNested hi hx hp hadm HT Hfields) hΓ ha hb EΓ Eα Ea Eb
    obtain ⟨args, rfl, Eargs⟩ := proofErase_const_spine_inv Eα
    have hlen : args.length = info.nparams := by
      have HH := congrArg List.length Eargs
      simp only [List.length_map] at HH
      omega
    have hexpa := (StructureReplay.expansion_typed_iff henv hΓ hi hlen hx ha).2 hadm
    apply JointCheck.carrierNested hi hx (Hps.length_eq.symm.trans hp) hadm HT
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
    exact
      ihfields i hj hn hΓ hiaF hibF EΓ EF' Epa Epb W (projection_compute hq (Hps.imp (fun _ _ H => forget_scope H)))

end Lean4Lean.VEnv.Strengthening
