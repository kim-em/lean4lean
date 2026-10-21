import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextOracleBeta

/-! # Joint checking through beta changes of context and carrier types

Comparison endpoints stay fixed. Carrier types may beta-reduce simultaneously
with the context oracle. The mutual induction adapts a recovered application
domain using its carrier subderivation, rather than a global re-synthesis law.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private infer_raw common_raw carrier_raw domain_sort_raw lambda_common_context
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointTransport
open private beta_forallE_parts from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- Typed mutual transport result: the context oracle beta-reduces, endpoints
stay fixed, and the carrier mode additionally permits a beta-reduced type. -/
def JointOracleBetaResult
    (Target : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (kind : JointCheckKind) (sa sb : ProofShape) : Prop :=
  match kind with
  | .compare mode => ∀ {Γ a b A Δ'}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ a A → env.HasType univs Γ b A → proofEraseCtx Γ = Δ →
      proofErase Γ a = sa → proofErase Γ b = sb → ContextOracleBeta Δ Δ' →
      JointCompare Target Δ' mode sa sb
  | .carrier α => ∀ {Γ a b A Δ'}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ a A → env.HasType univs Γ b A → proofEraseCtx Γ = Δ →
      proofErase Γ A = α → proofErase Γ a = sa → proofErase Γ b = sb →
      ContextOracleBeta Δ Δ' → ∀ α', ProofShape.BetaRed α α' →
      JointCarrierGuard Target Δ' α' sa sb

/-- Every joint constructor transports using source-typed exact computation,
computation/beta commutation, and forward recovery through changed oracles.
The application case uses the recursive carrier hypothesis at the newly
recovered domain; neither arbitrary endpoint-beta comparison nor carrier-domain
re-synthesis is assumed. -/
theorem ProofShape.JointCheck.oracle_beta
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hcompute : ∀ {Γ Δ Δ' e T source out}, ScopedCompute Step Δ source out →
      OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      proofEraseCtx Γ = Δ → proofErase Γ e = source → ContextOracleBeta Δ Δ' →
      ScopedCompute Target Δ' source out)
    (hcommute : ∀ {Γ Δ' e T out reduced}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ e T → ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ e) out →
      ProofShape.BetaRed (proofErase Γ e) reduced → ContextOracleBeta (proofEraseCtx Γ) Δ' →
      ∃ shared, ProofShape.BetaRed out shared ∧ ScopedCompute Target Δ' reduced shared)
    (hrecover : ∀ {Γ Δ' e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ e) out →
      ContextOracleBeta (proofEraseCtx Γ) Δ' →
      ∃ out', ScopedTypeRecovery Target Δ' (proofErase Γ e) out' ∧ ProofShape.BetaRed out out')
    (H : JointCheck Step Δ kind sa sb) : JointOracleBetaResult Target Δ kind sa sb := by
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
    obtain ⟨out', R', RB⟩ := hrecover hΓ hfPi
      (by simpa only [EΓ, Ef] using R) (by simpa only [EΓ] using W)
    obtain ⟨A', B', rfl, RA, _⟩ := beta_forallE_parts RB
    have HX' := ihx hΓ hxD hyD EΓ (by simpa only [ProofShape.liftN_zero] using ED)
      Ex Ey W A' RA
    exact .appCarrier (by simpa only [Ef] using R')
      (ihf hΓ hf HE.hasType.2 EΓ Ef Eg W) HX'
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
    have HB' := ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED]) Ebody Ebody' (W.cons .refl)
    exact .lam (ihD hΓ hD hD' EΓ ED ED' W) HB'
  | lamSorted SD SD' HD HB ihD ihB =>
    intro Γ a b A Δ' hΓ ha hb EΓ Ea Eb W
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HB' := ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED]) Ebody Ebody' (W.cons .refl)
    exact .lamSorted (W.sort SD .refl) (W.sort SD' .refl) (ihD hΓ hD hD' EΓ ED ED' W) HB'
  | lamCommon HB ihB =>
    intro Γ a b A Δ' hΓ ha hb EΓ Ea Eb W
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HB' := ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED]) Ebody Ebody' (W.cons .refl)
    exact .lamCommon HB'
  | etaLams HD Hη ihD =>
    intro Γ a b A Δ' hΓ ha hb EΓ Ea Eb W
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    exact .etaLams (ihD hΓ hD hD' EΓ ED ED' W) (Hη.imp (fun H => H) (fun H => H))
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
      (ihC hΓD hC HCC.hasType.2 EΓD EC EC' (W.cons .refl))
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
    exact .forallSorted (W.sort SD .refl) (W.sort SD' .refl) (ihD hΓ hD hD' EΓ ED ED' W)
      ((W.cons .refl).sort SC .refl) ((W.cons .refl).sort SC' .refl)
      (ihC hΓD hC hC' EΓD EC EC' (W.cons .refl))
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
    apply JointCheck.etaBodyL (W.sort SD .refl)
    exact ihB hΓD hbody hη (by simp only [proofEraseCtx, EΓ, ED]) Ebody Eη (W.cons .refl)
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
    apply JointCheck.etaBodyR (W.sort SD .refl)
    exact ihB hΓD hη hbody (by simp only [proofEraseCtx, EΓ, ED]) Eη Ebody (W.cons .refl)
  | @structFields Δ family info ls ps fields major hi hx hp hf hadm Hfields ihfields =>
    intro Γ a b A Δ' hΓ ha hb EΓ Ea Eb W
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
    intro Γ a b A Δ' hΓ ha hb EΓ Ea Eb W
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea Ra
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb Rb
    exact .compute (hcompute Ra hΓ ha EΓ Ea W)
      (hcompute Rb hΓ hb EΓ Eb W)
      (ih hΓ HA.hasType.2 HB.hasType.2 EΓ EA EB W)
  | symm HC ih =>
    intro Γ a b A Δ' hΓ ha hb EΓ Ea Eb W
    exact .symm (ih hΓ hb ha EΓ Eb Ea W)
  | carrierChecked HC ih =>
    intro Γ a b A Δ' hΓ ha hb EΓ Eα Ea Eb W α' Rα
    exact .carrierChecked (ih hΓ ha hb EΓ Ea Eb W)
  | carrierSubsingleton HS =>
    intro Γ a b A Δ' hΓ ha hb EΓ Eα Ea Eb W α' Rα
    exact .carrierSubsingleton (HS.beta Rα)
  | carrierSymm HC ih =>
    intro Γ a b A Δ' hΓ ha hb EΓ Eα Ea Eb W α' Rα
    exact .carrierSymm (ih hΓ hb ha EΓ Eα Eb Ea W α' Rα)
  | carrierCompute RC HC ih =>
    intro Γ a b A Δ' hΓ ha hb EΓ Eα Ea Eb W α' Rα
    obtain ⟨u, hA⟩ := ha.isType henv hΓ
    obtain ⟨A', HE, EA⟩ := proofErase_scoped_compute_realize hstep hΓ hA EΓ Eα RC
    obtain ⟨shared, RB, RS⟩ := hcommute hΓ hA
      (by simpa only [EΓ, Eα] using RC)
      (by simpa only [Eα] using Rα) (by simpa only [EΓ] using W)
    exact .carrierCompute RS
      (ih hΓ (HE.defeq ha) (HE.defeq hb) EΓ EA Ea Eb W shared RB)
  | carrierReduce Ra Rb HC ih =>
    intro Γ a b A Δ' hΓ ha hb EΓ Eα Ea Eb W α' Rα
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea Ra
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb Rb
    exact .carrierReduce (hcompute Ra hΓ ha EΓ Ea W)
      (hcompute Rb hΓ hb EΓ Eb W)
      (ih hΓ HA.hasType.2 HB.hasType.2 EΓ Eα EA EB W α' Rα)
  | carrierFunction SD HC ih =>
    intro Γ a b A Δ' hΓ ha hb EΓ Eα Ea Eb W α' Rα
    obtain ⟨rawD', rawC', rfl, RD, RC⟩ := beta_forallE_parts Rα
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
    apply JointCheck.carrierFunction (W.sort SD RD)
    exact ih hΓD hfa hfb (by simp only [proofEraseCtx, EΓ, ED]) EC Efa Efb (W.cons RD) rawC' RC
  | @carrierIntro family info ls Δ sa sb ps hi hx hp hadm Hfields ihfields =>
    intro Γ a b A Δ' hΓ ha hb EΓ Eα Ea Eb W α' Rα
    have HE := carrier_raw hstep (.carrierIntro hi hx hp hadm Hfields) hΓ ha hb EΓ Eα Ea Eb
    obtain ⟨ps', rfl, Hps⟩ := Rα.const_spine
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
    intro Γ a b A Δ' hΓ ha hb EΓ Eα Ea Eb W α' Rα
    have HE := carrier_raw hstep (.carrierNested hi hx hp hadm HT Hfields) hΓ ha hb EΓ Eα Ea Eb
    obtain ⟨ps', rfl, Hps⟩ := Rα.const_spine
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
    exact ihfields i hj hn hΓ hiaF hibF EΓ EF' Epa Epb W _ (projectionType_beta Hps .refl)

/-- At source stage n+1, simultaneous context-oracle and carrier-type beta
transport needs proposition beta transport only at stage n. The conclusion
covers every constructor of both comparison and carrier checking. -/
theorem proofErase_joint_stage_oracle_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D))
    (H : JointCheck (ErasedJointStage D (stage + 1)) Δ kind sa sb) :
    JointOracleBetaResult (ErasedJointUnion D) Δ kind sa sb := by
  apply H.oracle_beta (erased_joint_stage_descent heq hs (stage + 1))
  · intro Γ Δ Δ' e T source out R hΓ ht EΓ Ee W
    simpa only [ProofShape.subst_id] using R.subst_typed
      (erased_joint_stage_descent heq hs (stage + 1))
      (erased_joint_stage_subst_of_lower_beta heq hs hregistry Hbeta)
      hΓ ht EΓ Ee W.interpretation
  · intro Γ Δ' e T out reduced hΓ ht R B W
    obtain ⟨shared, BS, RS⟩ := proofErase_joint_stage_beta_commute_of_lower_beta
      heq hs hregistry Hbeta hΓ ht R B
    have RS := RS.subst (erased_beta_stable_joint_subst heq hs) W.interpretation
    simp only [ProofShape.subst_id] at RS
    exact ⟨shared, BS, RS.mono erased_beta_stable_joint_into_union⟩
  · intro Γ Δ' e T out hΓ ht R W
    obtain ⟨out', HR, HB⟩ := proofErase_joint_recovery_oracle_beta_of_lower_beta
      heq hs hregistry Hbeta hΓ ht W.interpretation W.entries R
    exact ⟨out', HR.mono erased_beta_stable_joint_into_union, HB⟩

/-- Stage-zero comparison and carrier checking transport through beta changes
of context oracles and carrier types without a proposition beta premise.
This does not assert beta stability of the compared endpoints. -/
theorem proofErase_joint_zero_oracle_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : JointCheck (ErasedJointStage D 0) Δ kind sa sb) :
    JointOracleBetaResult (ErasedJointUnion D) Δ kind sa sb := by
  apply H.oracle_beta (erased_joint_stage_descent heq hs 0)
  · intro Γ Δ Δ' e T source out R hΓ ht EΓ Ee W
    have RS := R.subst (fun H _ => erased_iota_primitive_subst H) W.interpretation
    simp only [ProofShape.subst_id] at RS
    exact RS.mono (fun H => ⟨0, H⟩)
  · intro Γ Δ' e T out reduced hΓ ht R B W
    obtain ⟨shared, BS, RS⟩ := proofErase_joint_zero_beta_commute heq hs hΓ ht R B
    have RS := RS.subst (erased_beta_stable_joint_subst heq hs) W.interpretation
    simp only [ProofShape.subst_id] at RS
    exact ⟨shared, BS, RS.mono erased_beta_stable_joint_into_union⟩
  · intro Γ Δ' e T out hΓ ht R W
    obtain ⟨out', HR, HB⟩ := proofErase_joint_zero_recovery_oracle_beta
      heq hs hΓ ht W.interpretation W.entries R
    exact ⟨out', HR.mono erased_beta_stable_joint_into_union, HB⟩

/-- A typed carrier guard survives beta reduction of its carrier, with both
endpoints fixed. The hypothesis is strictly below its source computation stage;
no stability of an enlarged target guard is invoked. -/
theorem proofErase_joint_carrier_type_beta_of_lower_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : JointCarrierGuard (ErasedJointStage D (stage + 1)) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ a) (proofErase Γ b))
    (R : ProofShape.BetaRed (proofErase Γ A) A') :
    JointCarrierGuard (ErasedJointUnion D) (proofEraseCtx Γ) A'
      (proofErase Γ a) (proofErase Γ b) := by
  have W : ContextOracleBeta (proofEraseCtx Γ) (proofEraseCtx Γ) :=
    ⟨ContextSubstitution.of_defeqCtx hΓ (.zero (Γ₀ := Γ)), fun _ => .refl⟩
  exact proofErase_joint_stage_oracle_beta heq hs hregistry Hbeta H hΓ ha hb rfl rfl rfl rfl W A' R

/-- Reducing an actual typed binder domain preserves joint comparison of its
bodies. Both endpoint erasures are those of the actual converted context. -/
theorem proofErase_joint_compare_domain_beta_of_lower_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (R : VExpr.BetaRed A A')
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : JointCompare (ErasedJointStage D (stage + 1)) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    JointCompare (ErasedJointUnion D) (proofEraseCtx (A' :: Γ)) mode
      (proofErase (A' :: Γ) a) (proofErase (A' :: Γ) b) := by
  have W : ContextOracleBeta (proofEraseCtx Γ) (proofEraseCtx Γ) :=
    ⟨ContextSubstitution.of_defeqCtx hΓ (.zero (Γ₀ := Γ)), fun _ => .refl⟩
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have W := W.cons (proofErase_beta_forward hΓ hA R)
  have HC := proofErase_joint_stage_oracle_beta heq hs hregistry Hbeta H
    hΓA ha hb rfl rfl rfl W
  have HE := beta_eq hΓ hA R
  rwa [proofErase_defeqCtx hΓA (.succ .zero HE) ha,
    proofErase_defeqCtx hΓA (.succ .zero HE) hb] at HC

end Lean4Lean.VEnv.Strengthening
