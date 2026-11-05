import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTerminalLambdaPayload

/-! # Inferred lambda-body extraction across converted terminal binders

The pending-control comparison induction keeps a fixed reference binder while
allowing the two original lambdas to use independent ordinary conversions.
Terminal context transport closes payload boundaries without forward histories
between the original domains.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private control_context from Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaTraceComparison
variable [Params] {D : PureObservation.Definitions}

private theorem terminal_traced_inferred_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HT : TerminalDomain Γ C)
    (HCA : env.IsDefEq univs Γ C A (.sort u)) (HCB : env.IsDefEq univs Γ C B (.sort u))
    (ha : env.HasType univs (C :: Γ) a T) (hb : env.HasType univs (C :: Γ) b T)
    (hna : ¬ IsProof Γ (.lam A a)) (hnb : ¬ IsProof Γ (.lam B b))
    (H : ComputedJointCheck (ErasedStaticStructureEtaExpansionStage D 0) Δ kind sa sb)
    (hk : kind = .compare false)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (hf : env.HasType univs Γ' f F) (hg : env.HasType univs Γ' g G)
    (EΓ : proofEraseCtx Γ' = Δ) (Ef : proofErase Γ' f = sa) (Eg : proofErase Γ' g = sb)
    (TA : IgnoredLambdaTrace (StageZeroLambdaOrigin D Γ A a u) n sa k)
    (TB : IgnoredLambdaTrace (StageZeroLambdaOrigin D Γ B b u) n sb k) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (C :: Γ)) false
      (proofErase (C :: Γ) a) (proofErase (C :: Γ) b) := by
  induction H generalizing A B a b Γ' n k f g F G with
  | leaf H =>
    cases hk
    cases H with
    | refl =>
      obtain ⟨X, x, PA, PB⟩ := TA.common_payload TB
      exact stage_zero_terminal_lambda_common_payload_compare hΓ HCA HCB ha hb PA PB
    | sort => exact TA.not_sort.elim
    | const => exact (TA.not_primitiveHead trivial).elim
  | app HF HX ihF _ | appCarrier _ HF HX ihF _ | appComputed _ HF HX ihF _ =>
    obtain ⟨f₀, x₀, rfl, _, Ef₀, _⟩ := erase_app_inv Ef
    obtain ⟨g₀, y₀, rfl, _, Eg₀, _⟩ := erase_app_inv Eg
    obtain ⟨_, _, hf₀, _⟩ := hf.app_inv henv hΓ'
    obtain ⟨_, _, hg₀, _⟩ := hg.app_inv henv hΓ'
    exact ihF HCA HCB ha hb hna hnb rfl hΓ' W hf₀ hg₀ EΓ Ef₀ Eg₀ TA.app_inv TB.app_inv
  | proj => exact TA.not_proj.elim
  | lam HD HB _ ihB =>
    cases hk
    cases k with
    | zero =>
      obtain ⟨X, x, PA, rfl, rfl⟩ := TA.lam_zero
      obtain ⟨Y, y, PB, rfl, rfl⟩ := TB.lam_zero
      exact stage_zero_terminal_lambda_payload_body_compare heq hs hΓ HT HCA HCB ha hb hΓ' W PA PB (EΓ ▸ HB)
    | succ k =>
      obtain ⟨C', a', b', T', v, hC', ha', hb', EC, Ea, Eb⟩ :=
        control_context heq hs (.lam HD HB) hΓ' hf hg EΓ Ef Eg
      have hΓC' : OnCtx (C' :: Γ') (env.IsType univs) := ⟨hΓ', v, hC'⟩
      have W' : Ctx.LiftN (n+1) 0 Γ (C' :: Γ') := W.comp (by omega) (by omega) Ctx.LiftN.one
      exact ihB HCA HCB ha hb hna hnb rfl hΓC' W' ha' hb' (by simp only [proofEraseCtx, EC, EΓ]) Ea Eb TA.lam_succ TB.lam_succ
  | lamSorted SX SY HD HB _ ihB =>
    cases hk
    cases k with
    | zero =>
      obtain ⟨X, x, PA, rfl, rfl⟩ := TA.lam_zero
      obtain ⟨Y, y, PB, rfl, rfl⟩ := TB.lam_zero
      exact stage_zero_terminal_lambda_payload_body_compare heq hs hΓ HT HCA HCB ha hb hΓ' W PA PB (EΓ ▸ HB)
    | succ k =>
      obtain ⟨C', a', b', T', v, hC', ha', hb', EC, Ea, Eb⟩ :=
        control_context heq hs (.lamSorted SX SY HD HB) hΓ' hf hg EΓ Ef Eg
      have hΓC' : OnCtx (C' :: Γ') (env.IsType univs) := ⟨hΓ', v, hC'⟩
      have W' : Ctx.LiftN (n+1) 0 Γ (C' :: Γ') := W.comp (by omega) (by omega) Ctx.LiftN.one
      exact ihB HCA HCB ha hb hna hnb rfl hΓC' W' ha' hb' (by simp only [proofEraseCtx, EC, EΓ]) Ea Eb TA.lam_succ TB.lam_succ
  | forallE | forallSorted => exact TA.not_forallE.elim
  | etaLams HD HE _ =>
    cases k with
    | zero =>
      obtain ⟨X, x, PA, rfl, rfl⟩ := TA.lam_zero
      obtain ⟨Y, y, PB, rfl, rfl⟩ := TB.lam_zero
      exact stage_zero_terminal_lambda_payload_eta_compare heq hs hΓ HT HCA HCB ha hb hna hnb PA PB HE
    | succ k =>
      rcases HE with HE | HE
      · obtain ⟨X, x, PA, PB⟩ := ((IgnoredLambdaTrace.eta_iff HE).1 TA).common_payload TB
        exact stage_zero_terminal_lambda_common_payload_compare hΓ HCA HCB ha hb PA PB
      · obtain ⟨X, x, PA, PB⟩ := TA.common_payload ((IgnoredLambdaTrace.eta_iff HE).1 TB)
        exact stage_zero_terminal_lambda_common_payload_compare hΓ HCA HCB ha hb PA PB
  | compute RF RG HC ih =>
    have hstep : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D 0) :=
      erased_static_structure_eta_expansion_stage_descent heq hs 0
    obtain ⟨f', HF, Ef'⟩ := proofErase_scoped_compute_realize hstep hΓ' hf EΓ Ef RF
    obtain ⟨g', HG, Eg'⟩ := proofErase_scoped_compute_realize hstep hΓ' hg EΓ Eg RG
    have TA' := proofErase_scoped_compute_ignoredLambdaTrace hstep stage_zero_ignored_lambda_trace
      (stage_zero_lambdaOrigin_componentClosure heq hs hΓ) RF hΓ' W hf EΓ Ef TA
    have TB' := proofErase_scoped_compute_ignoredLambdaTrace hstep stage_zero_ignored_lambda_trace
      (stage_zero_lambdaOrigin_componentClosure heq hs hΓ) RG hΓ' W hg EΓ Eg TB
    exact ih HCA HCB ha hb hna hnb hk hΓ' W HF.hasType.2 HG.hasType.2 EΓ Ef' Eg' TA' TB'
  | symm HC ih =>
    exact (ih HCB HCA hb ha hnb hna hk hΓ' W hg hf EΓ Eg Ef TB TA).symm
  | lamCommon | etaBodyL | etaBodyR | structFields | carrierIntro | carrierChecked |
      carrierSubsingleton | carrierFunction | carrierSymm | carrierCompute | carrierReduce |
      carrierNested => cases hk

/-- Arbitrary inferred comparison of independently computed lambdas extracts
a body comparison in a fixed terminal binder. Original domains need only be
ordinarily equal to the reference domain; no computation between them is used.
Both bodies may have a common dependent type in that reference context. -/
theorem stage_zero_terminal_computed_inferred_lambda_body_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HT : TerminalDomain Γ C)
    (HCA : env.IsDefEq univs Γ C A (.sort u)) (HCB : env.IsDefEq univs Γ C B (.sort u))
    (ha : env.HasType univs (C :: Γ) a T) (hb : env.HasType univs (C :: Γ) b T)
    (hna : ¬ IsProof Γ (.lam A a)) (hnb : ¬ IsProof Γ (.lam B b))
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) a)) f)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.lam (proofErase Γ B) (proofErase (B :: Γ) b)) g)
    (H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) false f g) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (C :: Γ)) false
      (proofErase (C :: Γ) a) (proofErase (C :: Γ) b) := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D 0) :=
    erased_static_structure_eta_expansion_stage_descent heq hs 0
  have ha' := ha.defeqDFC henv (IsDefEqCtx.succ .zero HCA)
  have hb' := hb.defeqDFC henv (IsDefEqCtx.succ .zero HCB)
  obtain ⟨f', HF, Ef⟩ := proofErase_scoped_compute_realize hstep hΓ (HasType.lam HCA.hasType.2 ha') rfl
    (show proofErase Γ (.lam A a) = .lam _ _ from if_neg hna) RA
  obtain ⟨g', HG, Eg⟩ := proofErase_scoped_compute_realize hstep hΓ (HasType.lam HCB.hasType.2 hb') rfl
    (show proofErase Γ (.lam B b) = .lam _ _ from if_neg hnb) RB
  exact terminal_traced_inferred_compare heq hs hΓ HT HCA HCB ha hb hna hnb H rfl hΓ (Ctx.LiftN.zero [])
    HF.hasType.2 HG.hasType.2 rfl Ef Eg
    (proofErase_stage_zero_lambda_trace heq hs hΓ HCA.hasType.2 ha' hna RA)
    (proofErase_stage_zero_lambda_trace heq hs hΓ HCB.hasType.2 hb' hnb RB)

/-- Direct inferred checking of differently annotated lambdas supplies their
body comparison at the ordinarily equal terminal reference binder. -/
theorem stage_zero_terminal_inferred_lambda_body_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HT : TerminalDomain Γ C)
    (HCA : env.IsDefEq univs Γ C A (.sort u)) (HCB : env.IsDefEq univs Γ C B (.sort u))
    (ha : env.HasType univs (C :: Γ) a T) (hb : env.HasType univs (C :: Γ) b T)
    (hna : ¬ IsProof Γ (.lam A a)) (hnb : ¬ IsProof Γ (.lam B b))
    (H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) false
      (.lam (proofErase Γ A) (proofErase (A :: Γ) a))
      (.lam (proofErase Γ B) (proofErase (B :: Γ) b))) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (C :: Γ)) false
      (proofErase (C :: Γ) a) (proofErase (C :: Γ) b) :=
  stage_zero_terminal_computed_inferred_lambda_body_compare heq hs hΓ HT HCA HCB ha hb hna hnb .refl .refl H

/-- A lambda assigned a Pi at a reference domain has its body at the reference
codomain in that context. The written domain is ordinarily equal to the
reference domain, with the reference universe retained. -/
theorem lambda_body_at_reference_pi
    (hΓ : OnCtx Γ (env.IsType univs)) (hC : env.HasType univs Γ C (.sort u))
    (hf : env.HasType univs Γ (.lam A a) (.forallE C T)) :
    env.IsDefEq univs Γ C A (.sort u) ∧ env.HasType univs (C :: Γ) a T := by
  obtain ⟨⟨v, hA⟩, U, ha⟩ := hf.lam_inv henv hΓ
  obtain ⟨⟨_, HAC⟩, _, HUT⟩ := ((HasType.lam hA ha).uniqU henv hΓ hf).forallE_inv henv hΓ
  have HCA := HAC.toU.symm.of_l henv hΓ hC
  exact ⟨HCA, (HUT.defeq ha).defeqDFC henv (IsDefEqCtx.succ .zero HCA.symm)⟩

/-- Common actual Pi typing supplies all domain alignment for inferred
lambda-body extraction at a terminal reference binder. The compared original
lambdas may have different written annotations and arbitrary internal checks. -/
theorem stage_zero_terminal_lambda_bodies_at_pi
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hC : env.HasType univs Γ C (.sort u))
    (HT : TerminalDomain Γ C)
    (hf : env.HasType univs Γ (.lam A a) (.forallE C T))
    (hg : env.HasType univs Γ (.lam B b) (.forallE C T))
    (hna : ¬ IsProof Γ (.lam A a)) (hnb : ¬ IsProof Γ (.lam B b))
    (H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A a)) (proofErase Γ (.lam B b))) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (C :: Γ)) false
      (proofErase (C :: Γ) a) (proofErase (C :: Γ) b) := by
  obtain ⟨HCA, ha⟩ := lambda_body_at_reference_pi hΓ hC hf
  obtain ⟨HCB, hb⟩ := lambda_body_at_reference_pi hΓ hC hg
  apply stage_zero_terminal_inferred_lambda_body_compare heq hs hΓ HT HCA HCB ha hb hna hnb
  simpa only [show proofErase Γ (.lam A a) = .lam _ _ from if_neg hna,
    show proofErase Γ (.lam B b) = .lam _ _ from if_neg hnb] using H

end Lean4Lean.VEnv.Strengthening
