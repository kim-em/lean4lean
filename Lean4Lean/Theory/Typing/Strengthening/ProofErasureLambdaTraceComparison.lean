import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaTracePayload
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaApplicationBoundary

/-! # Inferred comparison follows pending lambda control traces

The comparison induction follows function positions at a larger pending arity.
Control lambdas extend temporary prefixes; payload lambdas discharge the body
comparison below those prefixes. Argument guards are not needed by this trace.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private infer_raw lambda_common_context from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointTransport
variable [Params] {D : PureObservation.Definitions}

private theorem control_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) Δ false (.lam X x) (.lam Y y))
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f F) (hg : env.HasType univs Γ g G)
    (EΓ : proofEraseCtx Γ = Δ) (Ef : proofErase Γ f = .lam X x) (Eg : proofErase Γ g = .lam Y y) :
    ∃ C a b T u, env.HasType univs Γ C (.sort u) ∧
      env.HasType univs (C :: Γ) a T ∧ env.HasType univs (C :: Γ) b T ∧
      proofErase Γ C = X ∧ proofErase (C :: Γ) a = x ∧ proofErase (C :: Γ) b = y := by
  obtain ⟨C, a, rfl, hnF, EC, Ea⟩ := erase_lam_inv Ef
  obtain ⟨C', b, rfl, hnG, _, Eb⟩ := erase_lam_inv Eg
  have HE := infer_raw (erased_static_structure_eta_expansion_stage_descent heq hs 0)
    H hΓ hf hg EΓ Ef Eg hnF hnG
  obtain ⟨u, T, hC, _, ha, hb, Ectx⟩ := lambda_common_context hΓ hf HE.hasType.2
  rw [Ectx] at Eb
  exact ⟨C, a, b, T, u, hC, ha, hb, EC, Ea, Eb⟩

private theorem traced_inferred_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hC : env.HasType univs Γ C (.sort u))
    (ha : env.HasType univs (C :: Γ) a T) (hb : env.HasType univs (C :: Γ) b T)
    (hna : ¬ IsProof Γ (.lam C a)) (hnb : ¬ IsProof Γ (.lam C b))
    (H : ComputedJointCheck (ErasedStaticStructureEtaExpansionStage D 0) Δ kind sa sb)
    (hk : kind = .compare false)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (hf : env.HasType univs Γ' f F) (hg : env.HasType univs Γ' g G)
    (EΓ : proofEraseCtx Γ' = Δ) (Ef : proofErase Γ' f = sa) (Eg : proofErase Γ' g = sb)
    (TA : IgnoredLambdaTrace (StageZeroLambdaOrigin D Γ C a u) n sa k)
    (TB : IgnoredLambdaTrace (StageZeroLambdaOrigin D Γ C b u) n sb k) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (C :: Γ)) false
      (proofErase (C :: Γ) a) (proofErase (C :: Γ) b) := by
  induction H generalizing a b Γ' n k f g F G with
  | leaf H =>
    cases hk
    cases H with
    | refl =>
      obtain ⟨X, x, PA, PB⟩ := TA.common_payload TB
      exact stage_zero_lambda_common_payload_compare PA PB
    | sort => exact TA.not_sort.elim
    | const => exact (TA.not_primitiveHead trivial).elim
  | app HF HX ihF _ | appCarrier _ HF HX ihF _ | appComputed _ HF HX ihF _ =>
    obtain ⟨f₀, x₀, rfl, _, Ef₀, _⟩ := erase_app_inv Ef
    obtain ⟨g₀, y₀, rfl, _, Eg₀, _⟩ := erase_app_inv Eg
    obtain ⟨_, _, hf₀, _⟩ := hf.app_inv henv hΓ'
    obtain ⟨_, _, hg₀, _⟩ := hg.app_inv henv hΓ'
    exact ihF ha hb hna hnb rfl hΓ' W hf₀ hg₀ EΓ Ef₀ Eg₀ TA.app_inv TB.app_inv
  | proj => exact TA.not_proj.elim
  | lam HD HB _ ihB =>
    cases hk
    cases k with
    | zero =>
      obtain ⟨X, x, PA, rfl, rfl⟩ := TA.lam_zero
      obtain ⟨Y, y, PB, rfl, rfl⟩ := TB.lam_zero
      exact stage_zero_lambda_payload_body_compare heq hs hΓ hC ha hb hΓ' W PA PB (EΓ ▸ HB)
    | succ k =>
      obtain ⟨C', a', b', T', v, hC', ha', hb', EC, Ea, Eb⟩ :=
        control_context heq hs (.lam HD HB) hΓ' hf hg EΓ Ef Eg
      have hΓC' : OnCtx (C' :: Γ') (env.IsType univs) := ⟨hΓ', v, hC'⟩
      have W' : Ctx.LiftN (n+1) 0 Γ (C' :: Γ') := W.comp (by omega) (by omega) Ctx.LiftN.one
      exact ihB ha hb hna hnb rfl hΓC' W' ha' hb' (by simp only [proofEraseCtx, EC, EΓ]) Ea Eb TA.lam_succ TB.lam_succ
  | lamSorted SX SY HD HB _ ihB =>
    cases hk
    cases k with
    | zero =>
      obtain ⟨X, x, PA, rfl, rfl⟩ := TA.lam_zero
      obtain ⟨Y, y, PB, rfl, rfl⟩ := TB.lam_zero
      exact stage_zero_lambda_payload_body_compare heq hs hΓ hC ha hb hΓ' W PA PB (EΓ ▸ HB)
    | succ k =>
      obtain ⟨C', a', b', T', v, hC', ha', hb', EC, Ea, Eb⟩ :=
        control_context heq hs (.lamSorted SX SY HD HB) hΓ' hf hg EΓ Ef Eg
      have hΓC' : OnCtx (C' :: Γ') (env.IsType univs) := ⟨hΓ', v, hC'⟩
      have W' : Ctx.LiftN (n+1) 0 Γ (C' :: Γ') := W.comp (by omega) (by omega) Ctx.LiftN.one
      exact ihB ha hb hna hnb rfl hΓC' W' ha' hb' (by simp only [proofEraseCtx, EC, EΓ]) Ea Eb TA.lam_succ TB.lam_succ
  | forallE | forallSorted => exact TA.not_forallE.elim
  | etaLams HD HE _ =>
    cases k with
    | zero =>
      obtain ⟨X, x, PA, rfl, rfl⟩ := TA.lam_zero
      obtain ⟨Y, y, PB, rfl, rfl⟩ := TB.lam_zero
      exact stage_zero_lambda_payload_eta_compare heq hs hΓ hC ha hb hna hnb PA PB HE
    | succ k =>
      rcases HE with HE | HE
      · obtain ⟨X, x, PA, PB⟩ := ((IgnoredLambdaTrace.eta_iff HE).1 TA).common_payload TB
        exact stage_zero_lambda_common_payload_compare PA PB
      · obtain ⟨X, x, PA, PB⟩ := TA.common_payload ((IgnoredLambdaTrace.eta_iff HE).1 TB)
        exact stage_zero_lambda_common_payload_compare PA PB
  | compute RF RG HC ih =>
    have hstep : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D 0) :=
      erased_static_structure_eta_expansion_stage_descent heq hs 0
    obtain ⟨f', HF, Ef'⟩ := proofErase_scoped_compute_realize hstep hΓ' hf EΓ Ef RF
    obtain ⟨g', HG, Eg'⟩ := proofErase_scoped_compute_realize hstep hΓ' hg EΓ Eg RG
    have TA' := proofErase_scoped_compute_ignoredLambdaTrace hstep stage_zero_ignored_lambda_trace
      (stage_zero_lambdaOrigin_componentClosure heq hs hΓ) RF hΓ' W hf EΓ Ef TA
    have TB' := proofErase_scoped_compute_ignoredLambdaTrace hstep stage_zero_ignored_lambda_trace
      (stage_zero_lambdaOrigin_componentClosure heq hs hΓ) RG hΓ' W hg EΓ Eg TB
    exact ih ha hb hna hnb hk hΓ' W HF.hasType.2 HG.hasType.2 EΓ Ef' Eg' TA' TB'
  | symm HC ih =>
    exact (ih hb ha hnb hna hk hΓ' W hg hf EΓ Eg Ef TB TA).symm
  | lamCommon | etaBodyL | etaBodyR | structFields | carrierIntro | carrierChecked |
      carrierSubsingleton | carrierFunction | carrierSymm | carrierCompute | carrierReduce |
      carrierNested => cases hk

/-- Inferred comparison after arbitrary stage-zero computation of two original
lambdas implies comparison of their original bodies. Pending ignored control
arguments discharge every application constructor; no application-extraction
premise, terminal-domain restriction or normalization assumption remains. -/
theorem stage_zero_computed_inferred_lambda_body_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hC : env.HasType univs Γ C (.sort u))
    (ha : env.HasType univs (C :: Γ) a T) (hb : env.HasType univs (C :: Γ) b T)
    (hna : ¬ IsProof Γ (.lam C a)) (hnb : ¬ IsProof Γ (.lam C b))
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.lam (proofErase Γ C) (proofErase (C :: Γ) a)) f)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.lam (proofErase Γ C) (proofErase (C :: Γ) b)) g)
    (H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) false f g) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (C :: Γ)) false
      (proofErase (C :: Γ) a) (proofErase (C :: Γ) b) := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D 0) :=
    erased_static_structure_eta_expansion_stage_descent heq hs 0
  obtain ⟨f', HF, Ef⟩ := proofErase_scoped_compute_realize hstep hΓ (HasType.lam hC ha) rfl
    (show proofErase Γ (.lam C a) = .lam _ _ from if_neg hna) RA
  obtain ⟨g', HG, Eg⟩ := proofErase_scoped_compute_realize hstep hΓ (HasType.lam hC hb) rfl
    (show proofErase Γ (.lam C b) = .lam _ _ from if_neg hnb) RB
  exact traced_inferred_compare heq hs hΓ hC ha hb hna hnb H rfl hΓ (Ctx.LiftN.zero [])
    HF.hasType.2 HG.hasType.2 rfl Ef Eg
    (proofErase_stage_zero_lambda_trace heq hs hΓ hC ha hna RA)
    (proofErase_stage_zero_lambda_trace heq hs hΓ hC hb hnb RB)

/-- The direct inferred lambda-body extraction theorem includes all internal
compute, symmetry, application, eta and carrier-argument checking constructors. -/
theorem stage_zero_inferred_lambda_body_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hC : env.HasType univs Γ C (.sort u))
    (ha : env.HasType univs (C :: Γ) a T) (hb : env.HasType univs (C :: Γ) b T)
    (hna : ¬ IsProof Γ (.lam C a)) (hnb : ¬ IsProof Γ (.lam C b))
    (H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) false
      (.lam (proofErase Γ C) (proofErase (C :: Γ) a))
      (.lam (proofErase Γ C) (proofErase (C :: Γ) b))) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (C :: Γ)) false
      (proofErase (C :: Γ) a) (proofErase (C :: Γ) b) :=
  stage_zero_computed_inferred_lambda_body_compare heq hs hΓ hC ha hb hna hnb .refl .refl H

/-- The previously isolated application interface is discharged by pending
control traces. Its three alternatives are exactly the original grammar rules. -/
theorem stage_zero_lambda_application_extraction
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) : StageZeroLambdaApplicationExtraction D := by
  intro Γ C u a b T f g x y hΓ hC ha hb hna hnb RA RB HF HX
  apply stage_zero_computed_inferred_lambda_body_compare heq hs hΓ hC ha hb hna hnb RA RB
  rcases HX with HX | ⟨A, B, RN, HX⟩ | ⟨A, body, RF, HX⟩
  · exact .app HF HX
  · exact .appCarrier RN HF HX
  · exact .appComputed RF HF HX

end Lean4Lean.VEnv.Strengthening
