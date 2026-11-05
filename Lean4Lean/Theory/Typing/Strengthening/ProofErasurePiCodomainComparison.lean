import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiCodomainPayload
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaTraceComparison

/-! # Pi codomain extraction through arbitrary stage-zero comparisons

A fixed written binder supplies native backward context transport for both
payload histories. Temporary controls and all inferred constructors are covered.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private control_context from Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaTraceComparison
open private types_inferred_raw from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedTypedExposure
variable [Params] {D : PureObservation.Definitions}

private theorem traced_pi_codomain_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hE : env.HasType univs (A :: Γ) E (.sort v))
    (H : ComputedJointCheck (ErasedStaticStructureEtaExpansionStage D 0) Δ kind sa sb)
    (hk : kind = .compare false)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (hf : env.HasType univs Γ' f F) (hg : env.HasType univs Γ' g G)
    (EΓ : proofEraseCtx Γ' = Δ) (Ef : proofErase Γ' f = sa) (Eg : proofErase Γ' g = sb)
    (TA : MarkedPiTrace (StageZeroPiOrigin D Γ A B u v) n sa k)
    (TB : MarkedPiTrace (StageZeroPiOrigin D Γ A E u v) n sb k) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (A :: Γ)) false
      (proofErase (A :: Γ) B) (proofErase (A :: Γ) E) := by
  induction H generalizing B E Γ' n k f g F G with
  | leaf H =>
    cases hk
    cases H with
    | refl =>
      obtain ⟨X, x, PA, PB⟩ := TA.common_payload TB
      exact stage_zero_pi_common_payload_codomains PA PB
    | sort => exact TA.not_sort.elim
    | const => exact (TA.not_primitiveHead trivial).elim
  | app HF HX ihF _ | appCarrier _ HF HX ihF _ | appComputed _ HF HX ihF _ =>
    obtain ⟨f₀, x₀, rfl, _, Ef₀, _⟩ := erase_app_inv Ef
    obtain ⟨g₀, y₀, rfl, _, Eg₀, _⟩ := erase_app_inv Eg
    obtain ⟨_, _, hf₀, _⟩ := hf.app_inv henv hΓ'
    obtain ⟨_, _, hg₀, _⟩ := hg.app_inv henv hΓ'
    exact ihF hB hE rfl hΓ' W hf₀ hg₀ EΓ Ef₀ Eg₀ TA.app_inv TB.app_inv
  | proj => exact TA.not_proj.elim
  | lam HD HB _ ihB =>
    cases hk
    cases k with
    | zero => exact TA.not_lam_zero.elim
    | succ k =>
      obtain ⟨C', a', b', T', v', hC', ha', hb', EC, Ea, Eb⟩ :=
        control_context heq hs (.lam HD HB) hΓ' hf hg EΓ Ef Eg
      have hΓC' : OnCtx (C' :: Γ') (env.IsType univs) := ⟨hΓ', v', hC'⟩
      have W' : Ctx.LiftN (n+1) 0 Γ (C' :: Γ') := W.comp (by omega) (by omega) Ctx.LiftN.one
      exact ihB hB hE rfl hΓC' W' ha' hb' (by simp only [proofEraseCtx, EC, EΓ]) Ea Eb TA.lam_succ TB.lam_succ
  | lamSorted SX SY HD HB _ ihB =>
    cases hk
    cases k with
    | zero => exact TA.not_lam_zero.elim
    | succ k =>
      obtain ⟨C', a', b', T', v', hC', ha', hb', EC, Ea, Eb⟩ :=
        control_context heq hs (.lamSorted SX SY HD HB) hΓ' hf hg EΓ Ef Eg
      have hΓC' : OnCtx (C' :: Γ') (env.IsType univs) := ⟨hΓ', v', hC'⟩
      have W' : Ctx.LiftN (n+1) 0 Γ (C' :: Γ') := W.comp (by omega) (by omega) Ctx.LiftN.one
      exact ihB hB hE rfl hΓC' W' ha' hb' (by simp only [proofEraseCtx, EC, EΓ]) Ea Eb TA.lam_succ TB.lam_succ
  | forallE HD HB _ _ | forallSorted _ _ HD _ _ HB _ _ =>
    obtain ⟨rfl, X, x, PA, rfl, rfl⟩ := TA.pi_inv
    obtain ⟨_, Y, y, PB, rfl, rfl⟩ := TB.pi_inv
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    exact proofErase_computed_joint_types_inferred
      (erased_static_structure_eta_expansion_stage_descent heq hs 0) hΓA hB hE
      (stage_zero_pi_payload_codomain_compare heq hs hΓ hA hB hE hΓ' W PA PB (EΓ ▸ HB))
  | etaLams HD HE _ =>
    cases k with
    | zero => exact TA.not_lam_zero.elim
    | succ k =>
      rcases HE with HE | HE
      · obtain ⟨X, x, PA, PB⟩ := ((MarkedPiTrace.eta_iff HE).1 TA).common_payload TB
        exact stage_zero_pi_common_payload_codomains PA PB
      · obtain ⟨X, x, PA, PB⟩ := TA.common_payload ((MarkedPiTrace.eta_iff HE).1 TB)
        exact stage_zero_pi_common_payload_codomains PA PB
  | compute RF RG HC ih =>
    have hstep : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D 0) :=
      erased_static_structure_eta_expansion_stage_descent heq hs 0
    obtain ⟨f', HF, Ef'⟩ := proofErase_scoped_compute_realize hstep hΓ' hf EΓ Ef RF
    obtain ⟨g', HG, Eg'⟩ := proofErase_scoped_compute_realize hstep hΓ' hg EΓ Eg RG
    have TA' := proofErase_scoped_compute_markedPiTrace hstep stage_zero_marked_pi_trace
      (stage_zero_piOrigin_componentClosure heq hs hΓ) RF hΓ' W hf EΓ Ef TA
    have TB' := proofErase_scoped_compute_markedPiTrace hstep stage_zero_marked_pi_trace
      (stage_zero_piOrigin_componentClosure heq hs hΓ) RG hΓ' W hg EΓ Eg TB
    exact ih hB hE hk hΓ' W HF.hasType.2 HG.hasType.2 EΓ Ef' Eg' TA' TB'
  | symm HC ih => exact (ih hE hB hk hΓ' W hg hf EΓ Eg Ef TB TA).symm
  | lamCommon | etaBodyL | etaBodyR | structFields | carrierIntro | carrierChecked |
      carrierSubsingleton | carrierFunction | carrierSymm | carrierCompute | carrierReduce |
      carrierNested => cases hk

/-- Computed comparisons of Pis with a shared written binder recover a check
of their original codomains. The codomains may have independent universes;
ordinary Pi injectivity aligns their actual typings before trace extraction.
No component comparison or common computation endpoint is assumed. -/
theorem stage_zero_computed_pi_codomains_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hE : env.HasType univs (A :: Γ) E (.sort z))
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) f)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) E)) g)
    (H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) mode f g) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (A :: Γ)) false
      (proofErase (A :: Γ) B) (proofErase (A :: Γ) E) := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D 0) :=
    erased_static_structure_eta_expansion_stage_descent heq hs 0
  have hPiB := HasType.forallE hA hB
  have hPiE := HasType.forallE hA hE
  have EB : proofErase Γ (.forallE A B) = .forallE (proofErase Γ A) (proofErase (A :: Γ) B) :=
    if_neg (not_isProof_of_sort hΓ hPiB)
  have EE : proofErase Γ (.forallE A E) = .forallE (proofErase Γ A) (proofErase (A :: Γ) E) :=
    if_neg (not_isProof_of_sort hΓ hPiE)
  obtain ⟨f', HF, Ef⟩ := proofErase_scoped_compute_realize hstep hΓ hPiB rfl EB RA
  obtain ⟨g', HG, Eg⟩ := proofErase_scoped_compute_realize hstep hΓ hPiE rfl EE RC
  have HI := types_inferred_raw hstep H hΓ HF.hasType.2 HG.hasType.2 rfl Ef Eg
  have HOrig : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx Γ) false (proofErase Γ (.forallE A B)) (proofErase Γ (.forallE A E)) := by
    rw [EB, EE]
    exact .compute RA RC HI
  have HPi := (proofErase_computed_joint_compare_reflect hstep hΓ hPiB hPiE HOrig).2
    rfl (not_isProof_of_sort hΓ hPiB) (not_isProof_of_sort hΓ hPiE)
  obtain ⟨_, _, HBE⟩ := HPi.forallE_inv henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hEv : env.HasType univs (A :: Γ) E (.sort v) := (show env.IsDefEqU univs (A :: Γ) B E from ⟨_, HBE⟩).of_l henv hΓA hB |>.hasType.2
  exact traced_pi_codomain_compare heq hs hΓ hA hB hEv HI rfl hΓ (Ctx.LiftN.zero [])
    HF.hasType.2 HG.hasType.2 rfl Ef Eg
    (proofErase_stage_zero_pi_trace heq hs hΓ hA hB RA)
    (proofErase_stage_zero_pi_trace heq hs hΓ hA hEv RC)

/-- A full Pi comparison at a shared written binder contains an inferred
codomain comparison at that binder, through arbitrary internal computation. -/
theorem stage_zero_pi_codomains_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hE : env.HasType univs (A :: Γ) E (.sort z))
    (H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (.forallE A B)) (proofErase Γ (.forallE A E))) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (A :: Γ)) false
      (proofErase (A :: Γ) B) (proofErase (A :: Γ) E) := by
  apply stage_zero_computed_pi_codomains_compare heq hs hΓ hA hB hE .refl .refl
  simpa only [show proofErase Γ (.forallE A B) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ (HasType.forallE hA hB)),
    show proofErase Γ (.forallE A E) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ (HasType.forallE hA hE))] using H

end Lean4Lean.VEnv.Strengthening
