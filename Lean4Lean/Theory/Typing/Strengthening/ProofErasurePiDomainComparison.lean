import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiDomainPayload
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaTraceComparison

/-! # Pi-domain extraction from arbitrary computed comparisons at stage zero

Pending ignored controls let the induction follow application function checks.
At a Pi payload, its domain comparison descends to the original context and
retains both original domain histories. Either outer comparison mode is allowed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private control_context from Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaTraceComparison
open private types_inferred_raw from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedTypedExposure
variable [Params] {D : PureObservation.Definitions}

private theorem traced_pi_domain_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : ComputedJointCheck (ErasedStaticStructureEtaExpansionStage D 0) Δ kind sa sb)
    (hk : kind = .compare false)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (hf : env.HasType univs Γ' f F) (hg : env.HasType univs Γ' g G)
    (EΓ : proofEraseCtx Γ' = Δ) (Ef : proofErase Γ' f = sa) (Eg : proofErase Γ' g = sb)
    (TA : MarkedPiTrace (StageZeroPiOrigin D Γ A B u v) n sa k)
    (TB : MarkedPiTrace (StageZeroPiOrigin D Γ C E w z) n sb k) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) false
      (proofErase Γ A) (proofErase Γ C) := by
  induction H generalizing A B C E u v w z Γ' n k f g F G with
  | leaf H =>
    cases hk
    cases H with
    | refl =>
      obtain ⟨X, x, PA, PB⟩ := TA.common_payload TB
      exact stage_zero_pi_common_payload_domains PA PB
    | sort => exact TA.not_sort.elim
    | const => exact (TA.not_primitiveHead trivial).elim
  | app HF HX ihF _ | appCarrier _ HF HX ihF _ | appComputed _ HF HX ihF _ =>
    obtain ⟨f₀, x₀, rfl, _, Ef₀, _⟩ := erase_app_inv Ef
    obtain ⟨g₀, y₀, rfl, _, Eg₀, _⟩ := erase_app_inv Eg
    obtain ⟨_, _, hf₀, _⟩ := hf.app_inv henv hΓ'
    obtain ⟨_, _, hg₀, _⟩ := hg.app_inv henv hΓ'
    exact ihF rfl hΓ' W hf₀ hg₀ EΓ Ef₀ Eg₀ TA.app_inv TB.app_inv
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
      exact ihB rfl hΓC' W' ha' hb' (by simp only [proofEraseCtx, EC, EΓ]) Ea Eb TA.lam_succ TB.lam_succ
  | lamSorted SX SY HD HB _ ihB =>
    cases hk
    cases k with
    | zero => exact TA.not_lam_zero.elim
    | succ k =>
      obtain ⟨C', a', b', T', v', hC', ha', hb', EC, Ea, Eb⟩ :=
        control_context heq hs (.lamSorted SX SY HD HB) hΓ' hf hg EΓ Ef Eg
      have hΓC' : OnCtx (C' :: Γ') (env.IsType univs) := ⟨hΓ', v', hC'⟩
      have W' : Ctx.LiftN (n+1) 0 Γ (C' :: Γ') := W.comp (by omega) (by omega) Ctx.LiftN.one
      exact ihB rfl hΓC' W' ha' hb' (by simp only [proofEraseCtx, EC, EΓ]) Ea Eb TA.lam_succ TB.lam_succ
  | forallE HD HB _ _ | forallSorted _ _ HD _ _ HB _ _ =>
    obtain ⟨rfl, X, x, PA, rfl, rfl⟩ := TA.pi_inv
    obtain ⟨_, Y, y, PB, rfl, rfl⟩ := TB.pi_inv
    exact stage_zero_pi_payload_domain_compare heq hs hΓ hΓ' W PA PB (EΓ ▸ HD)
  | etaLams HD HE _ =>
    cases k with
    | zero => exact TA.not_lam_zero.elim
    | succ k =>
      rcases HE with HE | HE
      · obtain ⟨X, x, PA, PB⟩ := ((MarkedPiTrace.eta_iff HE).1 TA).common_payload TB
        exact stage_zero_pi_common_payload_domains PA PB
      · obtain ⟨X, x, PA, PB⟩ := TA.common_payload ((MarkedPiTrace.eta_iff HE).1 TB)
        exact stage_zero_pi_common_payload_domains PA PB
  | compute RF RG HC ih =>
    have hstep : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D 0) :=
      erased_static_structure_eta_expansion_stage_descent heq hs 0
    obtain ⟨f', HF, Ef'⟩ := proofErase_scoped_compute_realize hstep hΓ' hf EΓ Ef RF
    obtain ⟨g', HG, Eg'⟩ := proofErase_scoped_compute_realize hstep hΓ' hg EΓ Eg RG
    have TA' := proofErase_scoped_compute_markedPiTrace hstep stage_zero_marked_pi_trace
      (stage_zero_piOrigin_componentClosure heq hs hΓ) RF hΓ' W hf EΓ Ef TA
    have TB' := proofErase_scoped_compute_markedPiTrace hstep stage_zero_marked_pi_trace
      (stage_zero_piOrigin_componentClosure heq hs hΓ) RG hΓ' W hg EΓ Eg TB
    exact ih hk hΓ' W HF.hasType.2 HG.hasType.2 EΓ Ef' Eg' TA' TB'
  | symm HC ih => exact (ih hk hΓ' W hg hf EΓ Eg Ef TB TA).symm
  | lamCommon | etaBodyL | etaBodyR | structFields | carrierIntro | carrierChecked |
      carrierSubsingleton | carrierFunction | carrierSymm | carrierCompute | carrierReduce |
      carrierNested => cases hk

/-- Either mode of comparison after arbitrary stage-zero computations from
two independently typed Pis yields an inferred comparison of their original
domains at stage zero. Domains, codomains and assigned universes may all differ.
No common endpoint, terminal domain or component-comparison premise is assumed. -/
theorem stage_zero_computed_pi_domains_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hC : env.HasType univs Γ C (.sort w)) (hE : env.HasType univs (C :: Γ) E (.sort z))
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) f)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.forallE (proofErase Γ C) (proofErase (C :: Γ) E)) g)
    (H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) mode f g) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) false
      (proofErase Γ A) (proofErase Γ C) := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D 0) :=
    erased_static_structure_eta_expansion_stage_descent heq hs 0
  have hPiA := HasType.forallE hA hB
  have hPiC := HasType.forallE hC hE
  obtain ⟨f', HF, Ef⟩ := proofErase_scoped_compute_realize hstep hΓ hPiA rfl
    (show proofErase Γ (.forallE A B) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hPiA)) RA
  obtain ⟨g', HG, Eg⟩ := proofErase_scoped_compute_realize hstep hΓ hPiC rfl
    (show proofErase Γ (.forallE C E) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hPiC)) RC
  have HI := types_inferred_raw hstep H hΓ HF.hasType.2 HG.hasType.2 rfl Ef Eg
  exact traced_pi_domain_compare heq hs hΓ HI rfl hΓ (Ctx.LiftN.zero [])
    HF.hasType.2 HG.hasType.2 rfl Ef Eg
    (proofErase_stage_zero_pi_trace heq hs hΓ hA hB RA)
    (proofErase_stage_zero_pi_trace heq hs hΓ hC hE RC)

/-- Full computed Pi comparison contains an inferred comparison of the original
domains, even when its internal checks traverse arbitrary control wrappers. -/
theorem stage_zero_pi_domains_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hC : env.HasType univs Γ C (.sort w)) (hE : env.HasType univs (C :: Γ) E (.sort z))
    (H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (.forallE A B)) (proofErase Γ (.forallE C E))) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) false
      (proofErase Γ A) (proofErase Γ C) := by
  apply stage_zero_computed_pi_domains_compare heq hs hΓ hA hB hC hE .refl .refl
  simpa only [show proofErase Γ (.forallE A B) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ (HasType.forallE hA hB)),
    show proofErase Γ (.forallE C E) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ (HasType.forallE hC hE))] using H

end Lean4Lean.VEnv.Strengthening
