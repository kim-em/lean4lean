import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStageZeroPiExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureBackwardContext

/-! # Exact sort exposure for compared control arguments

The shared type-head trace exposes a sort through constant expansions.
Actual comparison reflection identifies its universe, so an explicit level
step restores the original literal sort without a confluence assumption.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private infer_raw from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointTransport
variable [Params]

/-- Inferred comparison against a displayed sort exposes a sort at stage zero.
The raw statement does not assert equality of the exposed universe levels. -/
theorem stage_zero_inferred_sort_exposure
    (H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) Δ false (.sort u) T) :
    ∃ v, ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) Δ T (.sort v) := by
  obtain ⟨out, R, HO⟩ := H.ignored_type_head_trace (fun H => H) stage_zero_ignored_type_head_trace .sort
  obtain ⟨v, RB⟩ := IgnoredSortTrace.expose HO
  exact ⟨v, R.trans (.beta RB)⟩

/-- A sort-typed term compared with a literal sort computes back to that exact
sort at stage zero. This concerns an existing checker certificate; ordinary
definitional equality alone is not assumed to provide a computation. -/
theorem stage_zero_compared_sort_returns
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs)
    (ht : env.HasType univs Γ t (.sort v))
    (H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) mode
      (.sort u) (proofErase Γ t)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ t) (.sort u) := by
  have hU : env.HasType univs Γ (.sort u) (.sort (.succ u)) := .sort hu
  have EU : proofErase Γ (.sort u) = .sort u := if_neg (not_isProof_of_sort hΓ hU)
  have hstep : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D 0) :=
    erased_static_structure_eta_expansion_stage_descent heq hs 0
  have HI := proofErase_computed_joint_types_inferred hstep hΓ hU ht (EU ▸ H)
  rw [EU] at HI
  have HE := infer_raw hstep HI hΓ hU ht rfl EU rfl
    (not_isProof_of_sort hΓ hU) (not_isProof_of_sort hΓ ht)
  obtain ⟨w, R⟩ := stage_zero_inferred_sort_exposure HI
  obtain ⟨t', HT, ET⟩ := proofErase_scoped_compute_realize hstep hΓ ht rfl rfl R
  have ESort : t' = .sort w := by
    cases t' <;> simp only [proofErase] at ET <;> split at ET <;> cases ET <;> rfl
  subst t'
  have HW : u ≈ w := (HE.toU.trans henv hΓ HT.toU).sort_inv henv hΓ
  exact R.trans (.base (.inl (.inr (.sort HW.symm hu))))

/-- Comparing a converted binder with a literal universe supplies exact
stage-zero native images from the universe context to that binder context.
Only the annotation comparison is computed; ordinary domain equality supplies
the typed interpretation of the identity substitution. -/
theorem stage_zero_compared_sort_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAC : env.IsDefEq univs Γ (.sort u) C (.sort v))
    (H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) mode
      (.sort u) (proofErase Γ C)) :
    StaticStructureEtaNativeSubstitution.ImageSubstitution D 0
      (proofEraseCtx (.sort u :: Γ)) (proofEraseCtx (C :: Γ)) ProofShape.Subst.id := by
  have RC := stage_zero_compared_sort_returns heq hs hΓ
    (HAC.hasType.1.sort_inv henv.ordered) HAC.hasType.2 H
  have EU : proofErase Γ (.sort u) = .sort u := if_neg (not_isProof_of_sort hΓ HAC.hasType.1)
  rw [← EU] at RC
  intro Γ' hΓ' EΓ'
  exact static_structure_native_backward_context heq hs hΓ HAC.symm RC hΓ' EΓ'

/-- All finite-stage body comparisons transport to a binder compared with
their original literal universe. The exact endpoints and guard depth survive;
this is restricted universe-binder transport, not general compared-context
transport for arbitrary annotations. -/
theorem proofErase_check_compared_sort_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAC : env.IsDefEq univs Γ (.sort u) C (.sort v))
    (HC : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) domainMode
      (.sort u) (proofErase Γ C))
    (ha : env.HasType univs (.sort u :: Γ) a T) (hb : env.HasType univs (.sort u :: Γ) b T)
    (H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx (.sort u :: Γ)) mode
      (proofErase (.sort u :: Γ) a) (proofErase (.sort u :: Γ) b)) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx (C :: Γ)) mode
      (proofErase (C :: Γ) a) (proofErase (C :: Γ) b) := by
  have hΓU : OnCtx (.sort u :: Γ) (env.IsType univs) := ⟨hΓ, v, HAC.hasType.1⟩
  have HR := StaticStructureEtaNativeSubstitution.check heq hs (k := 0) H hΓU ha hb rfl rfl rfl
    (stage_zero_compared_sort_context heq hs hΓ HAC HC)
  simp only [Nat.add_zero, ProofShape.subst_id] at HR
  rw [proofErase_defeqCtx hΓU (IsDefEqCtx.succ .zero HAC) ha,
    proofErase_defeqCtx hΓU (IsDefEqCtx.succ .zero HAC) hb] at HR
  exact HR

end Lean4Lean.VEnv.Strengthening
