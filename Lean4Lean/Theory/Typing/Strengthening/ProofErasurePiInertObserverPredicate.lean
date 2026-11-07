import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertSortedProjectionFrames

/-! # Exact same-scope projection predicates and field transfer

A closed record in the observer's scope has only identity application frames
left, with no pending arguments. Their continuation predicate is exactly the
ordinary projected-computation predicate for every raw competitor, not only
for the selected typed execution. This preserves global minimum comparisons
when replacing a body endpoint by its computed type-field major.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- At a closed record already in the observer's scope, all remaining frames
have exactly the ordinary projection predicate at every raw endpoint and count.
Actual typing is used only to identify the frames; competitors remain untyped. -/
theorem PiInertProjectionContinuationRun.closed_record_same_scope_predicate
    (H : PiInertProjectionContinuationRun D Ω family index out Δ K e ck)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info)
    (hscope : Δ = Ω)
    (hΓ : OnCtx Γ (env.IsType univs)) (EΓ : proofEraseCtx Γ = Δ)
    (hm : env.HasType univs Γ m (.const family [])) (Ee : proofErase Γ m = e) :
    ∀ candidate budget, K candidate budget ↔
      PiInertProjectionContinuation D Δ family index out candidate budget := by
  induction H generalizing Γ m with
  | projection => exact fun _ _ => Iff.rfl
  | @application Δ e Θ τ args n cs e' K ck HT W HNext RNext HK ih =>
    cases W with
    | identity =>
      have hnil := TypedSource.closed_record_pending_nil hi hΓ EΓ hm
        (by simpa only [ProofShape.subst_id, ← Ee] using HNext)
      simp only [hnil, ProofShape.mkApps, ProofShape.subst_id] at RNext
      obtain ⟨m', HE, Em'⟩ := proofErase_scoped_compute_realize
        (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n))
        hΓ hm EΓ Ee RNext.forget
      have IH := ih hscope hΓ EΓ HE.hasType.2 Em'
      intro candidate budget
      constructor
      · rintro ⟨later, j, endpoint, k, hsum, RJ, RK⟩
        simp only [hnil, ProofShape.mkApps, ProofShape.subst_id] at RJ
        obtain ⟨observerStage, RO⟩ := (IH endpoint k).1 RK
        exact ⟨max later observerStage, hsum ▸
          (RJ.mono (pi_inert_stage_mono (Nat.le_max_left _ _))).proj.trans
            (RO.mono (pi_inert_stage_mono (Nat.le_max_right _ _)))⟩
      · rintro ⟨later, RJ⟩
        refine ⟨later, 0, candidate, budget, by omega, ?_, (IH candidate budget).2 ⟨later, RJ⟩⟩
        simpa only [hnil, ProofShape.mkApps, ProofShape.subst_id] using
          (ScopedComputeCount.beta (Step := PiInertStage D later) (Δ := Δ) (BetaRed.refl (e := candidate)))
    | inst =>
      have HL := HK.scope_length_le
      have HE := congrArg List.length hscope
      simp only [List.length_cons] at HE
      omega
  | retained _ _ _ _ HK ih =>
    have HL := HK.scope_length_le
    have HE := congrArg List.length hscope
    simp only [List.length_cons] at HE
    omega

/-- A same-scope closed-record frame minimum is an ordinary global projection
minimum, including comparisons with every finite stage and raw major path.
The reverse predicate correspondence supplies competitors at zero body cost. -/
theorem PiInertProjectionContinuationMinimum.closed_record_global_minimum
    (H : PiInertProjectionContinuationMinimum D Δ family index out Δ source cost)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info)
    (hΓ : OnCtx Γ (env.IsType univs)) (EΓ : proofEraseCtx Γ = Δ)
    (hm : env.HasType univs Γ m (.const family [])) (Ee : proofErase Γ m = source) :
    (∃ n, ScopedComputeCount (PiInertStage D n) cost Δ (.proj family index source) out) ∧
    ∀ later j, ScopedComputeCount (PiInertStage D later) j Δ (.proj family index source) out → cost ≤ j := by
  have R := H.closed_record_same_scope heq hs hi hΓ EΓ hm Ee
  obtain ⟨K, n, cb, ck, endpoint, _, RB, HK, _, HM⟩ := H
  obtain ⟨m', HE, Em'⟩ := proofErase_scoped_compute_realize
    (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n))
    hΓ hm EΓ Ee RB.forget
  have HP := HK.closed_record_same_scope_predicate heq hs hi rfl hΓ EΓ HE.hasType.2 Em'
  refine ⟨R, ?_⟩
  intro later j RJ
  have HH := HM later 0 source j (.beta .refl) ((HP source j).2 ⟨later, RJ⟩)
  omega

/-- The computed-projection field relay accepts any actual remaining run in
the observer's scope. Closed pair image typing supplies both exact flattening
and reconstruction of raw competitors, so the original global frame minimum
is preserved rather than replaced by an unrelated projection minimum. -/
theorem pi_inert_projection_frame_run_smaller_failure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0)
    (HSort : ControlTyping Ξ (.proj family 0 source) (.sort u))
    (RF : ScopedComputeCount (PiInertStage D bodyStage) fieldCost Ξ (.proj family 0 source) field)
    (HT : TypedSource Ξ (ProofShape.mkApps (.const info.ctorName []) [field, value']))
    (W : ContextSubstitution Ξ Ω τ)
    (HNext : TypedSource Ω (ProofShape.mkApps
      ((ProofShape.mkApps (.const info.ctorName []) [field, value']).subst τ) pending))
    (RNext : ScopedComputeCount (PiInertStage D nextStage) cs Ω (ProofShape.mkApps
      ((ProofShape.mkApps (.const info.ctorName []) [field, value']).subst τ) pending) major)
    (HK : PiInertProjectionContinuationRun D Ω family 0 out Ω K major ck)
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (hgap : fieldCost+cs+ck < cost)
    (HM : ∀ later j endpoint k, ScopedComputeCount (PiInertStage D later) j Ξ source endpoint →
      PiInertApplicationContinuation D Ω τ pending K endpoint k → cost ≤ j+k) :
    pending = [] ∧ cs+ck < cost ∧
      PiInertPairProjectionBudgetFailure D Ω family info
        (field.subst τ) (value'.subst τ) out (cs+ck) := by
  have EP := TypedSource.closed_constructor_image_pending_nil hi hp hz (by simp [hf]) HT W HNext
  have EI : (ProofShape.mkApps (.const info.ctorName []) [field, value']).subst τ =
      ProofShape.mkApps (.const info.ctorName []) [field.subst τ, value'.subst τ] := by
    simp only [ProofShape.subst_mkApps, ProofShape.subst, List.map_cons, List.map_nil]
  have HTimage : TypedSource Ω
      (ProofShape.mkApps (.const info.ctorName []) [field.subst τ, value'.subst τ]) := by
    rw [EP, EI] at HNext
    exact HNext
  obtain ⟨Γ, image, hΓ, EΓ, hm, Em⟩ := TypedSource.closed_constructor_realize hi hp hz
    (by simp [hf]) HTimage
  have RN : ScopedComputeCount (PiInertStage D nextStage) cs Ω (proofErase Γ image) major := by
    rw [Em]
    rw [EP, EI] at RNext
    exact RNext
  obtain ⟨actualMajor, HE, EM⟩ := proofErase_scoped_compute_realize
    (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs nextStage))
    hΓ hm EΓ rfl RN.forget
  obtain ⟨observerStage, RObserve⟩ := HK.closed_record_same_scope heq hs hi rfl hΓ EΓ HE.hasType.2 EM
  have HP := HK.closed_record_same_scope_predicate heq hs hi rfl hΓ EΓ HE.hasType.2 EM
  apply pi_inert_projection_frames_smaller_failure heq hs hi hp hf hz HSort RF HT W HNext
    RNext RObserve hout hgap
  rintro later j endpoint k RJ ⟨suffixStage, suffixCost, endpoint', tailCost, hsum, RS, RO⟩
  exact HM later j endpoint k RJ
    ⟨suffixStage, suffixCost, endpoint', tailCost, hsum, RS, (HP endpoint' tailCost).2 RO⟩

end Lean4Lean.VEnv.Strengthening
