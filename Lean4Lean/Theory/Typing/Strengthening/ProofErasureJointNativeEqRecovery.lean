import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointTypedBinderComputation

/-! # Native Eq recovery in the union with a recoverable anchor

The fixed anchor need only recover its supplied carrier. Typed Pi inversion
and recoverable single substitution replace unrestricted primitive substitution.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private eq_carrier_recovery
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqNativeCarrierRecovery
variable [Params]

/-- A typed union path can be instantiated at an anchor that recovers its
assigned type. The anchor recovery has a finite stage bound; the path need not
share that bound. Proof anchors require no selected recovery. -/
theorem proofErase_joint_union_compute_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hz : env.HasType univs Γ z A)
    (HR : ¬ IsProof Γ z → ScopedTypeRecovery (ErasedJointUnion D)
      (proofEraseCtx Γ) (proofErase Γ z) (proofErase Γ A))
    (ht : env.HasType univs (A :: Γ) e T)
    (R : ScopedCompute (ErasedJointUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) e) out) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      ((proofErase (A :: Γ) e).inst (proofErase Γ z)) (out.inst (proofErase Γ z)) := by
  have HX : ∃ stage, ¬ IsProof Γ z → ScopedTypeRecovery (ErasedJointStage D stage)
      (proofEraseCtx Γ) (proofErase Γ z) (proofErase Γ A) := by
    by_cases hp : IsProof Γ z
    · exact ⟨0, fun hn => (hn hp).elim⟩
    · obtain ⟨stage, H⟩ := (HR hp).finite_stage erased_joint_stage_mono
      exact ⟨stage, fun _ => H⟩
  obtain ⟨stage, HX⟩ := HX
  obtain ⟨u, hA⟩ := hz.isType henv hΓ
  have H := R.subst_recovering (erased_joint_union_descent heq hs)
    (erased_joint_stage_rename heq hs stage) (erased_joint_union_recovering heq hs stage)
    (show OnCtx (A :: Γ) (env.IsType univs) from ⟨hΓ, u, hA⟩) ht rfl rfl
    (RecoveringSubstitution.inst hΓ hz HX)
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using H

/-- A recovered Eq prefix's selected type computes from the native final Pi
in the full union, provided the fixed anchor recovers its supplied carrier.
No general union substitution law is required. -/
theorem proofErase_joint_union_eq_prefix_native_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hα : env.HasType univs Γ α (.sort u))
    (hz : env.HasType univs Γ z α)
    (HR : ¬ IsProof Γ z → ScopedTypeRecovery (ErasedJointUnion D)
      (proofEraseCtx Γ) (proofErase Γ z) (proofErase Γ α))
    (R : ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ)
      (.app (.app (.const ``Eq [u]) (proofErase Γ α)) (proofErase Γ z)) T) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (.forallE (proofErase Γ α) (.sort .zero)) T := by
  classical
  generalize EΔ : proofEraseCtx Γ = Δ at R
  generalize E : ProofShape.app (.app (.const ``Eq [u]) (proofErase Γ α)) (proofErase Γ z) = e at R
  induction R with
  | app RF =>
    cases E
    have RC := eq_carrier_recovery heq erased_joint_union_head RF
    have hΓα : OnCtx (α :: Γ) (env.IsType univs) := ⟨hΓ, u, hα⟩
    have hαw : env.HasType univs (α :: Γ) α.lift (.sort u) := hα.weak henv
    have hΓαα : OnCtx (α.lift :: α :: Γ) (env.IsType univs) := ⟨hΓα, u, hαw⟩
    have hS := HasType.sort (env := env) (U := univs) (Γ := α.lift :: α :: Γ)
      (l := .zero) (by trivial)
    have hB := HasType.forallE hαw hS
    have EB : proofErase (α :: Γ) (.forallE α.lift (.sort .zero)) =
        .forallE ((proofErase Γ α).liftN 1) (.sort .zero) := by
      change (if IsProof (α :: Γ) (.forallE α.lift (.sort .zero)) then _ else _) = _
      rw [if_neg (not_isProof_of_sort hΓα hB)]
      rw [show proofErase (α.lift :: α :: Γ) (.sort .zero) = .sort .zero from
        if_neg (not_isProof_of_sort hΓαα hS)]
      rw [show proofErase (α :: Γ) α.lift = (proofErase Γ α).liftN 1 from
        proofErase_liftN hΓ hΓα Ctx.LiftN.one hα]
    rw [← EB] at RC
    obtain ⟨A, B, HE, _, RB⟩ := proofErase_joint_union_forallE_inv heq hs hΓ hα hB EΔ RC
    cases HE
    rw [← EΔ] at RB
    change ScopedCompute (ErasedJointUnion D) (proofEraseCtx (α :: Γ)) _ _ at RB
    have HI := proofErase_joint_union_compute_inst heq hs hΓ hz HR hB RB
    rw [EB] at HI
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst,
      ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id, EΔ] using HI
  | convert _ H ih => exact (ih EΔ E).trans H
  | bvar | sort | const | lam | forallE | proj => cases E

/-- The selected last-argument domain of a union Eq prefix is reachable from
its supplied carrier when the fixed anchor recovers that carrier. -/
theorem proofErase_joint_union_eq_prefix_domain_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hα : env.HasType univs Γ α (.sort u))
    (hz : env.HasType univs Γ z α)
    (HR : ¬ IsProof Γ z → ScopedTypeRecovery (ErasedJointUnion D)
      (proofEraseCtx Γ) (proofErase Γ z) (proofErase Γ α))
    (R : ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ)
      (.app (.app (.const ``Eq [u]) (proofErase Γ α)) (proofErase Γ z)) (.forallE A B)) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ α) A := by
  obtain ⟨A', B', HE, RA⟩ := (proofErase_joint_union_eq_prefix_native_compute
    heq hs hΓ hα hz HR R).forallE_domain_inv erased_joint_union_head
  cases HE
  exact RA

end Lean4Lean.VEnv.Strengthening
