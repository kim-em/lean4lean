import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointPrimitiveSubstitution

/-! # Concrete joint-stage substitution conditional only on re-synthesis

Stage induction discharges typed primitive simulation into the closed union.
The remaining semantic premise is joint domain re-synthesis at that union.
All resulting computations and joint checks have finite output-stage bounds.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Source-typed simulation of every concrete stage into the joint union.
The induction uses only preceding-stage simulation to transport guarded prefixes;
no substitution closure of the union is assumed. -/
theorem erased_joint_stage_subst_of_resynthesis
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hres : JointCarrierDomainResynthesis (ErasedJointUnion D) (ErasedJointUnion D)) :
    ∀ stage, ErasedPrimitiveSubstitutionTo (ErasedJointStage D stage) (ErasedJointUnion D) := by
  intro stage
  induction stage with
  | zero =>
    intro Γ Γ₀ σ τ e T out hΓ₀ W E ht H
    rw [proofErase_subst_with hΓ₀ W ht E]
    exact .base ⟨0, erased_iota_primitive_subst H⟩
  | succ stage ih =>
    intro Γ Γ₀ σ τ e T out hΓ₀ W E ht H
    rcases H with H | H | H
    · exact ih hΓ₀ W E ht H
    · have H' := proofErase_joint_singleton_subst heq
        (erased_joint_stage_descent heq hs stage) (erased_joint_union_descent heq hs)
        ih (fun H => ⟨stage, H⟩) hres hΓ₀ W E ht H.2
      rw [proofErase_subst_with hΓ₀ W ht E]
      exact .base (erased_joint_union_iff.2 (.inr (.inl
        ⟨H.1.subst (ContextSubstitution.of_typed hΓ₀ W E), H'⟩)))
    · have H' := proofErase_joint_prefix_subst heq (erased_joint_stage_descent heq hs stage)
        ih (fun H => ⟨stage, H⟩) hres hΓ₀ W E ht H
      rw [proofErase_subst_with hΓ₀ W ht E]
      exact .base (erased_joint_union_iff.2 (.inr (.inr H')))

/-- Union primitive simulation follows by selecting its finite source stage.
Joint re-synthesis is the only additional semantic premise beyond canonical Eq
and sound core definitions. -/
theorem erased_joint_union_subst_of_resynthesis
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hres : JointCarrierDomainResynthesis (ErasedJointUnion D) (ErasedJointUnion D)) :
    ErasedPrimitiveSubstitutionTo (ErasedJointUnion D) (ErasedJointUnion D) := by
  intro Γ Γ₀ σ τ e T out hΓ₀ W E ht H
  obtain ⟨stage, H⟩ := H
  exact erased_joint_stage_subst_of_resynthesis heq hs hres stage hΓ₀ W E ht H

/-- Every compatible union computation substitutes exactly at its typed source,
conditional on joint domain re-synthesis at the union. -/
theorem proofErase_joint_union_compute_subst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hres : JointCarrierDomainResynthesis (ErasedJointUnion D) (ErasedJointUnion D))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (e.subst σ)) (out.subst τ) :=
  proofErase_scoped_compute_subst_typed (erased_joint_union_descent heq hs)
    (erased_joint_union_subst_of_resynthesis heq hs hres) hΓ₀ W E ht R

/-- A typed finite-stage computation substitutes at one finite later stage.
The output is the exact substituted raw target; no selected recovery type is
preserved or assumed. -/
theorem proofErase_joint_compute_subst_finite
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hres : JointCarrierDomainResynthesis (ErasedJointUnion D) (ErasedJointUnion D))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedJointStage D stage) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ∃ later, stage ≤ later ∧ ScopedCompute (ErasedJointStage D later) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (e.subst σ)) (out.subst τ) := by
  have R' := proofErase_joint_union_compute_subst heq hs hres hΓ₀ W E ht
    (R.mono (fun H => ⟨stage, H⟩))
  obtain ⟨later, R'⟩ := R'.finite_stage erased_joint_stage_mono
  exact ⟨max stage later, Nat.le_max_left _ _, R'.mono (erased_joint_stage_mono (Nat.le_max_right _ _))⟩

/-- All common-typed joint comparisons substitute at a finite later stage.
The actual stage family, including its general singleton guards, is used. -/
theorem proofErase_joint_compare_subst_finite
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hres : JointCarrierDomainResynthesis (ErasedJointUnion D) (ErasedJointUnion D))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : JointCompare (ErasedJointStage D stage) (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b)) :
    ∃ later, stage ≤ later ∧ JointCompare (ErasedJointStage D later) (proofEraseCtx Γ₀) mode
      (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  have H' := proofErase_joint_compare_subst_of_resynthesis (erased_joint_stage_descent heq hs stage)
    (erased_joint_stage_subst_of_resynthesis heq hs hres stage) (fun H => ⟨stage, H⟩) hres hΓ₀ W ha hb H
  obtain ⟨later, H'⟩ := H'.finite_stage erased_joint_stage_mono
  exact ⟨max stage later, Nat.le_max_left _ _, H'.mono (erased_joint_stage_mono (Nat.le_max_right _ _))⟩

/-- Independently typed inferred comparisons also have finite substituted
certificates, provided their original endpoints are non-proofs. -/
theorem proofErase_joint_inferred_subst_finite
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hres : JointCarrierDomainResynthesis (ErasedJointUnion D) (ErasedJointUnion D))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (hna : ¬ IsProof Γ a) (hnb : ¬ IsProof Γ b)
    (H : JointCompare (ErasedJointStage D stage) (proofEraseCtx Γ) false (proofErase Γ a) (proofErase Γ b)) :
    ∃ later, stage ≤ later ∧ JointCompare (ErasedJointStage D later) (proofEraseCtx Γ₀) false
      (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  have H' := proofErase_joint_inferred_subst_of_resynthesis (erased_joint_stage_descent heq hs stage)
    (erased_joint_stage_subst_of_resynthesis heq hs hres stage) (fun H => ⟨stage, H⟩) hres hΓ₀ W ha hb hna hnb H
  obtain ⟨later, H'⟩ := H'.finite_stage erased_joint_stage_mono
  exact ⟨max stage later, Nat.le_max_left _ _, H'.mono (erased_joint_stage_mono (Nat.le_max_right _ _))⟩

/-- Actual joint carrier certificates substitute at a finite later stage with
the exact substituted supplied carrier, conditional only on union re-synthesis. -/
theorem proofErase_joint_carrier_subst_finite
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hres : JointCarrierDomainResynthesis (ErasedJointUnion D) (ErasedJointUnion D))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : JointCarrierGuard (ErasedJointStage D stage) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ a) (proofErase Γ b)) :
    ∃ later, stage ≤ later ∧ JointCarrierGuard (ErasedJointStage D later) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (A.subst σ)) (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  have H' := proofErase_joint_carrier_subst_of_resynthesis (erased_joint_stage_descent heq hs stage)
    (erased_joint_stage_subst_of_resynthesis heq hs hres stage) (fun H => ⟨stage, H⟩) hres hΓ₀ W ha hb H
  obtain ⟨later, H'⟩ := H'.finite_stage erased_joint_stage_mono
  exact ⟨max stage later, Nat.le_max_left _ _, H'.mono (erased_joint_stage_mono (Nat.le_max_right _ _))⟩

end Lean4Lean.VEnv.Strengthening
