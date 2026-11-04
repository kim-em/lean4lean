import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedScopedHeadBeta
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierRecoveredPrimitiveRenaming
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierRecoveredUnion

/-! # Core computations in paired scoped body substitution

The source may now use the full core delta/iota primitive relation in addition
to beta, recursive eta and structure fields. Its typed primitive simulation is
proved from raw core substitution, rather than supplied as an unproved domain
re-synthesis or beta-stability premise. Higher guarded stages remain separate.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

private theorem core_substitution :
    ErasedPrimitiveSubstitutionTo (ErasedJointStage D 0) (ErasedCarrierRecoveredUnion D) := by
  intro Γ Γ₀ σ τ e T out hΓ₀ W E ht H
  rw [proofErase_subst_with hΓ₀ W ht E]
  exact .base ⟨0, erased_iota_primitive_subst H⟩

/-- Core delta/iota scoped checking transports under two inferred-related
actual image maps, including all recursive eta and structure-field cases.
Every primitive-substitution premise is discharged for the concrete source. -/
theorem proofErase_carrier_aligned_core_paired_substitution
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (W : CarrierAlignedSubstitution (ErasedCarrierRecoveredUnion D) Γ Γ₀ σ φ ρ τ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : ScopedCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b)) :
    CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ₀) mode
      (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst φ)) :=
  proofErase_carrier_aligned_scoped_paired_substitution_with_primitives
    (erased_joint_stage_descent heq hs 0) core_substitution
    (erased_carrier_recovered_union_descent heq hs) (erased_carrier_recovered_union_rename heq hs) W ha hb H

/-- Distinct inferred-related arguments instantiate any common-typed core
scoped body comparison. Neither image recovery nor a computation join is needed;
the source body computations may include delta/iota as well as beta. -/
theorem proofErase_carrier_aligned_core_paired_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (HX : CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) false
      (proofErase Γ x) (proofErase Γ y))
    (H : ScopedCompare (ErasedJointStage D 0) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst x)) (proofErase Γ (b.inst y)) := by
  simpa only [VExpr.inst_eq] using proofErase_carrier_aligned_core_paired_substitution heq hs
    (CarrierAlignedSubstitution.inst hΓA hx hy HX) ha hb H

/-- Core inferred lambda checking survives paired head beta, even when the
functions first compute through delta/iota and change their written domains.
Only inferred comparison of the argument images is required; all source
primitive interfaces are proved for the concrete core relation. -/
theorem proofErase_carrier_aligned_core_head_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x P) (hy : env.HasType univs Γ y P)
    (hf : env.HasType univs Γ (.lam A b) (.forallE P (.sort .zero)))
    (hg : env.HasType univs Γ (.lam D₀ c) (.forallE P (.sort .zero)))
    (HX : CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) false
      (proofErase Γ x) (proofErase Γ y))
    (H : ScopedCompare (ErasedJointStage D 0) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam D₀ c))) :
    CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) true
      (proofErase Γ (b.inst x)) (proofErase Γ (c.inst y)) :=
  proofErase_carrier_aligned_scoped_head_beta_with_primitives
    (erased_joint_stage_descent heq hs 0) (erased_joint_stage_head 0) core_substitution
    (erased_carrier_recovered_union_descent heq hs) (erased_carrier_recovered_union_rename heq hs)
    hΓ hx hy hf hg HX H

end Lean4Lean.VEnv.Strengthening
