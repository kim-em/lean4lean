import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedCorePairedSubstitution

/-! # Paired substitution through all finite structure-singleton stages

The source computations include arbitrary finite nesting of registered general
singleton guards and explicit structure-carrier Eq prefixes. Their existing
interpreted substitution law supplies the primitive interface of paired scoped
checking. Recovered-application and mutually recursive carrier guards remain
outside this source relation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- All finite structure-singleton stages, with each primitive retaining its
own finite bound. This does not include recovered-application guard stages. -/
def ErasedStructureSingletonUnion (D : PureObservation.Definitions)
    (Δ : List ProofShape) (a b : ProofShape) : Prop :=
  ∃ stage, ErasedStructureSingletonStage D stage Δ a b

/-- Structure-singleton primitives already occur in the recovered-carrier
union. The chain of embeddings preserves the original finite stage. -/
theorem erased_structure_singleton_union_into_carrier_recovered
    (H : ErasedStructureSingletonUnion D Δ a b) : ErasedCarrierRecoveredUnion D Δ a b := by
  obtain ⟨stage, H⟩ := H
  exact ⟨stage, erased_computed_into_carrier_recovered stage (erased_joint_into_computed stage
    (erased_recursive_singleton_into_joint stage (erased_application_into_recursive_singleton stage
      (erased_structure_into_application stage H))))⟩

/-- Every primitive in the structure-singleton union descends through inserted
binder blocks using its own finite-stage descent proof. -/
theorem erased_structure_singleton_union_descent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ErasedScopedPrimitiveDescent (ErasedStructureSingletonUnion D) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht H
  obtain ⟨stage, H⟩ := H
  exact erased_structure_singleton_stage_descent heq hs stage hΓ hΓ' W ht H

/-- Union primitives retain constant or projection heads. -/
theorem erased_structure_singleton_union_head
    (H : ErasedStructureSingletonUnion D Δ a b) : PrimitiveHead a := by
  obtain ⟨stage, H⟩ := H
  exact erased_structure_singleton_stage_head stage H

/-- Arbitrary interpreted substitutions preserve each primitive's original
finite structure-singleton bound, hence the union. -/
theorem erased_structure_singleton_union_subst (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : ErasedStructureSingletonUnion D Δ a b) (W : ContextSubstitution Δ Δ' τ) :
    ErasedStructureSingletonUnion D Δ' (a.subst τ) (b.subst τ) := by
  obtain ⟨stage, H⟩ := H
  exact ⟨stage, erased_structure_singleton_stage_subst heq hs stage H W⟩

/-- The primitive simulation for paired scoped checking is discharged for
all finite structure-singleton stages, including their nested family guards. -/
theorem erased_structure_singleton_union_substitution_to_carrier_recovered
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ErasedPrimitiveSubstitutionTo (ErasedStructureSingletonUnion D) (ErasedCarrierRecoveredUnion D) := by
  intro Γ Γ₀ σ τ e T out hΓ₀ W E ht H
  rw [proofErase_subst_with hΓ₀ W ht E]
  exact .base (erased_structure_singleton_union_into_carrier_recovered
    (erased_structure_singleton_union_subst heq hs H (ContextSubstitution.of_typed hΓ₀ W E)))

/-- Full scoped checking with arbitrarily nested structure-singleton source
computation survives paired maps at inferred-related images. No additional
primitive simulation or native-image recovery premise remains. -/
theorem proofErase_carrier_aligned_guarded_paired_substitution
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (W : CarrierAlignedSubstitution (ErasedCarrierRecoveredUnion D) Γ Γ₀ σ φ ρ τ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : ScopedCompare (ErasedStructureSingletonUnion D) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b)) :
    CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ₀) mode
      (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst φ)) :=
  proofErase_carrier_aligned_scoped_paired_substitution_with_primitives
    (erased_structure_singleton_union_descent heq hs)
    (erased_structure_singleton_union_substitution_to_carrier_recovered heq hs)
    (erased_carrier_recovered_union_descent heq hs) (erased_carrier_recovered_union_rename heq hs) W ha hb H

/-- Common-typed guarded scoped bodies instantiate at distinct inferred-related
images, with no shared reduct of the bodies or join of the images required. -/
theorem proofErase_carrier_aligned_guarded_paired_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (HX : CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) false
      (proofErase Γ x) (proofErase Γ y))
    (H : ScopedCompare (ErasedStructureSingletonUnion D) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst x)) (proofErase Γ (b.inst y)) := by
  simpa only [VExpr.inst_eq] using proofErase_carrier_aligned_guarded_paired_substitution heq hs
    (CarrierAlignedSubstitution.inst hΓA hx hy HX) ha hb H

/-- Paired proposition-valued head beta allows arbitrarily nested general
singleton and structure-carrier source computations before the inferred lambda
check. All primitive interfaces are discharged; the argument check remains explicit. -/
theorem proofErase_carrier_aligned_guarded_head_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x P) (hy : env.HasType univs Γ y P)
    (hf : env.HasType univs Γ (.lam A b) (.forallE P (.sort .zero)))
    (hg : env.HasType univs Γ (.lam D₀ c) (.forallE P (.sort .zero)))
    (HX : CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) false
      (proofErase Γ x) (proofErase Γ y))
    (H : ScopedCompare (ErasedStructureSingletonUnion D) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam D₀ c))) :
    CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) true
      (proofErase Γ (b.inst x)) (proofErase Γ (c.inst y)) :=
  proofErase_carrier_aligned_scoped_head_beta_with_primitives
    (erased_structure_singleton_union_descent heq hs) erased_structure_singleton_union_head
    (erased_structure_singleton_union_substitution_to_carrier_recovered heq hs)
    (erased_carrier_recovered_union_descent heq hs) (erased_carrier_recovered_union_rename heq hs)
    hΓ hx hy hf hg HX H

end Lean4Lean.VEnv.Strengthening
