import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedSimulationClosure

/-! # Core computation extended by proved universe conversion

The new steps belong only to the erased metatheory. Both descent and structural
simulation are closed proofs. In particular, equivalent recovered types can be
made literally equal without assuming native conversion completeness.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- The context-independent core plus explicit sort/constant universe conversion. -/
def ErasedLevelCore (D : Definitions) (a b : ProofShape) : Prop :=
  ErasedIotaPrimitive D a b ∨ LevelPrimitive univs a b

/-- Every level-extended core step descends through inserted binders. -/
theorem erased_level_core_descent (hs : D.Sound env univs) :
    ErasedScopedPrimitiveDescent (fun _ => ErasedLevelCore D) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht R
  rcases R with R | R
  · exact ErasedPrimitiveReplay.toDescent hs (erased_iota_replay hs) hΓ hΓ' W ht R
  · exact erased_level_primitive_descent hΓ hΓ' W ht R

/-- Core rules simulate as before; a universe step can be simulated by the
empty path because its reduct is already a structural variant of the target. -/
theorem erased_level_core_structural_simulation
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) :
    StructuralPrimitiveSimulation (ErasedLevelCore D) := by
  intro Γ Γ' e e' T T' a out R hΓ hΓ' ht ht' Ee V
  rcases R with R | R
  · obtain ⟨out', R', V'⟩ := proofErase_carrier_aligned_iota_variant hs hlevels hcon R hΓ hΓ' ht ht' Ee V
    exact ⟨out', .base (.inl R'), V'⟩
  · exact ⟨_, .refl, R.variant.symm.trans V⟩

/-- The entire finite level-extended core satisfies structural simulation. -/
theorem structuralVariantCompute_level_core
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) :
    StructuralVariantCompute (fun _ => ErasedLevelCore D) := by
  intro Γ Γ' e e' T T' out hΓ hΓ' ht ht' _ R V
  obtain ⟨out', R', V'⟩ := proofErase_carrier_aligned_compute_variant_of_simulation
    (erased_level_core_descent hs) (erased_level_core_structural_simulation hs hlevels hcon)
    R.core_forget hΓ hΓ' ht ht' rfl V
  exact ⟨out', R'.scoped (fun H => .base H), V'⟩

/-- Exact context transport is automatic for the context-independent extended core. -/
theorem structuralVariantComputeContext_level_core :
    StructuralVariantComputeContext (fun _ => ErasedLevelCore D) := by
  intro Γ Γ' e T Δ source out hΓ ht W HO EΓ Ee R
  exact R.core_forget.scoped (fun H => .base H)

/-- The extended core computes to any typed structural variant of its source. -/
theorem proofErase_carrier_aligned_level_core_variant_path
    (V : StructuralVariant a (proofErase Γ e))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T) :
    ScopedCompute (fun _ => ErasedLevelCore D) Δ a (proofErase Γ e) :=
  (proofErase_carrier_aligned_variant_level_compute V hΓ ht).scoped (fun H => .base (.inr H))

/-- All existing joint checking constructors retain their structural transport
laws after adding explicit universe conversion. -/
theorem ProofShape.ComputedJointCheck.level_core_variant
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (H : ComputedJointCheck (fun _ => ErasedLevelCore D) Δ kind a b) :
    ComputedJointVariantResult (fun _ => ErasedLevelCore D) Δ kind a b :=
  H.structural_variant (erased_level_core_descent hs) structuralVariantComputeContext_level_core
    (structuralVariantCompute_level_core hs hlevels hcon)

end Lean4Lean.VEnv.Strengthening
