import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedStageContext

/-! # Closing structural transport at every level-extended stage

A structural variant can first convert back to the original raw shape, using a
typed representative of that shape in the target context. Exact context
transport then follows the original path. This derives structural simulation
from context transport and closes the stage induction without a new assumption.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape PureObservation
variable [Params]

/-- With explicit universe conversion available, exact context transport
implies structural simulation. The simulated output is literally the original
output; no independent endpoint-variation closure for guard checking is needed. -/
theorem structuralVariantCompute_of_context_and_levels
    (hstep : ErasedScopedPrimitiveDescent Step) (hctx : StructuralVariantComputeContext Step)
    (hlevel : ∀ {Δ a b}, LevelPrimitive univs a b → ScopedCompute Step Δ a b) :
    StructuralVariantCompute Step := by
  intro Γ Γ' e e' T T' out hΓ hΓ' ht ht' HO R V
  have W := proofErase_carrier_aligned_context_variant_defeq (Step := Step) hstep hΓ hΓ' HO
  have htΓ' := ht.defeqDFC henv W
  have EE := proofErase_defeqCtx hΓ W ht
  have Rback := (proofErase_carrier_aligned_variant_level_compute
    (by simpa only [← EE] using V.symm) hΓ' htΓ').scoped (Δ := proofEraseCtx Γ') hlevel
  have Rforward := hctx hΓ ht W HO rfl rfl R
  refine ⟨out, .trans Rback ?_, .refl⟩
  simpa only [EE] using Rforward

/-- Every finite level-extended recovered stage has both exact context
transport and structural simulation. The induction uses the preceding stage's
proved certificate laws for singleton and Eq-prefix guards. -/
theorem erased_level_recovered_stage_structural_closure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ stage, StructuralVariantComputeContext (ErasedLevelRecoveredStage D stage) ∧
      StructuralVariantCompute (ErasedLevelRecoveredStage D stage) := by
  intro stage
  induction stage with
  | zero =>
    have HC : StructuralVariantComputeContext (ErasedLevelRecoveredStage D 0) :=
      structuralVariantComputeContext_level_core
    exact ⟨HC, structuralVariantCompute_of_context_and_levels (erased_level_recovered_stage_descent heq hs 0)
      HC (fun H => .base (erased_level_primitive_into_stage H 0))⟩
  | succ stage ih =>
    have HC : StructuralVariantComputeContext (ErasedLevelRecoveredStage D (stage + 1)) :=
      structuralVariantComputeContext_level_successor heq hs ih.1 ih.2
    exact ⟨HC, structuralVariantCompute_of_context_and_levels (erased_level_recovered_stage_descent heq hs _)
      HC (fun H => .base (erased_level_primitive_into_stage H _))⟩

/-- Exact context transport at each stage now has no simulation premise. -/
theorem structuralVariantComputeContext_level_stage
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (stage : Nat) :
    StructuralVariantComputeContext (ErasedLevelRecoveredStage D stage) :=
  (erased_level_recovered_stage_structural_closure heq hs stage).1

/-- Structural computation simulation at each stage now has no level-
compatibility or concrete-pattern premise: explicit conversion reaches the
original raw source before replaying its transported computation. -/
theorem structuralVariantCompute_level_stage
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (stage : Nat) :
    StructuralVariantCompute (ErasedLevelRecoveredStage D stage) :=
  (erased_level_recovered_stage_structural_closure heq hs stage).2

/-- The full joint checking language transports at every finite stage. -/
theorem ProofShape.ComputedJointCheck.level_stage_variant
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : ComputedJointCheck (ErasedLevelRecoveredStage D stage) Δ kind a b) :
    ComputedJointVariantResult (ErasedLevelRecoveredStage D stage) Δ kind a b :=
  H.structural_variant (erased_level_recovered_stage_descent heq hs stage)
    (structuralVariantComputeContext_level_stage heq hs stage)
    (structuralVariantCompute_level_stage heq hs stage)

/-- Full recovered comparison transports at every finite stage, retaining a
literal common native carrier at recovered nodes. -/
theorem proofErase_carrier_aligned_level_stage_recovered_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (HO : List.Forall₂ StructuralVariant (proofEraseCtx Γ) (proofEraseCtx Γ'))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : CarrierRecoveredCompare (ErasedLevelRecoveredStage D stage) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b)) :
    CarrierRecoveredCompare (ErasedLevelRecoveredStage D stage) (proofEraseCtx Γ') mode
      (proofErase Γ' a) (proofErase Γ' b) := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedLevelRecoveredStage D stage) :=
    erased_level_recovered_stage_descent heq hs stage
  have W := proofErase_carrier_aligned_context_variant_defeq (Step := ErasedLevelRecoveredStage D stage) hstep hΓ hΓ' HO
  have H' := H.structural_context hstep (structuralVariantComputeContext_level_stage heq hs stage)
    (structuralVariantCompute_level_stage heq hs stage)
    (fun H => .base (erased_level_primitive_into_stage H stage)) hΓ ha hb rfl rfl rfl W HO
  rwa [proofErase_defeqCtx hΓ W ha, proofErase_defeqCtx hΓ W hb] at H'

end Lean4Lean.VEnv.Strengthening
