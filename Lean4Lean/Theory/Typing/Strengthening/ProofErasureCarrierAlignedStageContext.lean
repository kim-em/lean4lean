import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedContextClosure

/-! # Context transport advances one recovered singleton stage

Transport of general singleton and Eq-prefix certificates uses only the previous
stage's exact context transport and structural simulation. The first successor
stage is therefore closed unconditionally from the proved level-extended base.
The successor interface keeps preceding structural simulation explicit;
LevelStageClosure discharges it uniformly.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape PureObservation
variable [Params]

/-- The next recovered stage transports every typed root occurrence. Earlier
stage roots may use finite transported paths; new guarded roots retain exact outputs. -/
theorem erased_level_recovered_successor_root_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hctx : StructuralVariantComputeContext (ErasedLevelRecoveredStage D stage))
    (hsim : StructuralVariantCompute (ErasedLevelRecoveredStage D stage)) :
    StructuralPrimitiveContext (ErasedLevelRecoveredStage D (stage + 1)) := by
  intro Γ Γ' e T out hΓ W HO ht R
  have hstep : ErasedScopedPrimitiveDescent (ErasedLevelRecoveredStage D stage) :=
    erased_level_recovered_stage_descent heq hs stage
  rcases R with R | R | R
  · have R' := hctx hΓ ht W HO rfl rfl (.base R)
    rw [proofErase_defeqCtx hΓ W ht] at R'
    exact R'.mono (fun H => .inl H)
  · exact .base (.inr (.inl (proofErase_recovered_singleton_structural_context heq hstep hctx hsim
      (fun H => .base (erased_level_primitive_into_stage H stage)) hΓ W HO ht R)))
  · exact .base (.inr (.inr (proofErase_computed_joint_prefix_structural_context heq hstep hctx hsim hΓ W HO ht R)))

/-- Previous-stage structural simulation and context transport suffice for
context transport of every finite path at the next stage. -/
theorem structuralVariantComputeContext_level_successor
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hctx : StructuralVariantComputeContext (ErasedLevelRecoveredStage D stage))
    (hsim : StructuralVariantCompute (ErasedLevelRecoveredStage D stage)) :
    StructuralVariantComputeContext (ErasedLevelRecoveredStage D (stage + 1)) :=
  structuralVariantComputeContext_of_roots (erased_level_recovered_stage_descent heq hs _)
    (erased_level_recovered_successor_root_context heq hs hctx hsim)

/-- The first stage of general recovered-family singleton and Eq-prefix
computation has unconditional exact context transport over the concrete core. -/
theorem structuralVariantComputeContext_level_one
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) :
    StructuralVariantComputeContext (ErasedLevelRecoveredStage D 1) :=
  structuralVariantComputeContext_level_successor heq hs structuralVariantComputeContext_level_core
    (structuralVariantCompute_level_core hs hlevels hcon)

/-- Once structural simulation is proved at every stage, exact context transport
follows at every stage by the closed successor construction. This states the
simulation premise explicitly; LevelStageClosure proves it uniformly rather
than inferring it from semantic descent. -/
theorem structuralVariantComputeContext_level_stages
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hsim : ∀ stage, StructuralVariantCompute (ErasedLevelRecoveredStage D stage)) :
    ∀ stage, StructuralVariantComputeContext (ErasedLevelRecoveredStage D stage) := by
  intro stage
  induction stage with
  | zero => exact structuralVariantComputeContext_level_core
  | succ stage ih => exact structuralVariantComputeContext_level_successor heq hs ih (hsim stage)

end Lean4Lean.VEnv.Strengthening
