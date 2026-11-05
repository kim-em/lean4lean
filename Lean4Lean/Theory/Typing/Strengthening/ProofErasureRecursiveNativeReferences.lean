import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelRecursiveTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeControlReferenceReturn

/-! # Complete native outputs compared through evolving references

One recursive comparison between selected references suffices for all native
selections and final tails at stage zero. References need not be fixed, return
from their reducts, or have a common core reduct with each other. Constructing
these recursive certificates for arbitrary compared functions remains open.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- A recursive comparison between any two selected native outputs transports
to every pair of complete native outputs of the respective sources. The sources
may differ, including their assigned types. Native coherence joins each output
to its own reference, then the references evolve independently. -/
theorem stage_zero_recursive_reference_outputs_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hl : D.LevelCompatible univs) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hD : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs Γ e A) (hf : env.HasType univs Γ f B)
    (RE : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ e) referenceE)
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ f) referenceF)
    (H : LevelRecursiveGuard D mode referenceE referenceF)
    (RL : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ e) outL)
    (RR : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ f) outR) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) mode outL outR := by
  have JL := stage_zero_native_outputs_join heq hs hl hcon hD hc hΓ he RL RE
  have JR := stage_zero_native_outputs_join heq hs hl hcon hD hc hΓ hf RR RF
  exact ((H.of_joins hs hl hcon (proofErase_level_core_confluent hs hl hcon hc) JL JR).scoped
    (fun H => .base (.inl H))).joint.computed

/-- A recursive comparison of the selected codomains at one actual shared
argument compares complete native application outputs. Neither application
must select the supplied reference Pi internally. The two original arguments
compute to the shared argument, with no normalization requirement on the
instantiated reference types. Arbitrary Pi-comparison certificates do not yet
supply the recursive result comparison required here. -/
theorem stage_zero_recursive_reference_application_outputs_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hl : D.LevelCompatible univs) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hD : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE C T))
    (hg : env.HasType univs Γ g (.forallE C U))
    (hx : env.HasType univs Γ x C) (hy : env.HasType univs Γ y C) (hp : env.HasType univs Γ p C)
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ f) (.forallE X Y))
    (RG : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ g) (.forallE Z W))
    (H : LevelRecursiveGuard D mode (Y.inst (proofErase Γ p)) (W.inst (proofErase Γ p)))
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ x) (proofErase Γ p))
    (RY : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ y) (proofErase Γ p))
    (RL : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (.app f x)) outL)
    (RR : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (.app g y)) outR) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) mode outL outR := by
  have JL := stage_zero_native_application_reference_join heq hs hl hcon hD hc hΓ hf hx hp RF RX RL
  have JR := stage_zero_native_application_reference_join heq hs hl hcon hD hc hΓ hg hy hp RG RY RR
  exact ((H.of_joins hs hl hcon (proofErase_level_core_confluent hs hl hcon hc) JL JR).scoped
    (fun H => .base (.inl H))).joint.computed

namespace EnvironmentCore

/-- Actual environment definitions discharge all compatibility and confluence
premises for transport through recursively compared native references. -/
theorem stage_zero_recursive_reference_outputs_compare
    (heq : env.HasCanonicalEq) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs Γ e A) (hf : env.HasType univs Γ f B)
    (RE : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage definitions 0) (proofEraseCtx Γ)
      (proofErase Γ e) referenceE)
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage definitions 0) (proofEraseCtx Γ)
      (proofErase Γ f) referenceF)
    (H : LevelRecursiveGuard definitions mode referenceE referenceF)
    (RL : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage definitions 0) (proofEraseCtx Γ)
      (proofErase Γ e) outL)
    (RR : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage definitions 0) (proofEraseCtx Γ)
      (proofErase Γ f) outR) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage definitions 0) (proofEraseCtx Γ) mode outL outR :=
  Strengthening.stage_zero_recursive_reference_outputs_compare heq sound (levelCompatible hcon) hcon
    no_rigid (typed_core_confluence hcon) hΓ he hf RE RF H RL RR

end EnvironmentCore
end Lean4Lean.VEnv.Strengthening
