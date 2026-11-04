import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelNativeVariants
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeInputConvertedExample
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTerminalDomainExample

/-! # Converted inputs now instantiate every guarded layer

These actual typed lambdas have no exact assigned recovery in the old computed
union. Explicit universe conversion supplies stage-zero recovery in the new
system, hence all-stage substitution without stage growth for these images.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions} {n : Nat}

namespace TypeInputConvertedExample
open private erasures from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeInputConvertedExample
open private declared declared_equiv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveryJoinBoundary

/-- The previously obstructed literal universe input has exact native recovery
at its assigned type after adding only explicit universe conversion. -/
theorem level_recovery (hΓ : OnCtx Γ (env.IsType univs)) :
    ScopedTypeRecovery (ErasedLevelRecoveredStage D 0) (proofEraseCtx Γ)
      (proofErase Γ image) (proofErase Γ assigned) := by
  apply LevelNativeSubstitution.recovery_variant hΓ image_typed
    (out := .forallE (.sort (.succ .zero)) (.sort (.succ .zero)))
  · rw [(erasures hΓ).1]
    exact .lam (.sort (by trivial))
  · rw [(erasures hΓ).2]
    exact .forallE (.sort declared_equiv.symm) .refl

/-- The old recovery obstruction and the new certificate hold simultaneously. -/
theorem level_repair (hΓ : OnCtx Γ (env.IsType univs)) :
    (¬ ScopedTypeRecovery (ErasedComputedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ image) (proofErase Γ assigned)) ∧
    ScopedTypeRecovery (ErasedLevelRecoveredStage D 0) (proofEraseCtx Γ)
      (proofErase Γ image) (proofErase Γ assigned) :=
  ⟨(assigned_recovery_failure D hΓ).2, level_recovery hΓ⟩

/-- This converted image preserves arbitrary finite guarded computation in
the extended system, at the unchanged source stage. -/
theorem level_compute_inst (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs (assigned :: Γ) e T)
    (R : ScopedCompute (ErasedLevelRecoveredStage D n) (proofEraseCtx (assigned :: Γ))
      (proofErase (assigned :: Γ) e) out) :
    ScopedCompute (ErasedLevelRecoveredStage D n) (proofEraseCtx Γ)
      (proofErase Γ (e.inst image)) (out.inst (proofErase Γ image)) := by
  simpa only [Nat.add_zero] using
    LevelNativeSubstitution.compute_inst heq hs hΓ image_typed (level_recovery hΓ) ht R

end TypeInputConvertedExample

namespace TerminalDomainExample
open private erasures from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTerminalDomainExample

/-- The higher-order converted input also has exact assigned native recovery
using universe conversion inside its nested Pi domain. -/
theorem level_recovery (hΓ : OnCtx Γ (env.IsType univs)) :
    ScopedTypeRecovery (ErasedLevelRecoveredStage D 0) (proofEraseCtx Γ)
      (proofErase Γ image) (proofErase Γ assigned) := by
  apply LevelNativeSubstitution.recovery_variant hΓ image_typed
    (out := .forallE (.forallE (.sort (.succ .zero)) (.sort .zero)) (.sort (.succ .zero)))
  · rw [(erasures hΓ).1]
    exact .lam (.sort (by trivial))
  · rw [(erasures hΓ).2]
    exact .forallE (.forallE (.sort VLevel.imax_self.symm) .refl) .refl

/-- This is a strict repair of the old exact-recovery obstruction. -/
theorem level_repair (hΓ : OnCtx Γ (env.IsType univs)) :
    (¬ ScopedTypeRecovery (ErasedComputedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ image) (proofErase Γ assigned)) ∧
    ScopedTypeRecovery (ErasedLevelRecoveredStage D 0) (proofEraseCtx Γ)
      (proofErase Γ image) (proofErase Γ assigned) :=
  ⟨assigned_recovery_failure D hΓ, level_recovery hΓ⟩

/-- Higher-order universe-converted inputs instantiate every guarded layer
at its original bound, including recovered singleton-family guards. -/
theorem level_compute_inst (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs (assigned :: Γ) e T)
    (R : ScopedCompute (ErasedLevelRecoveredStage D n) (proofEraseCtx (assigned :: Γ))
      (proofErase (assigned :: Γ) e) out) :
    ScopedCompute (ErasedLevelRecoveredStage D n) (proofEraseCtx Γ)
      (proofErase Γ (e.inst image)) (out.inst (proofErase Γ image)) := by
  simpa only [Nat.add_zero] using
    LevelNativeSubstitution.compute_inst heq hs hΓ image_typed (level_recovery hΓ) ht R

end TerminalDomainExample
end Lean4Lean.VEnv.Strengthening
