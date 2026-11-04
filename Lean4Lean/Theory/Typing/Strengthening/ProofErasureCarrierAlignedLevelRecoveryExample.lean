import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedLevelStages
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveryJoinBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedNormalSyntax

/-! # A literal common native carrier created by universe conversion

Even two sorts with equivalent levels have no common native output in the old
recovered union: their distinct successor-sort outputs are fixed. The new base
repairs this precise failure using one proved universe-conversion step.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape PureObservation
variable [Params]

/-- Equivalent but syntactically different sorts cannot share an old native
recovery output, while one explicit universe step gives an exact common output
in the new base and licenses the original recovered-carrier constructor. -/
theorem carrier_aligned_level_recovery_repairs_literal_output :
    (¬ ∃ out,
      ScopedTypeRecovery (ErasedCarrierRecoveredUnion D) Δ (.sort (.max .zero .zero)) out ∧
      ScopedTypeRecovery (ErasedCarrierRecoveredUnion D) Δ (.sort .zero) out) ∧
    (∃ out,
      ScopedTypeRecovery (fun _ => ErasedLevelCore D) Δ (.sort (.max .zero .zero)) out ∧
      ScopedTypeRecovery (fun _ => ErasedLevelCore D) Δ (.sort .zero) out) ∧
    CarrierRecoveredCompare (fun _ => ErasedLevelCore D) Δ false
      (.sort (.max .zero .zero)) (.sort .zero) := by
  have HL : VLevel.max .zero .zero ≈ .zero := by rfl
  have normal (u : VLevel) : ScopedNormalSyntax (ErasedCarrierRecoveredUnion D) Δ (.sort u) :=
    ⟨fun _ H => erased_carrier_recovered_union_head H, trivial⟩
  have RA : ScopedTypeRecovery (fun _ => ErasedLevelCore D) Δ (.sort (.max .zero .zero)) (.sort (.succ .zero)) :=
    (ScopedTypeRecovery.sort (by trivial)).convert (.base (.inr (.sort (VLevel.succ_congr HL) (by trivial))))
  have RB : ScopedTypeRecovery (fun _ => ErasedLevelCore D) Δ (.sort .zero) (.sort (.succ .zero)) :=
    .sort (by trivial)
  refine ⟨?_, ⟨_, RA, RB⟩, .recovered RA RB (.carrierChecked (.leaf (.sort HL)))⟩
  rintro ⟨out, H₁, H₂⟩
  have E₁ := H₁.sort_compute.fixed_of_scoped_normal (normal _)
  have E₂ := H₂.sort_compute.fixed_of_scoped_normal (normal _)
  cases E₁.symm.trans E₂

end Lean4Lean.VEnv.Strengthening
