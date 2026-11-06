import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFunctionHistory
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedComputedSpineExposure

/-! # Empty-structure carrier conversion from type comparison

Rigid-family exposure turns comparison with a parameterized empty structure
into a carrier guard at the other type. The root-preservation premise is proved
for the level-recovered stages. It is not assumed for the expanded Pi-inert
stages, which can wrap a constant head in a beta redex.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- A typed comparison with a parameterized empty structure suffices to guard
arbitrary endpoints at the compared type. Only family-head preservation is
needed of computation; no syntactic head is required of the target type. -/
theorem proofErase_compared_unit_carrier
    (hstep : ErasedScopedPrimitiveDescent Step) (hroot : SpineRootLevels Step family)
    (hi : env.projections family info) (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hp : ps.length = info.nparams) (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (VExpr.mkApps (.const family ls) ps) (.sort u))
    (hT : env.HasType univs Γ T (.sort v))
    (H : ComputedJointCompare Step (proofEraseCtx Γ) mode
      (proofErase Γ (VExpr.mkApps (.const family ls) ps)) (proofErase Γ T)) :
    ComputedJointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ T) a b := by
  have ES := proofErase_const_spine hΓ hS (not_isProof_of_sort hΓ hS)
  obtain ⟨ls', ps', R, _, hlen⟩ := proofErase_carrier_aligned_computed_family_exposure
    hstep hroot hΓ hS hT H ES
  apply ComputedJointCheck.carrierCompute R
  apply ComputedJointCheck.carrierSubsingleton
  exact .unit hi hx hf (hlen.trans ((List.length_map ..).trans hp))

/-- The non-expanding level-recovered computation embeds into the current
Pi-inert stage at the same bound, including all recursive singleton/Eq guards. -/
theorem erased_level_recovered_into_pi_inert
    (H : ErasedLevelRecoveredStage D n Δ a b) : PiInertStage D n Δ a b := by
  refine ⟨erased_eta_into_static_structure_eta_stage n
    (erased_expansion_into_eta_stage n (erased_level_into_expansion_stage n H)), ?_⟩
  rcases erased_level_recovered_stage_root n H with H | H
  · exact .inl H
  · cases H with
    | sort => exact .inr ⟨_, rfl⟩
    | const => exact .inl trivial

/-- Arbitrary finite non-expanding guards support empty-structure carrier
conversion at unchanged stage. Parameters and universes may vary, and the
target carrier need not be a literal family application. -/
theorem proofErase_level_compared_unit_carrier
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hp : ps.length = info.nparams) (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (VExpr.mkApps (.const family ls) ps) (.sort u))
    (hT : env.HasType univs Γ T (.sort v))
    (H : ComputedJointCompare (ErasedLevelRecoveredStage D n) (proofEraseCtx Γ) mode
      (proofErase Γ (VExpr.mkApps (.const family ls) ps)) (proofErase Γ T)) :
    ComputedJointCarrierGuard (PiInertStage D n) (proofEraseCtx Γ) (proofErase Γ T) a b :=
  (proofErase_compared_unit_carrier (erased_level_recovered_stage_descent heq hs n)
    (erased_level_recovered_stage_spine_levels heq (henv.projectionRigid hi) hD n)
    hi hx hf hp hΓ hS hT H).mono (fun R => erased_level_recovered_into_pi_inert R)

/-- The literal rigid-root condition cannot be used for general Pi-inert
conversion: even stage zero permits a constant beta wrapper. This refutes that
proposed proof premise, not exposure up to beta or carrier conversion itself. -/
theorem pi_inert_not_spine_root_levels (n : Nat) (family : Lean.Name) :
    ¬ SpineRootLevels (PiInertStage D n) family := by
  intro H
  have R : PiInertStage D 0 [] (.const family []) (constantExpansion (.const family [])) :=
    ⟨.inr (.intro (by intro E; cases E)), .inl trivial⟩
  obtain ⟨ls, E, _⟩ := H (args := []) (pi_inert_stage_mono (Nat.zero_le n) R)
  cases E

end Lean4Lean.VEnv.Strengthening
