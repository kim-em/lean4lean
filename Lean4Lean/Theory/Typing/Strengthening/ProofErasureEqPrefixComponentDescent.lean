import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertProbeGuardedCut
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureCertificateDescent

/-! # Eq-prefix readout from retained carrier and endpoint paths

The carrier need not remain a literal sort. Its computation and both endpoint
computations pull the observed guard back to the original three arguments.
Exact certificate descent then removes the inserted binders. This discharges
the direct Eq-prefix case once those three component origins are supplied;
it does not extract them from an arbitrary expanded whole-term path.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- A direct Eq prefix exposes its guard. Retained computation of all three
guard positions pulls it back without any head-preservation or typing premise. -/
theorem ProofShape.ComputedJointPrefixPrimitive.component_guard
    (H : ComputedJointPrefixPrimitive Step Δ (ProofShape.eqRecBeforeMajor v w α' a' M m b') out)
    (Rα : ScopedCompute Step Δ α α') (Ra : ScopedCompute Step Δ a a')
    (Rb : ScopedCompute Step Δ b b') : ComputedJointCarrierGuard Step Δ α a b := by
  cases H with
  | intro HG => exact .carrierCompute Rα (.carrierReduce Ra Rb HG)

/-- Three aligned component paths suffice to recover the exact lower carrier
certificate from an observed Eq-prefix step. Motive/minor origins are not needed
for this readout, and computation may change the carrier's syntactic head. -/
theorem proofErase_eq_prefix_component_certificate_descend
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Target)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ')
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (Rα : ScopedCompute Step (proofEraseCtx Γ') ((proofErase Γ A).liftN count offset) α')
    (Ra : ScopedCompute Step (proofEraseCtx Γ') ((proofErase Γ a).liftN count offset) a')
    (Rb : ScopedCompute Step (proofEraseCtx Γ') ((proofErase Γ b).liftN count offset) b')
    (H : ComputedJointPrefixPrimitive Step (proofEraseCtx Γ')
      (ProofShape.eqRecBeforeMajor v w α' a' M m b') out) :
    ComputedJointCarrierGuard Target (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ a) (proofErase Γ b) :=
  proofErase_computed_joint_carrier_certificate_descend hstep hΓ hΓ' W ha hb
    (H.component_guard Rα Ra Rb)

/-- Full expanded argument paths and an independently staged Eq guard retain
the lower certificate at their maximum stage. Universe changes, native eta,
structure eta and arbitrary guarded argument computations are admitted. -/
theorem static_eq_prefix_component_certificate_descend
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ')
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (Rα : ScopedCompute (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx Γ')
      ((proofErase Γ A).liftN count offset) α')
    (Ra : ScopedCompute (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx Γ')
      ((proofErase Γ a).liftN count offset) a')
    (Rb : ScopedCompute (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx Γ')
      ((proofErase Γ b).liftN count offset) b')
    (H : ComputedJointPrefixPrimitive (ErasedStaticStructureEtaExpansionStage D k) (proofEraseCtx Γ')
      (ProofShape.eqRecBeforeMajor v w α' a' M m b') out) :
    ComputedJointCarrierGuard (ErasedStaticStructureEtaExpansionStage D (max n k))
      (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ a) (proofErase Γ b) := by
  exact proofErase_eq_prefix_component_certificate_descend
    (erased_static_structure_eta_expansion_stage_certificate_descent heq hs (max n k)) hΓ hΓ' W ha hb
    (Rα.mono (fun H => erased_static_structure_eta_expansion_stage_mono (Nat.le_max_left n k) H))
    (Ra.mono (fun H => erased_static_structure_eta_expansion_stage_mono (Nat.le_max_left n k) H))
    (Rb.mono (fun H => erased_static_structure_eta_expansion_stage_mono (Nat.le_max_left n k) H))
    (H.mono (fun H => erased_static_structure_eta_expansion_stage_mono (Nat.le_max_right n k) H))

/-- In the Pi-inert cut, an earlier Eq-prefix guard and component origins at
the original stage yield the lower endpoint equation without raising that stage.
This is conditional on component ancestry, not a proof that every cut has it. -/
theorem pi_inert_eq_prefix_component_descend
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hk : k ≤ n)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ')
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (Rα : ScopedCompute (PiInertStage D n) (proofEraseCtx Γ')
      ((proofErase Γ A).liftN count offset) α')
    (Ra : ScopedCompute (PiInertStage D n) (proofEraseCtx Γ')
      ((proofErase Γ a).liftN count offset) a')
    (Rb : ScopedCompute (PiInertStage D n) (proofEraseCtx Γ')
      ((proofErase Γ b).liftN count offset) b')
    (H : ComputedJointPrefixPrimitive (ErasedStaticStructureEtaExpansionStage D k) (proofEraseCtx Γ')
      (ProofShape.eqRecBeforeMajor v w α' a' M m b') out) :
    ComputedJointCarrierGuard (ErasedStaticStructureEtaExpansionStage D n)
      (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ a) (proofErase Γ b) ∧
      env.IsDefEq univs Γ a b A := by
  have HG := static_eq_prefix_component_certificate_descend heq hs hΓ hΓ' W ha hb
    (Rα.mono (fun H => H.1)) (Ra.mono (fun H => H.1)) (Rb.mono (fun H => H.1)) H
  rw [Nat.max_eq_left hk] at HG
  exact ⟨HG, proofErase_computed_joint_carrier_reflect
    (erased_static_structure_eta_expansion_stage_descent heq hs n) hΓ ha hb HG⟩

end Lean4Lean.VEnv.Strengthening
