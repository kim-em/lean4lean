import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralFunctionCarrierConversion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructuralDomainBoundary

/-! # Application repair beyond the three-way domain recovery boundary

The assigned Pi carrier is transported to the lambda's written Pi carrier.
Neither exact assigned-domain exposure nor carrier inertness is required.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private context native assigned nativeRaw assignedRaw context_wf
  types_equal erasures
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary
variable [Params]

/-- The whole argument guard may change a neutral domain inside a dependent
function carrier before applying the existing computed-lambda rule. Its
codomain remains the original raw codomain, with all computation retained. -/
theorem proofErase_computed_joint_application_dependent_domain_convert
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HA : AnchoredCarrier 0 (proofErase Γ A))
    (hx : env.HasType univs Γ x (.forallE A C))
    (hy : env.HasType univs Γ y (.forallE A C))
    (HX : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) C)) (proofErase Γ x) (proofErase Γ y))
    (RF : ScopedCompute (ErasedJointStage D 0) (proofEraseCtx Γ) f
      (.lam (.forallE (proofErase Γ B) (proofErase (A :: Γ) C)) body))
    (HF : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) false f g) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (.app f (proofErase Γ x)) (.app g (proofErase Γ y)) :=
  .appComputed RF HF
    (proofErase_computed_joint_dependent_neutral_function_carrier_convert hs hΓ HAB HA hx hy HX)

/-- A computed lambda may use its written function carrier after converting
an entire guard from an equal neutral-domain function carrier. This produces
an existing application certificate, with no target argument guard premise. -/
theorem proofErase_computed_joint_application_function_domain_convert
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HA : AnchoredCarrier 0 (proofErase Γ A))
    (hx : env.HasType univs Γ x (.forallE A (.sort v)))
    (hy : env.HasType univs Γ y (.forallE A (.sort v)))
    (HX : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (.sort v)) (proofErase Γ x) (proofErase Γ y))
    (RF : ScopedCompute (ErasedJointStage D 0) (proofEraseCtx Γ) f
      (.lam (.forallE (proofErase Γ B) (.sort v)) body))
    (HF : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) false f g) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (.app f (proofErase Γ x)) (.app g (proofErase Γ y)) :=
  .appComputed RF HF (proofErase_computed_joint_neutral_function_carrier_convert hs hΓ HAB HA hx hy HX)

/-- The exact Pi-wrapped eta boundary admits application comparison after
whole-guard conversion to its written domain. Its native recovery at the
assigned type, exact assigned-domain exposure, and inertness failures remain
valid. This is an application repair, not arbitrary body substitution. -/
theorem proofErase_structural_eta_application_repair
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs (context Γ) x (.forallE assigned (.sort .zero)))
    (hy : env.HasType univs (context Γ) y (.forallE assigned (.sort .zero)))
    (HX : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (context Γ))
      (.forallE assignedRaw (.sort .zero)) (proofErase (context Γ) x) (proofErase (context Γ) y)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (context Γ)) mode
      (.app (.lam (.forallE nativeRaw (.sort .zero)) (.sort .zero)) (proofErase (context Γ) x))
      (.app (.lam (.forallE nativeRaw (.sort .zero)) (.sort .zero)) (proofErase (context Γ) y)) := by
  have HA : AnchoredCarrier 0 (proofErase (context Γ) assigned) := by
    rw [(erasures hΓ).2]
    exact ⟨1, [_], by omega, rfl⟩
  have HC := proofErase_computed_joint_neutral_function_carrier_convert hs (context_wf hΓ)
    types_equal HA hx hy (by simpa only [(erasures hΓ).2] using HX)
  rw [(erasures hΓ).1] at HC
  exact .appComputed .refl (.leaf .refl) HC

end Lean4Lean.VEnv.Strengthening
