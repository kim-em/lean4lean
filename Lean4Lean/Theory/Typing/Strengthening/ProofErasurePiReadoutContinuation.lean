import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionBackwardContext

/-! # Continuing dependent component computation after a binder changes

A later codomain path runs under the newly selected domain. Exact native
identity images pull it back, so it composes with the original codomain path.
This closes the literal-Pi continuation case of retaining a marked Pi origin.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Two phases of dependent component computation retain a Pi readout in the
original scope, even when the second codomain path runs under the changed
domain. No domain purity, shape restriction or new native-coverage premise is
used. The stage bound accounts for backward context transport. -/
theorem proofErase_pi_readout_continue_components
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAX : env.IsDefEq univs Γ A X (.sort u))
    (hY : env.HasType univs (X :: Γ) Y T)
    (RA : ScopedCompute (ErasedExpansionStage D k) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ X))
    (RB : ScopedCompute (ErasedExpansionStage D r) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) B) (proofErase (A :: Γ) Y))
    (RX : ScopedCompute (ErasedExpansionStage D m) (proofEraseCtx Γ)
      (proofErase Γ X) outX)
    (RY : ScopedCompute (ErasedExpansionStage D n) (proofEraseCtx (X :: Γ))
      (proofErase (X :: Γ) Y) outY) :
    PiReadout (ErasedExpansionStage D (max (max k m) (max r (n + k))))
      (proofEraseCtx Γ) (proofErase Γ A) (proofErase (A :: Γ) B) (.forallE outX outY) := by
  have RY' := proofErase_expansion_compute_backward_context heq hs hΓ HAX RA hY RY
  apply PiReadout.parts
  · exact (RA.mono (fun H => erased_expansion_stage_mono (by omega) H)).trans
      (RX.mono (fun H => erased_expansion_stage_mono (by omega) H))
  · exact (RB.mono (fun H => erased_expansion_stage_mono (by omega) H)).trans
      (RY'.mono (fun H => erased_expansion_stage_mono (by omega) H))

/-- The continued Pi may then pass through arbitrarily many expanded root
steps and compatible beta reductions. The component bound stays unchanged,
regardless of guard depths used by those outer-root steps. -/
theorem proofErase_pi_readout_continue_root_path
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAX : env.IsDefEq univs Γ A X (.sort u))
    (hY : env.HasType univs (X :: Γ) Y T)
    (RA : ScopedCompute (ErasedExpansionStage D k) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ X))
    (RB : ScopedCompute (ErasedExpansionStage D r) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) B) (proofErase (A :: Γ) Y))
    (RX : ScopedCompute (ErasedExpansionStage D m) (proofEraseCtx Γ)
      (proofErase Γ X) outX)
    (RY : ScopedCompute (ErasedExpansionStage D n) (proofEraseCtx (X :: Γ))
      (proofErase (X :: Γ) Y) outY)
    (R : ReflTransGen (fun a b => ErasedExpansionUnion D Δroot a b ∨ ProofShape.BetaRed a b)
      (.forallE outX outY) out) :
    PiReadout (ErasedExpansionStage D (max (max k m) (max r (n + k))))
      (proofEraseCtx Γ) (proofErase Γ A) (proofErase (A :: Γ) B) out :=
  piReadout_root_beta_path
    (proofErase_pi_readout_continue_components heq hs hΓ HAX hY RA RB RX RY) R

end Lean4Lean.VEnv.Strengthening
