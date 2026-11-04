import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaLambdaReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelCoreNativeReduction
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaFunctionResidual

/-! # Core joins for eta before lambda-exposing head beta

Collapse the original native guard to core recovery. Syntactic Pi inversion
then tracks the selected domain through a finite nest of explicit lambda
applications. The existing typed eta residual restores the exposed body exactly,
including erased proof arguments. Argument native recovery is unnecessary.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- Eta on a beta-lambda readout remains core-joinable with its short source.
Guard paths may use any descending relation with typed level-core joins. The
readout can substitute arbitrary arguments through any finite nest of explicit
lambda applications; neither these arguments nor the exposed body require native
certificates. This does not cover arbitrary head beta that creates a lambda by
substituting into a variable or another neutral head. -/
theorem proofErase_native_eta_beta_lambda_core_join
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hD : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hstep : ErasedScopedPrimitiveDescent Recovery)
    (hjoin : ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute Recovery (proofEraseCtx Γ) (proofErase Γ e) out →
      ComputeJoin (ErasedLevelCore D) (proofErase Γ e) out)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (H : BetaLambdaReadout (proofErase Γ e) A b)
    (R : NativeEtaExpansion Recovery (proofEraseCtx Γ) (proofErase Γ e) expanded) :
    ComputeJoin (ErasedLevelCore D) (proofErase Γ e) expanded := by
  cases R with
  | intro RN SD =>
    obtain ⟨out', RN', RT⟩ := LevelCoreNative.recovery_of_compute_join
      hs hlevels hcon hD hc hstep hjoin RN hΓ he rfl rfl
    obtain ⟨X, Y, rfl, RX, _⟩ := (RT.mono (fun H => Or.inl H)).pi_parts
      (fun H => erased_level_core_no_pi H)
    obtain ⟨X', Y', E, RA⟩ := proofErase_beta_lambda_native_domain
      (fun H => erased_level_core_no_pi H) (fun H => erased_level_core_subst H) H RN'
    cases E
    have RL := proofErase_native_eta_function_lambda_residual
      (Source := fun _ => ErasedLevelCore D) (Target := fun _ => ErasedLevelCore D)
      hstep (erased_level_core_descent hs) (fun H _ => erased_level_core_subst H)
      hΓ he RN SD (ScopedCompute.beta H.beta_path)
    exact ⟨.lam X b, (Compute.beta H.beta_path).trans (.lam RA .refl),
      RL.core_forget.trans (.lam RX .refl)⟩

end Lean4Lean.VEnv.Strengthening
