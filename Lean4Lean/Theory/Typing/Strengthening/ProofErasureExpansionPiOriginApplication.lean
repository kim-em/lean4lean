import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionPiOrigin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiReadoutApplication

/-! # Native application after arbitrary expanded Pi-type computation

The full origin theorem discharges the readout hypothesis. Existing native
function evidence can be reselected at a Pi with both inferred component
comparisons. Guarded result transport uses recovery at the original argument
type, independently of the selected function domain.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- A path from the assigned Pi to an existing native output gives inferred
comparisons of both selected components. No purity or readout premise remains,
and the native recovery relation itself is unchanged. -/
theorem proofErase_native_pi_expansion_path
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hstep : ErasedScopedPrimitiveDescent Recovery)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f (.forallE A B))
    (RN : ScopedTypeRecovery Recovery (proofEraseCtx Γ) (proofErase Γ f) out)
    (RT : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) out) :
    ∃ X Y, env.HasType univs Γ f (.forallE X Y) ∧
      ScopedTypeRecovery Recovery (proofEraseCtx Γ) (proofErase Γ f)
        (.forallE (proofErase Γ X) (proofErase (X :: Γ) Y)) ∧
      ComputedJointCompare (ErasedExpansionUnion D) (proofEraseCtx Γ) false
        (proofErase Γ A) (proofErase Γ X) ∧
      ComputedJointCompare (ErasedExpansionUnion D) (proofEraseCtx (A :: Γ)) false
        (proofErase (A :: Γ) B) (proofErase (A :: Γ) Y) := by
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨u, hA⟩, v, hB⟩ := hPi.forallE_inv henv
  exact proofErase_native_pi_readout_comparisons hstep hΓ hf RN
    (proofErase_expansion_union_pi_readout heq hs hΓ hA hB RT)

/-- Every expanded assigned-type path supports native application and a
computed assigned-result carrier. Only the original argument needs recovery
at its assigned A; neither recovery at the selected domain nor recovery of a
computed argument is assumed. The selected application keeps Recovery. -/
theorem proofErase_native_application_expansion_type_path
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hstep : ErasedScopedPrimitiveDescent Recovery)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.app f x))
    (RX : ScopedTypeRecovery (ErasedExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) (proofErase Γ A))
    (RN : ScopedTypeRecovery Recovery (proofEraseCtx Γ) (proofErase Γ f) out)
    (RT : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) out) :
    ∃ C : VExpr, env.HasType univs Γ (.app f x) (C.inst x) ∧
      ScopedTypeRecovery Recovery (proofEraseCtx Γ) (proofErase Γ (.app f x))
        (proofErase Γ (C.inst x)) ∧
      ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (B.inst x)) (proofErase Γ (C.inst x)) := by
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨u, hA⟩, v, hB⟩ := hPi.forallE_inv henv
  obtain ⟨X, C, hfXC, RPi, _, ⟨_, HBC⟩, _, RC⟩ := proofErase_native_pi_readout hstep hΓ hf RN
    (proofErase_expansion_union_pi_readout heq hs hΓ hA hB RT)
  obtain ⟨ht, Rapp⟩ := proofErase_native_application_selected_pi hΓ hf hfXC hx hn RPi
  obtain ⟨k, RX⟩ := RX.finite_stage (Stages := ErasedExpansionStage D)
    (fun {stage later} hle {Δ a b} H => erased_expansion_stage_mono hle H)
  obtain ⟨n, RC⟩ := RC.finite_stage (Stages := ErasedExpansionStage D)
    (fun {stage later} hle {Δ a b} H => erased_expansion_stage_mono hle H)
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have RI := ExpansionNativeSubstitution.compute_inst heq hs hΓ hx RX HBC.hasType.1 RC
  rw [← proofErase_instN hΓA hx Ctx.InstN.zero HBC.hasType.2] at RI
  exact ⟨C, ht, Rapp, RI.mono (fun H => ⟨n+k, H⟩)⟩

end Lean4Lean.VEnv.Strengthening
