import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiReadoutSelection
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionNativeInstantiation

/-! # Applying native functions after dependent Pi readout

Retained codomain computation is instantiated in the original binder scope.
The selected native function itself requires no native certificate for the
argument. Only transporting a guarded component path uses native-image evidence.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- If component primitives support typed substitution, Pi readout closes
native application with a computed assigned-result carrier. No native recovery
of the argument or purity condition is needed. Recovery and component relations
may differ. -/
theorem proofErase_native_application_pi_readout
    (hstep : ErasedScopedPrimitiveDescent Recovery)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.app f x))
    (R : ScopedTypeRecovery Recovery (proofEraseCtx Γ) (proofErase Γ f) out)
    (H : PiReadout Step (proofEraseCtx Γ) (proofErase Γ A) (proofErase (A :: Γ) B) out) :
    ∃ C : VExpr, env.HasType univs Γ (.app f x) (C.inst x) ∧
      ScopedTypeRecovery Recovery (proofEraseCtx Γ) (proofErase Γ (.app f x))
        (proofErase Γ (C.inst x)) ∧
      ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ (B.inst x)) (proofErase Γ (C.inst x)) := by
  obtain ⟨D, C, hfDC, RN, _, ⟨_, HBC⟩, _, RC⟩ := proofErase_native_pi_readout hstep hΓ hf R H
  obtain ⟨ht, RNapp⟩ := proofErase_native_application_selected_pi hΓ hf hfDC hx hn RN
  obtain ⟨u, hA⟩ := hx.isType henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
  refine ⟨C, ht, RNapp, ?_⟩
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN] using
    proofErase_scoped_compute_subst hsubst hΓ W HBC.hasType.1 HBC.hasType.2 RC

/-- Ordinary erased core components instantiate at every typed argument. The
native recovery relation can independently include controlled expansions. -/
theorem proofErase_native_application_core_pi_readout
    (hstep : ErasedScopedPrimitiveDescent Recovery)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.app f x))
    (R : ScopedTypeRecovery Recovery (proofEraseCtx Γ) (proofErase Γ f) out)
    (H : PiReadout (fun _ => ErasedIotaPrimitive D) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase (A :: Γ) B) out) :
    ∃ C : VExpr, env.HasType univs Γ (.app f x) (C.inst x) ∧
      ScopedTypeRecovery Recovery (proofEraseCtx Γ) (proofErase Γ (.app f x))
        (proofErase Γ (C.inst x)) ∧
      ScopedCompute (fun _ => ErasedIotaPrimitive D) (proofEraseCtx Γ)
        (proofErase Γ (B.inst x)) (proofErase Γ (C.inst x)) :=
  proofErase_native_application_pi_readout hstep (fun H _ => erased_iota_primitive_subst H)
    hΓ hf hx hn R H

/-- Guarded component computation instantiates using native evidence at the
original assigned argument type. Selection does not require recovery of that
argument at the newly exposed domain. The native function stage is unchanged;
only its component path uses the existing additive instantiation bound. -/
theorem proofErase_native_application_expansion_pi_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hstep : ErasedScopedPrimitiveDescent Recovery)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.app f x))
    (RX : ScopedTypeRecovery (ErasedExpansionStage D k) (proofEraseCtx Γ)
      (proofErase Γ x) (proofErase Γ A))
    (R : ScopedTypeRecovery Recovery (proofEraseCtx Γ) (proofErase Γ f) out)
    (H : PiReadout (ErasedExpansionStage D n) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase (A :: Γ) B) out) :
    ∃ C : VExpr, env.HasType univs Γ (.app f x) (C.inst x) ∧
      ScopedTypeRecovery Recovery (proofEraseCtx Γ) (proofErase Γ (.app f x))
        (proofErase Γ (C.inst x)) ∧
      ScopedCompute (ErasedExpansionStage D (n + k)) (proofEraseCtx Γ)
        (proofErase Γ (B.inst x)) (proofErase Γ (C.inst x)) := by
  obtain ⟨D', C, hfDC, RN, _, ⟨_, HBC⟩, _, RC⟩ := proofErase_native_pi_readout hstep hΓ hf R H
  obtain ⟨ht, RNapp⟩ := proofErase_native_application_selected_pi hΓ hf hfDC hx hn RN
  obtain ⟨u, hA⟩ := hx.isType henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have RC' := ExpansionNativeSubstitution.compute_inst heq hs hΓ hx RX HBC.hasType.1 RC
  rw [← proofErase_instN hΓA hx Ctx.InstN.zero HBC.hasType.2] at RC'
  exact ⟨C, ht, RNapp, RC'⟩

end Lean4Lean.VEnv.Strengthening
