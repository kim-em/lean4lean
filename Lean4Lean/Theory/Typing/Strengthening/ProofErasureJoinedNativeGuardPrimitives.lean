import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreExpansionRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJoinedNativeRecoveredTransport

/-! # First recovered singleton stage with common native images

Both general recovered-family singletons and specialized Eq prefixes preserve
exact substituted outputs. Their core guards need common native image carriers,
not exact assigned types. This is compatible with the identity-expansion boundary:
identity expansion is not a primitive of this first recovered stage.
-/
namespace Lean4Lean.VEnv.Strengthening.ErasedQuotCore.JoinedNative
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {hq : QuotRegistered env}

/-- General recovered-family singleton guards substitute under their complete
generated telescope using only joined native images. -/
theorem singleton_subst (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (HI : Images hq Γ Γ₀ τ)
    (ht : env.HasType univs Γ e T)
    (R : CarrierRecoveredSingletonPrimitive (fun _ => Step hq) (proofEraseCtx Γ) (proofErase Γ e) out) :
    CarrierRecoveredSingletonPrimitive (fun _ => Step hq) (proofEraseCtx Γ₀)
      ((proofErase Γ e).subst τ) (out.subst τ) := by
  have hstep : ErasedScopedPrimitiveDescent (fun _ => Step hq) :=
    ErasedPrimitiveReplay.toDescent (sound hq) (erased_iota_replay (sound hq))
  have WR : ImageSubstitution hq (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ :=
    ImageSubstitution.of_typed hΓ₀ W ES HI
  exact ⟨R.1.subst WR.interpretation,
    proofErase_recovered_singleton_guard_subst_between heq hstep hstep
      (recovered_guard_substitution hcon) hΓ₀ W ES WR ht R.2⟩

/-- The specialized Eq prefix preserves its exact substituted output with the
same joined-image constraint. No singleton encoding or registry equality is needed. -/
theorem prefix_subst (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (HI : Images hq Γ Γ₀ τ)
    (ht : env.HasType univs Γ e T)
    (R : ComputedJointPrefixPrimitive (fun _ => Step hq) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ComputedJointPrefixPrimitive (fun _ => Step hq) (proofEraseCtx Γ₀)
      ((proofErase Γ e).subst τ) (out.subst τ) :=
  proofErase_computed_prefix_guard_subst_between heq (recovered_guard_substitution hcon).toComputedGuardSubstitution
    W.wf (ImageSubstitution.of_typed hΓ₀ W ES HI) ht R

/-- Every first-stage root transports through joined native images. Core
primitives substitute syntactically; both recursive guard branches use the
proved checker transport rather than an exact recovery hypothesis. -/
theorem stage_one_primitive_subst (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (R : ErasedCarrierRecoveredStage (definitions hq) 1 Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (WR : ImageSubstitution hq Δ Δ' τ) :
    ErasedCarrierRecoveredStage (definitions hq) 1 Δ' (source.subst τ) (out.subst τ) := by
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, W, ES, HI⟩ := WR hΓ EΓ
  rcases R with R | R | R
  · exact .inl (erased_iota_primitive_subst R)
  · have H := singleton_subst heq hcon hΓ₀ W ES HI ht (by simpa only [ErasedCarrierRecoveredStage, EΓ, Ee] using R)
    exact .inr (.inl (by simpa only [ErasedCarrierRecoveredStage, EΓ₀, Ee] using H))
  · have H := prefix_subst heq hcon hΓ₀ W ES HI ht (by simpa only [ErasedCarrierRecoveredStage, EΓ, Ee] using R)
    exact .inr (.inr (by simpa only [ErasedCarrierRecoveredStage, EΓ₀, Ee] using H))

/-- Arbitrarily long first-stage computations substitute exactly through
joined images. This includes nested singleton/Eq-prefix contractions and all
compatible contexts, not just a single primitive or a fixed telescope. -/
theorem stage_one_compute_subst (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (R : ScopedCompute (ErasedCarrierRecoveredStage (definitions hq) 1) Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (WR : ImageSubstitution hq Δ Δ' τ) :
    ScopedCompute (ErasedCarrierRecoveredStage (definitions hq) 1) Δ' (source.subst τ) (out.subst τ) :=
  R.transport_typed (erased_carrier_recovered_stage_descent heq (sound hq) 1)
    (ImageSubstitution hq) (fun W => W.cons)
    (fun R hΓ ht EΓ Ee WR => .base (stage_one_primitive_subst heq hcon R hΓ ht EΓ Ee WR))
    hΓ ht EΓ Ee WR

/-- A retained argument may recover through mixed core/expansion computation
and meet its assigned type at a common carrier. It then instantiates arbitrary
first-stage body computations with their exact raw output. Exact native
recovery of the assigned type is unnecessary for these guarded primitives. -/
theorem stage_one_compute_inst_mixed (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hr : ErasedScopedPrimitiveDescent Recovery)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (RN : ScopedTypeRecovery (ErasedCoreExpansion (definitions hq) Recovery)
      (proofEraseCtx Γ) (proofErase Γ x) native)
    (HJ : ComputeJoin (Step hq) (proofErase Γ A) native)
    (RB : ScopedCompute (ErasedCarrierRecoveredStage (definitions hq) 1) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) out) :
    ScopedCompute (ErasedCarrierRecoveredStage (definitions hq) 1) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (out.inst (proofErase Γ x)) := by
  obtain ⟨native', RN', RC'⟩ := expansion_recovery_align hq hcon hr hΓA.1 hx RN HJ
  have HI : Images hq (A :: Γ) Γ (ProofShape.Subst.one (proofErase Γ x)) := Images.inst RN' RC'
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
  have ES : ErasedSubstAgreement (A :: Γ) Γ (VExpr.Subst.one x)
      (ProofShape.Subst.one (proofErase Γ x)) := erasedSubstAgreement_one hΓA hx
  have H := stage_one_compute_subst heq hcon RB hΓA hb rfl rfl
    (ImageSubstitution.of_typed hΓA.1 W ES HI)
  rw [← proofErase_subst_with hΓA.1 W hb ES] at H
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN, ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using H

/-- An entire first-stage body path and an arbitrary expanded argument path
have the exact instantiated output as a residual of the original beta
contractum. Only the original argument needs a common native carrier; its
computed endpoint needs no recovery certificate. -/
theorem stage_one_body_argument_square_mixed (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hr : ErasedScopedPrimitiveDescent Recovery)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (RN : ScopedTypeRecovery (ErasedCoreExpansion (definitions hq) Recovery)
      (proofEraseCtx Γ) (proofErase Γ x) native)
    (HJ : ComputeJoin (Step hq) (proofErase Γ A) native)
    (RB : ScopedCompute (ErasedCarrierRecoveredStage (definitions hq) 1) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) outB)
    (RX : ScopedCompute (ErasedExpansionUnion (definitions hq)) (proofEraseCtx Γ) (proofErase Γ x) outX) :
    ScopedCompute (ErasedExpansionUnion (definitions hq)) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (outB.inst outX) := by
  have R₁ := stage_one_compute_inst_mixed heq hcon hr hΓA hb hx RN HJ RB
  obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize
    (erased_carrier_recovered_stage_descent heq (sound hq) 1) hΓA hb rfl rfl RB
  obtain ⟨stage, RX⟩ := RX.finite_stage (Stages := ErasedExpansionStage (definitions hq))
    (fun {stage later} hle {Δ a b} H => erased_expansion_stage_mono hle H)
  have R₂ := proofErase_expansion_compute_inst_argument heq (sound hq) hΓA HB.hasType.2 hx RX
  rw [proofErase_instN hΓA hx Ctx.InstN.zero HB.hasType.2, EB] at R₂
  exact (R₁.mono (fun H => ⟨1, erased_level_into_expansion_stage 1 (erased_recovered_into_level_stage 1 H)⟩)).trans
    (R₂.mono (fun H => ⟨stage, H⟩))

end Lean4Lean.VEnv.Strengthening.ErasedQuotCore.JoinedNative
