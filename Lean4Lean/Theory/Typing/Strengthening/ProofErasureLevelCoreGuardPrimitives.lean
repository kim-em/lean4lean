import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelCoreRecoveredTransport

/-! # First universe-extended recovered singleton stage with common native images

Both general recovered-family singletons and specialized Eq prefixes preserve
exact substituted outputs. Their level-core guards need common native image carriers,
not exact assigned types. This is compatible with the identity-expansion boundary:
identity expansion is not a primitive of this first level-recovered stage.
Native images may nevertheless be recovered through mixed controlled expansion.
-/
namespace Lean4Lean.VEnv.Strengthening.LevelCoreNative
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {Defs : Definitions}

/-- General recovered-family singleton guards substitute under their complete
generated telescope using only joined native images. -/
theorem singleton_subst (heq : env.HasCanonicalEq)
    (hs : Defs.Sound env univs) (hlevels : Defs.LevelCompatible univs)
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ Defs.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive Defs))
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (HI : Images Defs Γ Γ₀ τ)
    (ht : env.HasType univs Γ e T)
    (R : CarrierRecoveredSingletonPrimitive (fun _ => ErasedLevelCore Defs) (proofEraseCtx Γ) (proofErase Γ e) out) :
    CarrierRecoveredSingletonPrimitive (fun _ => ErasedLevelCore Defs) (proofEraseCtx Γ₀)
      ((proofErase Γ e).subst τ) (out.subst τ) := by
  have hstep : ErasedScopedPrimitiveDescent (fun _ => ErasedLevelCore Defs) :=
    erased_level_core_descent hs
  have WR : ImageSubstitution Defs (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ :=
    ImageSubstitution.of_typed hΓ₀ W ES HI
  exact ⟨R.1.subst WR.interpretation,
    proofErase_recovered_singleton_guard_subst_between heq hstep hstep
      (recovered_guard_substitution hs hlevels hRigid hc hcon) hΓ₀ W ES WR ht R.2⟩

/-- The specialized Eq prefix preserves its exact substituted output with the
same joined-image constraint. No singleton encoding or registry equality is needed. -/
theorem prefix_subst (heq : env.HasCanonicalEq)
    (hs : Defs.Sound env univs) (hlevels : Defs.LevelCompatible univs)
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ Defs.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive Defs))
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (HI : Images Defs Γ Γ₀ τ)
    (ht : env.HasType univs Γ e T)
    (R : ComputedJointPrefixPrimitive (fun _ => ErasedLevelCore Defs) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ComputedJointPrefixPrimitive (fun _ => ErasedLevelCore Defs) (proofEraseCtx Γ₀)
      ((proofErase Γ e).subst τ) (out.subst τ) :=
  proofErase_computed_prefix_guard_subst_between heq (recovered_guard_substitution hs hlevels hRigid hc hcon).toComputedGuardSubstitution
    W.wf (ImageSubstitution.of_typed hΓ₀ W ES HI) ht R

/-- Every first-stage root transports through joined native images. Core
primitives substitute syntactically; both recursive guard branches use the
proved checker transport rather than an exact recovery hypothesis. -/
theorem stage_one_primitive_subst (heq : env.HasCanonicalEq)
    (hs : Defs.Sound env univs) (hlevels : Defs.LevelCompatible univs)
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ Defs.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive Defs))
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (R : ErasedLevelRecoveredStage Defs 1 Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (WR : ImageSubstitution Defs Δ Δ' τ) :
    ErasedLevelRecoveredStage Defs 1 Δ' (source.subst τ) (out.subst τ) := by
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, W, ES, HI⟩ := WR hΓ EΓ
  rcases R with R | R | R
  · exact .inl (erased_level_core_subst R)
  · have H := singleton_subst heq hs hlevels hRigid hc hcon hΓ₀ W ES HI ht (by simpa only [ErasedLevelRecoveredStage, EΓ, Ee] using R)
    exact .inr (.inl (by simpa only [ErasedLevelRecoveredStage, EΓ₀, Ee] using H))
  · have H := prefix_subst heq hs hlevels hRigid hc hcon hΓ₀ W ES HI ht (by simpa only [ErasedLevelRecoveredStage, EΓ, Ee] using R)
    exact .inr (.inr (by simpa only [ErasedLevelRecoveredStage, EΓ₀, Ee] using H))

/-- Arbitrarily long first-stage computations substitute exactly through
joined images. This includes nested singleton/Eq-prefix contractions and all
compatible contexts, not just a single primitive or a fixed telescope. -/
theorem stage_one_compute_subst (heq : env.HasCanonicalEq)
    (hs : Defs.Sound env univs) (hlevels : Defs.LevelCompatible univs)
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ Defs.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive Defs))
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (R : ScopedCompute (ErasedLevelRecoveredStage Defs 1) Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (WR : ImageSubstitution Defs Δ Δ' τ) :
    ScopedCompute (ErasedLevelRecoveredStage Defs 1) Δ' (source.subst τ) (out.subst τ) :=
  R.transport_typed (erased_level_recovered_stage_descent heq hs 1)
    (ImageSubstitution Defs) (fun W => W.cons)
    (fun R hΓ ht EΓ Ee WR => .base (stage_one_primitive_subst heq hs hlevels hRigid hc hcon R hΓ ht EΓ Ee WR))
    hΓ ht EΓ Ee WR

/-- A retained argument may recover through mixed core/expansion computation
and meet its assigned type at a common carrier. It then instantiates arbitrary
first-stage body computations with their exact raw output. Exact native
recovery of the assigned type is unnecessary for these guarded primitives. -/
theorem stage_one_compute_inst_mixed (heq : env.HasCanonicalEq)
    (hs : Defs.Sound env univs) (hlevels : Defs.LevelCompatible univs)
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ Defs.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive Defs))
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hr : ErasedScopedPrimitiveDescent Recovery)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (RN : ScopedTypeRecovery (ErasedLevelCoreExpansion Defs Recovery)
      (proofEraseCtx Γ) (proofErase Γ x) native)
    (HJ : ComputeJoin (ErasedLevelCore Defs) (proofErase Γ A) native)
    (RB : ScopedCompute (ErasedLevelRecoveredStage Defs 1) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) out) :
    ScopedCompute (ErasedLevelRecoveredStage Defs 1) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (out.inst (proofErase Γ x)) := by
  obtain ⟨native', RN', RC'⟩ := expansion_recovery_align hs hlevels hcon hRigid hc hr hΓA.1 hx RN HJ
  have HI : Images Defs (A :: Γ) Γ (ProofShape.Subst.one (proofErase Γ x)) := Images.inst RN' RC'
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
  have ES : ErasedSubstAgreement (A :: Γ) Γ (VExpr.Subst.one x)
      (ProofShape.Subst.one (proofErase Γ x)) := erasedSubstAgreement_one hΓA hx
  have H := stage_one_compute_subst heq hs hlevels hRigid hc hcon RB hΓA hb rfl rfl
    (ImageSubstitution.of_typed hΓA.1 W ES HI)
  rw [← proofErase_subst_with hΓA.1 W hb ES] at H
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN, ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using H

/-- An entire first-stage body path and an arbitrary expanded argument path
have the exact instantiated output as a residual of the original beta
contractum. Only the original argument needs a common native carrier; its
computed endpoint needs no recovery certificate. -/
theorem stage_one_body_argument_square_mixed (heq : env.HasCanonicalEq)
    (hs : Defs.Sound env univs) (hlevels : Defs.LevelCompatible univs)
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ Defs.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive Defs))
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hr : ErasedScopedPrimitiveDescent Recovery)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (RN : ScopedTypeRecovery (ErasedLevelCoreExpansion Defs Recovery)
      (proofEraseCtx Γ) (proofErase Γ x) native)
    (HJ : ComputeJoin (ErasedLevelCore Defs) (proofErase Γ A) native)
    (RB : ScopedCompute (ErasedLevelRecoveredStage Defs 1) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) outB)
    (RX : ScopedCompute (ErasedExpansionUnion Defs) (proofEraseCtx Γ) (proofErase Γ x) outX) :
    ScopedCompute (ErasedExpansionUnion Defs) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (outB.inst outX) := by
  have R₁ := stage_one_compute_inst_mixed heq hs hlevels hRigid hc hcon hr hΓA hb hx RN HJ RB
  obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize
    (erased_level_recovered_stage_descent heq hs 1) hΓA hb rfl rfl RB
  obtain ⟨stage, RX⟩ := RX.finite_stage (Stages := ErasedExpansionStage Defs)
    (fun {stage later} hle {Δ a b} H => erased_expansion_stage_mono hle H)
  have R₂ := proofErase_expansion_compute_inst_argument heq hs hΓA HB.hasType.2 hx RX
  rw [proofErase_instN hΓA hx Ctx.InstN.zero HB.hasType.2, EB] at R₂
  exact (R₁.mono (fun H => ⟨1, erased_level_into_expansion_stage 1 H⟩)).trans
    (R₂.mono (fun H => ⟨stage, H⟩))

end Lean4Lean.VEnv.Strengthening.LevelCoreNative

namespace Lean4Lean.VEnv.Strengthening.StoredCore
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- Actual stored definitions discharge all confluence, rigidity, soundness,
and universe-compatibility premises. A mixed native output joined to its assigned
carrier suffices for the entire first universe-extended singleton stage. -/
theorem level_stage_one_inst_mixed (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (RN : ScopedTypeRecovery (ErasedLevelCoreExpansion (Definitions.ofEnv env univs henv)
        (ErasedExpansionUnion (Definitions.ofEnv env univs henv)))
      (proofEraseCtx Γ) (proofErase Γ x) native)
    (HJ : ComputeJoin (ErasedLevelCore (Definitions.ofEnv env univs henv)) (proofErase Γ A) native)
    (RB : ScopedCompute (ErasedLevelRecoveredStage (Definitions.ofEnv env univs henv) 1)
      (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b) out) :
    ScopedCompute (ErasedLevelRecoveredStage (Definitions.ofEnv env univs henv) 1)
      (proofEraseCtx Γ) (proofErase Γ (b.inst x)) (out.inst (proofErase Γ x)) :=
  LevelCoreNative.stage_one_compute_inst_mixed heq (Definitions.ofEnv_sound henv)
    (Definitions.ofEnv_levelCompatible henv) (fun hr _ _ => Definitions.ofEnv_no_rigid henv hr)
    (typed_core_confluence hcon) hcon
    (erased_expansion_union_descent heq (Definitions.ofEnv_sound henv)) hΓA hb hx RN HJ RB

end Lean4Lean.VEnv.Strengthening.StoredCore
