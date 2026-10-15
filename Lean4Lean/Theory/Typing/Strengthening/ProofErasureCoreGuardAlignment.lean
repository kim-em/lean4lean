import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreCheckReduction

/-! # General carrier alignment by repaired-core computation

The simultaneous transport theorem gives forward carrier reduction, alignment
at computationally joined carriers, and joint Pi/argument-guard re-synthesis
under computed context oracles. No arbitrary substitution theorem is asserted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]
namespace ErasedQuotCore

/-- Every well-formed original context supplies the reflexive oracle reduction. -/
theorem ContextReduction.refl (hq : QuotRegistered env) (hΓ : OnCtx Γ (env.IsType univs)) :
    ContextReduction hq (proofEraseCtx Γ) (proofEraseCtx Γ) :=
  .of_defeqCtx hq hΓ hΓ (.refl hΓ) (fun _ => .refl)

/-- Both comparison modes transport along actual context conversion when the
old oracle entries compute to the new ones. Endpoint erasures are expressed in
the actual target context. -/
theorem compare_context_reduce
    (hq : QuotRegistered env) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : ∀ i, Compute (Step hq) (contextOracle (proofEraseCtx Γ) i)
      (contextOracle (proofEraseCtx Γ') i))
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b T)
    (H : JointCompare (fun _ => Step hq) (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b)) :
    JointCompare (fun _ => Step hq) (proofEraseCtx Γ') mode (proofErase Γ' a) (proofErase Γ' b) := by
  have H' := H.quot_core_reduce_typed hq hcon hΓ ha hb rfl rfl rfl
    (ContextReduction.of_defeqCtx hq hΓ hΓ' W HO)
  rwa [proofErase_defeqCtx hΓ W ha, proofErase_defeqCtx hΓ W hb] at H'

/-- Every typed joint carrier guard survives forward ordinary-core computation
of its carrier, with no structural-subsingleton restriction. -/
theorem carrier_compute_forward
    (hq : QuotRegistered env) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b T)
    (H : JointCarrierGuard (fun _ => Step hq) (proofEraseCtx Γ)
      (proofErase Γ T) (proofErase Γ a) (proofErase Γ b))
    (R : Compute (Step hq) (proofErase Γ T) target) :
    JointCarrierGuard (fun _ => Step hq) (proofEraseCtx Γ) target (proofErase Γ a) (proofErase Γ b) :=
  H.quot_core_reduce_typed hq hcon hΓ ha hb rfl rfl rfl rfl (ContextReduction.refl hq hΓ) R

/-- A guard at a typed carrier transfers to any raw carrier computing to a
common reduct. This is general joint-guard alignment, including dependent
structure fields and function carriers; sound use still types the endpoints
at the target carrier. -/
theorem carrier_join_target
    (hq : QuotRegistered env) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b T)
    (H : JointCarrierGuard (fun _ => Step hq) (proofEraseCtx Γ)
      (proofErase Γ T) (proofErase Γ a) (proofErase Γ b))
    (RA : Compute (Step hq) (proofErase Γ T) shared)
    (RB : Compute (Step hq) target shared) :
    JointCarrierGuard (fun _ => Step hq) (proofEraseCtx Γ) target (proofErase Γ a) (proofErase Γ b) :=
  .carrierCompute (RB.scoped (fun H => .base H)) (carrier_compute_forward hq hcon hΓ ha hb H RA)

/-- Computational oracle reduction chooses a new recovered Pi and transports
an arbitrary typed joint argument guard to its new domain. This removes the
subsingleton restriction for this context-transport problem, without claiming
arbitrary non-proof substitution or guarded-stage re-synthesis. -/
theorem recovery_guard_oracle_reduce
    (hq : QuotRegistered env) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE D C))
    (hx : env.HasType univs Γ x D) (hy : env.HasType univs Γ y D)
    (W : ContextReduction hq (proofEraseCtx Γ) Δ')
    (R : ScopedTypeRecovery (fun _ => Step hq) (proofEraseCtx Γ) (proofErase Γ f) (.forallE A B))
    (HX : JointCarrierGuard (fun _ => Step hq) (proofEraseCtx Γ) A (proofErase Γ x) (proofErase Γ y)) :
    ∃ A' B', ScopedTypeRecovery (fun _ => Step hq) Δ' (proofErase Γ f) (.forallE A' B') ∧
      JointCarrierGuard (fun _ => Step hq) Δ' A' (proofErase Γ x) (proofErase Γ y) := by
  let hstep : ErasedScopedPrimitiveDescent (fun _ => Step hq) :=
    ErasedPrimitiveReplay.toDescent (sound hq) (erased_iota_replay (sound hq))
  obtain ⟨D₀, C₀, hfPi, ED, _⟩ := proofErase_scoped_recovered_pi_descend hstep hΓ hΓ
    (show Ctx.LiftN 0 0 Γ Γ from .zero []) hf (by simpa only [ProofShape.liftN_zero] using R)
  have hxD := argument_at_displayed_domain hΓ hf hfPi hx
  have hyD := argument_at_displayed_domain hΓ hf hfPi hy
  obtain ⟨A', B', HR, HA, _⟩ := recovery_pi_oracle_reduce hq hcon hΓ hf W.lookup R
  exact ⟨A', B', HR, HX.quot_core_reduce_typed hq hcon hΓ hxD hyD rfl
    (by simpa only [ProofShape.liftN_zero] using ED) rfl rfl W HA⟩

end ErasedQuotCore
end Lean4Lean.VEnv.Strengthening
