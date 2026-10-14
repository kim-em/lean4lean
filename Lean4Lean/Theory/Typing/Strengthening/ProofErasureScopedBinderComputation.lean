import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedContextConversion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBinderComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitiveHeads

/-! # Inverting scoped computation beneath a changing lambda annotation

Only the initial annotation needs an original typing. Replay of each annotation
path reconstructs the context conversion that moves later body computation back
to the initial binder context. The raw body itself need not be realized.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

namespace ProofShape
/-- Finite lambda computation retains independent annotation and body paths.
The body path is indexed by the initial annotation, even when intermediate
annotations change. No original typing of the raw body is required. -/
theorem ScopedCompute.lam_inv_typed
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hroot : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hΔ : proofEraseCtx Γ = Δ)
    (R : ScopedCompute Step Δ (.lam (proofErase Γ A) body) out) :
    ∃ A' body', out = .lam A' body' ∧
      ScopedCompute Step Δ (proofErase Γ A) A' ∧
      ScopedCompute Step (proofErase Γ A :: Δ) body body' := by
  generalize E : ProofShape.lam (proofErase Γ A) body = source at R
  induction R generalizing Γ A u body with
  | base H => exact (E ▸ hroot H).elim
  | beta H =>
    cases E
    obtain ⟨A', body', HE, HA, HB⟩ := H.lam_inv
    exact ⟨_, _, HE, .beta HA, .beta HB⟩
  | trans R₁ R₂ ih₁ ih₂ =>
    obtain ⟨A₁, body₁, rfl, RA, RB⟩ := ih₁ hΓ hA hΔ E
    have WI : Ctx.LiftN 0 0 Γ Γ := .zero []
    obtain ⟨A₀, HA, EA⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ WI hA hΔ
      (by simpa only [liftN_zero] using RA)
    simp only [liftN_zero] at EA
    obtain ⟨A₂, body₂, HE, RA₂, RB₂⟩ := ih₂ hΓ HA.hasType.2 hΔ (congrArg (·.lam body₁) EA)
    have HC : IsDefEqCtx env univs Γ (A₀ :: Γ) (A :: Γ) := .succ .zero HA.symm
    have RB₂' : ScopedCompute Step (proofEraseCtx (A₀ :: Γ)) body₁ body₂ := by
      simpa only [proofEraseCtx, hΔ] using RB₂
    have RB₂'' := RB₂'.defeqCtx hsubst hΓ HC
    refine ⟨_, _, HE, RA.trans (EA ▸ RA₂), RB.trans ?_⟩
    simpa only [proofEraseCtx, hΔ] using RB₂''
  | lam RA RB => cases E; exact ⟨_, _, rfl, RA, RB⟩
  | app | proj | forallE => cases E
end ProofShape

/-- Scoped prefix roots, at every finite guard depth, require a constant or
projection head. In particular they cannot contract a displayed lambda. -/
theorem erased_scoped_prefix_stage_head : ∀ stage {Δ a b},
    ErasedScopedPrefixStage D stage Δ a b → ProofShape.PrimitiveHead a := by
  intro stage
  induction stage with
  | zero => exact erased_iota_primitive_head
  | succ stage ih =>
    intro Δ a b H
    rcases H with H | H
    · exact ih H
    · cases H; trivial

/-- Inverting a finite contextual prefix path preserves its stage and returns
the entire body path in the original binder context. -/
theorem proofErase_scoped_prefix_lam_inv
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (R : ProofShape.ScopedCompute (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) body) out) :
    ∃ A' body', out = .lam A' body' ∧
      ProofShape.ScopedCompute (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ)
        (proofErase Γ A) A' ∧
      ProofShape.ScopedCompute (ErasedScopedPrefixStage D stage) (proofEraseCtx (A :: Γ)) body body' := by
  exact R.lam_inv_typed (erased_scoped_prefix_stage_descent heq hs stage)
    (erased_scoped_prefix_stage_subst stage) (erased_scoped_prefix_stage_head stage) hΓ hA rfl

end Lean4Lean.VEnv.Strengthening
