import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierResynthesisBoundary

/-! # Finite-stage joint domain re-synthesis

Ordinary-core recovery already fails the fixed-stage law independently of the
comparison primitives. This interface permits a later recovery and comparison
stage and keeps the coupled domain/guard requirement. It is an open obligation;
the conditional theorem establishes its exact use for application substitution.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Missing finite-stage joint re-synthesis. Both the recovered Pi and the
argument carrier guard may move to a common later stage, with no prescribed
domain or codomain syntax. This is unproved for the concrete stage families
and is not claimed a strictly smaller or sufficient strengthening front. -/
def FiniteCarrierDomainResynthesis
    (Recoveries : Nat → ProofShape → ProofShape → Prop)
    (Stages : Nat → List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {stage Γ Γ₀ σ f x y D C A B}, OnCtx Γ₀ (env.IsType univs) →
    Ctx.SubstEq env univs Γ₀ σ σ Γ →
    env.HasType univs Γ f (.forallE D C) →
    env.HasType univs Γ x D → env.HasType univs Γ y D →
    ProofShape.TypeRecovery (Recoveries stage) (ProofShape.contextOracle (proofEraseCtx Γ))
      (proofErase Γ f) (.forallE A B) →
    ProofShape.StructureCarrierGuard (Stages stage) (proofEraseCtx Γ) A
      (proofErase Γ x) (proofErase Γ y) →
    ∃ later A' B', stage ≤ later ∧
      ProofShape.TypeRecovery (Recoveries later) (ProofShape.contextOracle (proofEraseCtx Γ₀))
        (proofErase Γ₀ (f.subst σ)) (.forallE A' B') ∧
      ProofShape.StructureCarrierGuard (Stages later) (proofEraseCtx Γ₀) A'
        (proofErase Γ₀ (x.subst σ)) (proofErase Γ₀ (y.subst σ))

/-- The finite-stage law transports recovered application roots after typed
substitution. Monotonicity moves the independently substituted function
comparison to the stage chosen by joint re-synthesis. -/
theorem proofErase_carrier_application_subst_of_finite_resynthesis
    (hres : FiniteCarrierDomainResynthesis Recoveries Stages)
    (hsubst : ∀ stage {Δ Δ' a b τ}, Stages stage Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Stages stage Δ' (a.subst τ) (b.subst τ))
    (hmono : ∀ {stage later}, stage ≤ later → ∀ {Δ a b}, Stages stage Δ a b → Stages later Δ a b)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (hf : env.HasType univs Γ f (.forallE D C)) (hg : env.HasType univs Γ g (.forallE D C))
    (hx : env.HasType univs Γ x D) (hy : env.HasType univs Γ y D)
    (hnl : ¬ IsProof Γ (.app f x)) (hnr : ¬ IsProof Γ (.app g y))
    (R : ProofShape.TypeRecovery (Recoveries stage) (ProofShape.contextOracle (proofEraseCtx Γ))
      (proofErase Γ f) (.forallE A B))
    (HF : ProofShape.ScopedCompare (Stages stage) (proofEraseCtx Γ) false
      (proofErase Γ f) (proofErase Γ g))
    (HX : ProofShape.StructureCarrierGuard (Stages stage) (proofEraseCtx Γ) A
      (proofErase Γ x) (proofErase Γ y)) :
    ∃ later, stage ≤ later ∧
      ProofShape.RecoveredCarrierApplication (Recoveries later) (Stages later) (proofEraseCtx Γ₀)
        (proofErase Γ₀ ((VExpr.app f x).subst σ)) (proofErase Γ₀ ((VExpr.app g y).subst σ)) := by
  obtain ⟨later, A', B', hle, R', HX'⟩ := hres hΓ₀ W hf hx hy R HX
  have HF' := proofErase_scoped_compare_subst (hsubst stage) hΓ₀ W hf hg HF
  have hnl' := mt (isProof_subst hΓ₀ W (hf.app hx)).1 hnl
  have hnr' := mt (isProof_subst hΓ₀ W (hg.app hy)).1 hnr
  refine ⟨later, hle, ?_⟩
  rw [show proofErase Γ₀ ((VExpr.app f x).subst σ) = .app _ _ from if_neg hnl',
    show proofErase Γ₀ ((VExpr.app g y).subst σ) = .app _ _ from if_neg hnr']
  exact .app R' (HF'.mono (hmono hle)) HX'

end Lean4Lean.VEnv.Strengthening
