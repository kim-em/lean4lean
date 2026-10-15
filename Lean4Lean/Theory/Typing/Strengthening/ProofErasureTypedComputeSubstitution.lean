import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointResynthesis

/-! # Compatible substitution from source-typed primitive simulation

Primitive transport is required only at actual typed sources and may produce
a whole target computation. This is enough for compatible computation, because
source descent realizes every intermediate needed for the induction.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- Typed primitive substitution, allowing a finite target computation rather
than one primitive. The agreement need hold only on retained source variables.
This interface asserts nothing about unrealizable raw primitive sources. -/
def ErasedPrimitiveSubstitutionTo
    (Step Target : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ Γ₀ σ τ e T out}, OnCtx Γ₀ (env.IsType univs) →
    Ctx.SubstEq env univs Γ₀ σ σ Γ → ErasedSubstAgreement Γ Γ₀ σ τ →
    env.HasType univs Γ e T → Step (proofEraseCtx Γ) (proofErase Γ e) out →
    ProofShape.ScopedCompute Target (proofEraseCtx Γ₀)
      (proofErase Γ₀ (e.subst σ)) (out.subst τ)

/-- Source descent realizes a compatible computation at its original context,
including the exact target erasure and its typing at the original type. -/
theorem proofErase_scoped_compute_realize (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (R : ProofShape.ScopedCompute Step Δ source out) :
    ∃ e', env.IsDefEq univs Γ e e' T ∧ proofErase Γ e' = out := by
  have H := proofErase_scoped_compute_descend hstep hΓ hΓ
    (show Ctx.LiftN 0 0 Γ Γ from .zero []) ht EΓ
    (by simpa only [ProofShape.liftN_zero, Ee] using R)
  simpa only [ProofShape.liftN_zero] using H

/-- Compatible computation transports from typed primitive simulation. Each
transitive intermediate is realized using source descent; binder bodies use
their actual source domain and the extended interpreted substitution. -/
theorem ProofShape.ScopedCompute.subst_typed
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ErasedPrimitiveSubstitutionTo Step Target)
    (R : ScopedCompute Step Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : ContextSubstitution Δ Δ' τ) :
    ScopedCompute Target Δ' (source.subst τ) (out.subst τ) := by
  induction R generalizing Γ e T Δ' τ with
  | base H =>
    obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ EΓ
    have H' := hsubst hΓ₀ WS ES ht (by simpa only [EΓ, Ee] using H)
    simpa only [EΓ₀, proofErase_subst_with hΓ₀ WS ht ES, Ee] using H'
  | beta H => exact .beta H.subst
  | trans R₁ R₂ ih₁ ih₂ =>
    obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize hstep hΓ ht EΓ Ee R₁
    exact .trans (ih₁ hΓ ht EΓ Ee W) (ih₂ hΓ HE.hasType.2 EΓ EE W)
  | app _ _ ihf iha =>
    obtain ⟨f, a, rfl, _, Ef, Ea⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    exact .app (ihf hΓ hf EΓ Ef W) (iha hΓ ha EΓ Ea W)
  | proj _ ihm =>
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    exact .proj (ihm hΓ hm.hasType.2 EΓ Em W)
  | lam _ _ ihA ihb =>
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    exact .lam (ihA hΓ hA EΓ EA W)
      (ihb hΓA hb (by simp only [proofEraseCtx, EA, EΓ]) Eb W.cons)
  | forallE _ _ ihA ihB =>
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    exact .forallE (ihA hΓ hA EΓ EA W)
      (ihB hΓA hB (by simp only [proofEraseCtx, EA, EΓ]) EB W.cons)

/-- Ordinary typed simultaneous substitution of compatible computations needs
only source-typed primitive simulation. The target erasure may be specified by
its raw syntax without a separately supplied original representative. -/
theorem proofErase_scoped_compute_subst_typed
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ErasedPrimitiveSubstitutionTo Step Target)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ) (ht : env.HasType univs Γ e T)
    (R : ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ e) out) :
    ProofShape.ScopedCompute Target (proofEraseCtx Γ₀)
      (proofErase Γ₀ (e.subst σ)) (out.subst τ) := by
  rw [proofErase_subst_with hΓ₀ W ht E]
  exact R.subst_typed hstep hsubst W.wf ht rfl rfl
    (ProofShape.ContextSubstitution.of_typed hΓ₀ W E)

end Lean4Lean.VEnv.Strengthening
