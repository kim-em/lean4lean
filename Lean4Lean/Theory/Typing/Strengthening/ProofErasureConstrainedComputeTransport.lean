import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputeSubstitution

/-! # Typed computation transport with an explicit binder-stable constraint

A substitution side condition need only extend under binders. Source descent
realizes transitive intermediates, so no extra hypothesis is needed there.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- Compatible computation transports from typed primitive simulation. Each
transitive intermediate is realized using source descent; binder bodies use
their actual source domain and the extended interpreted substitution. -/
theorem ProofShape.ScopedCompute.transport_typed
    (hstep : ErasedScopedPrimitiveDescent Step)
    (Transport : List ProofShape → List ProofShape → ProofShape.Subst → Prop)
    (hcons : ∀ {Δ Δ' τ A}, Transport Δ Δ' τ →
      Transport (A :: Δ) (A.subst τ :: Δ') τ.lift)
    (hprimitive : ∀ {Γ Δ Δ' τ e T source out}, Step Δ source out →
      OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      proofEraseCtx Γ = Δ → proofErase Γ e = source → Transport Δ Δ' τ →
      ProofShape.ScopedCompute Target Δ' (source.subst τ) (out.subst τ))
    (R : ScopedCompute Step Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : Transport Δ Δ' τ) :
    ScopedCompute Target Δ' (source.subst τ) (out.subst τ) := by
  induction R generalizing Γ e T Δ' τ with
  | base H => exact hprimitive H hΓ ht EΓ Ee W
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
      (ihb hΓA hb (by simp only [proofEraseCtx, EA, EΓ]) Eb (hcons W))
  | forallE _ _ ihA ihB =>
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    exact .forallE (ihA hΓ hA EΓ EA W)
      (ihB hΓA hB (by simp only [proofEraseCtx, EA, EΓ]) EB (hcons W))

end Lean4Lean.VEnv.Strengthening
