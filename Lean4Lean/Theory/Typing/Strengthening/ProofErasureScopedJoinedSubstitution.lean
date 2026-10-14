import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSubstitutionRealization

/-! # Scoped paired body instantiation at computationally joined arguments

Computations of both instances end at a common raw argument substitution.
Typed replay of one argument realizes the context interpretation needed to
substitute the body certificate. No composition of comparisons is used.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
variable {τ : ProofShape.Subst}

/-- Two typed simultaneous substitutions with pointwise computational joins
preserve a scoped body certificate. The shared raw map obtains its context
interpretation by replaying the first substitution's image computations. -/
theorem proofErase_scoped_subst_join_with
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs))
    (W₁ : Ctx.SubstEq env univs Γ₀ σ₁ σ₁ Γ) (W₂ : Ctx.SubstEq env univs Γ₀ σ₂ σ₂ Γ)
    (E₁ : ErasedSubstAgreement Γ Γ₀ σ₁ ρ₁) (E₂ : ErasedSubstAgreement Γ Γ₀ σ₂ ρ₂)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ProofShape.ScopedCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b))
    (R₁ : ∀ i, ProofShape.ScopedCompute Step (proofEraseCtx Γ₀) (ρ₁ i) (τ i))
    (R₂ : ∀ i, ProofShape.ScopedCompute Step (proofEraseCtx Γ₀) (ρ₂ i) (τ i)) :
    ProofShape.ScopedCompare Step (proofEraseCtx Γ₀) mode
      (proofErase Γ₀ (a.subst σ₁)) (proofErase Γ₀ (b.subst σ₂)) := by
  rw [proofErase_subst_with hΓ₀ W₁ ha E₁, proofErase_subst_with hΓ₀ W₂ hb E₂]
  have WC : ProofShape.ContextSubstitution (proofEraseCtx Γ) (proofEraseCtx Γ₀) ρ₁ :=
    ProofShape.ContextSubstitution.of_typed hΓ₀ W₁ E₁
  exact .compute
    (proofErase_scoped_compute_subst_images hsubst hΓ₀ W₁ ha E₁ R₁)
    (proofErase_scoped_compute_subst_images hsubst hΓ₀ W₂ hb E₂ R₂)
    (H.subst hsubst (WC.compute_images hstep R₁))

/-- With the canonical erased image maps, simultaneous joined substitution
requires only ordinary typed substitutions and their pointwise erased joins. -/
theorem proofErase_scoped_subst_join
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs))
    (W₁ : Ctx.SubstEq env univs Γ₀ σ₁ σ₁ Γ) (W₂ : Ctx.SubstEq env univs Γ₀ σ₂ σ₂ Γ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ProofShape.ScopedCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b))
    (R₁ : ∀ i, ProofShape.ScopedCompute Step (proofEraseCtx Γ₀) (proofErase Γ₀ (σ₁ i)) (τ i))
    (R₂ : ∀ i, ProofShape.ScopedCompute Step (proofEraseCtx Γ₀) (proofErase Γ₀ (σ₂ i)) (τ i)) :
    ProofShape.ScopedCompare Step (proofEraseCtx Γ₀) mode
      (proofErase Γ₀ (a.subst σ₁)) (proofErase Γ₀ (b.subst σ₂)) :=
  proofErase_scoped_subst_join_with hstep hsubst hΓ₀ W₁ W₂
    (fun _ _ => rfl) (fun _ _ => rfl) ha hb H R₁ R₂

/-- Scoped body certificates instantiate at distinct computationally joined
arguments. Both comparison modes are preserved, including under dependent
binders; only one shared argument realization is reconstructed. -/
theorem proofErase_scoped_inst_join
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hb' : env.HasType univs (A :: Γ) b' B')
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HB : ProofShape.ScopedCompare Step (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) b) (proofErase (A :: Γ) b'))
    (RX : ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ x) shared)
    (RY : ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ y) shared) :
    ProofShape.ScopedCompare Step (proofEraseCtx Γ) mode
      (proofErase Γ (b.inst x)) (proofErase Γ (b'.inst y)) := by
  have W₀ : Ctx.LiftN 0 0 Γ Γ := .zero []
  obtain ⟨z, HZ, EZ⟩ := proofErase_scoped_compute_descend hstep hΓA.1 hΓA.1
    W₀ hx rfl (by simpa only [ProofShape.liftN_zero] using RX)
  simp only [ProofShape.liftN_zero] at EZ
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := z) (A₀ := A)).substEq hΓA HZ.hasType.2
  have E : ErasedSubstAgreement (A :: Γ) Γ (VExpr.Subst.one z)
      (ProofShape.Subst.one (proofErase Γ z)) := erasedSubstAgreement_one hΓA HZ.hasType.2
  rw [EZ] at E
  have HC := HB.subst hsubst (ProofShape.ContextSubstitution.of_typed hΓA.1 W E)
  apply ProofShape.ScopedCompare.compute
    (proofErase_scoped_compute_inst_argument hsubst hΓA hb hx RX)
    (proofErase_scoped_compute_inst_argument hsubst hΓA hb' hy RY)
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HC

/-- Every finite contextual prefix stage preserves joined-argument paired
instantiation at its original bound and in its original comparison mode. -/
theorem proofErase_scoped_prefix_inst_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hb' : env.HasType univs (A :: Γ) b' B')
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HB : ProofShape.ScopedCompare (ErasedScopedPrefixStage D stage) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) b) (proofErase (A :: Γ) b'))
    (RX : ProofShape.ScopedCompute (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ)
      (proofErase Γ x) shared)
    (RY : ProofShape.ScopedCompute (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ)
      (proofErase Γ y) shared) :
    ProofShape.ScopedCompare (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ) mode
      (proofErase Γ (b.inst x)) (proofErase Γ (b'.inst y)) :=
  proofErase_scoped_inst_join (erased_scoped_prefix_stage_descent heq hs stage)
    (erased_scoped_prefix_stage_subst stage) hΓA hb hb' hx hy HB RX RY

/-- Simultaneous joined substitution also preserves each finite contextual
prefix stage, with no growth in its guard depth. -/
theorem proofErase_scoped_prefix_subst_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs))
    (W₁ : Ctx.SubstEq env univs Γ₀ σ₁ σ₁ Γ) (W₂ : Ctx.SubstEq env univs Γ₀ σ₂ σ₂ Γ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ProofShape.ScopedCompare (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b))
    (R₁ : ∀ i, ProofShape.ScopedCompute (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (σ₁ i)) (τ i))
    (R₂ : ∀ i, ProofShape.ScopedCompute (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (σ₂ i)) (τ i)) :
    ProofShape.ScopedCompare (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ₀) mode
      (proofErase Γ₀ (a.subst σ₁)) (proofErase Γ₀ (b.subst σ₂)) :=
  proofErase_scoped_subst_join (erased_scoped_prefix_stage_descent heq hs stage)
    (erased_scoped_prefix_stage_subst stage) hΓ₀ W₁ W₂ ha hb H R₁ R₂

end Lean4Lean.VEnv.Strengthening
