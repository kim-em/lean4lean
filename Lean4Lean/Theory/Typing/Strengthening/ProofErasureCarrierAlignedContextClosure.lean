import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedSingletonContext

/-! # Finite computation transport from typed root transport

A primitive occurrence may move to a finite target path. Typed replay provides
intermediate sources; under binders, context conversion preserves the retained
source annotation. This lifts root certificate transport to all finite paths.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private oracle_cons_typed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedJointVariants
variable [Params]

/-- A typed primitive occurrence transports to a finite path with the same raw
output under a structurally varied actual context. -/
def StructuralPrimitiveContext (Step : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ Γ' e T out}, OnCtx Γ (env.IsType univs) → IsDefEqCtx env univs [] Γ Γ' →
    List.Forall₂ StructuralVariant (proofEraseCtx Γ) (proofEraseCtx Γ') →
    env.HasType univs Γ e T → Step (proofEraseCtx Γ) (proofErase Γ e) out →
    ScopedCompute Step (proofEraseCtx Γ') (proofErase Γ' e) out

private theorem context_compute
    (hstep : ErasedScopedPrimitiveDescent Step) (hroot : StructuralPrimitiveContext Step)
    (R : ScopedCompute Step Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : List.Forall₂ StructuralVariant Δ (proofEraseCtx Γ')) :
    ScopedCompute Step (proofEraseCtx Γ') source out := by
  induction R generalizing Γ Γ' e T with
  | base R =>
    have R' := hroot hΓ W (by simpa only [EΓ] using HO) ht (by simpa only [EΓ, Ee] using R)
    simpa only [← proofErase_defeqCtx hΓ W ht, Ee] using R'
  | beta R => exact .beta R
  | trans R₁ R₂ ih₁ ih₂ =>
    obtain ⟨e₁, HE, E₁⟩ := proofErase_scoped_compute_realize hstep hΓ ht EΓ Ee R₁
    exact .trans (ih₁ hΓ ht EΓ Ee W HO) (ih₂ hΓ HE.hasType.2 EΓ E₁ W HO)
  | app Rf Rx ihf ihx =>
    obtain ⟨f, x, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
    exact .app (ihf hΓ hf EΓ Ef W HO) (ihx hΓ hx EΓ Ex W HO)
  | proj Rm ihm =>
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    exact .proj (ihm hΓ hm.hasType.2 EΓ Em W HO)
  | lam RA Rb ihA ihb | forallE RA Rb ihA ihb =>
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := by
      first | exact erase_lam_inv Ee | exact erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := by
      first | exact ht.lam_inv henv hΓ | exact ht.forallE_inv henv
    have RB := ihb (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hb
      (by simp only [proofEraseCtx, EΓ, EA]) Eb (.succ W hA) (oracle_cons_typed hΓ W hA EA HO)
    have RB' := RB
    simp only [proofEraseCtx, ← proofErase_defeqCtx hΓ W hA, EA] at RB'
    first | exact .lam (ihA hΓ hA EΓ EA W HO) RB' | exact .forallE (ihA hΓ hA EΓ EA W HO) RB'

/-- Root context transport extends through all compatible finite computation. -/
theorem structuralVariantComputeContext_of_roots
    (hstep : ErasedScopedPrimitiveDescent Step) (hroot : StructuralPrimitiveContext Step) :
    StructuralVariantComputeContext Step := by
  intro Γ Γ' e T Δ source out hΓ ht W HO EΓ Ee R
  exact context_compute hstep hroot R hΓ ht EΓ Ee W HO

/-- Specialized Eq prefixes preserve their full guard and exact output when
joint checking transports through the ambient structural context conversion. -/
theorem proofErase_computed_joint_prefix_structural_context
    (heq : env.HasCanonicalEq) (hstep : ErasedScopedPrimitiveDescent Step)
    (hctx : StructuralVariantComputeContext Step) (hsim : StructuralVariantCompute Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : List.Forall₂ StructuralVariant (proofEraseCtx Γ) (proofEraseCtx Γ'))
    (ht : env.HasType univs Γ e T)
    (R : ComputedJointPrefixPrimitive Step (proofEraseCtx Γ) (proofErase Γ e) out) :
    ComputedJointPrefixPrimitive Step (proofEraseCtx Γ') (proofErase Γ' e) out := by
  generalize hsrc : proofErase Γ e = source at R
  cases R with
  | @intro α a b v w M m HC =>
    obtain ⟨α₀, a₀, M₀, m₀, b₀, rfl, Hα, Ha, HM, Hm, Hb⟩ := proofErase_eqRecBeforeMajor_inv hsrc
    obtain ⟨_, _, hα, ha, _, _, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
    have HC' := HC.structural_variant hstep hctx hsim hΓ ha hb rfl Hα Ha Hb W HO
      ⟨_, hα⟩ (Hα ▸ StructuralVariant.refl)
    rw [Hα] at HC'
    rw [← proofErase_defeqCtx hΓ W ht, hsrc]
    exact .intro HC'

end Lean4Lean.VEnv.Strengthening
