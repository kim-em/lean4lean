import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedApplication
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRawJoinedApplication

/-! # Scoped application with independent or joined arguments

Inferred functions accept arbitrary common-compared arguments. Common function
guards accept literal computational joins, including contextual prefix paths.
No unrestricted comparison composition premise is introduced.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- A typed argument computation extends under a fixed function. Result type
conversion is replayed from the original argument equality. -/
theorem proofErase_scoped_compute_apply_argument (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (Hxy : env.IsDefEq univs Γ x y A)
    (R : ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ y)) :
    ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ (.app f x)) (proofErase Γ (.app f y)) := by
  classical
  have HE := IsDefEq.appDF hf Hxy
  by_cases hp : IsProof Γ (.app f x)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HE).1 hp)]
    exact .refl
  · have hp' := mt (isProof_congr hΓ HE).2 hp
    rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hp,
      show proofErase Γ (.app f y) = .app _ _ from if_neg hp']
    exact .app .refl R

/-- Common scoped function comparison applies to distinct arguments having the
same erasure. This includes distinct proof terms at the shared domain. -/
theorem proofErase_scoped_apply_equal_arguments
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HF : ProofShape.ScopedCompare Step (proofEraseCtx Γ) mode (proofErase Γ f) (proofErase Γ g))
    (E : proofErase Γ x = proofErase Γ y) :
    ProofShape.ScopedCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (.app f x)) (proofErase Γ (.app g y)) := by
  rw [← proofErase_app_arg_eq hΓ hg hx hy E]
  exact proofErase_scoped_apply_same hstep hsubst hΓ hf hg hx HF

/-- Common scoped function comparison applies to distinct computationally joined
arguments. The theorem needs no confluence or comparison composition law. -/
theorem proofErase_scoped_apply_joined_arguments
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HF : ProofShape.ScopedCompare Step (proofEraseCtx Γ) mode (proofErase Γ f) (proofErase Γ g))
    (RX : ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ x) shared)
    (RY : ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ y) shared) :
    ProofShape.ScopedCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (.app f x)) (proofErase Γ (.app g y)) := by
  have W : Ctx.LiftN 0 0 Γ Γ := .zero []
  obtain ⟨x', HX, EX⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ W hx rfl
    (by simpa only [ProofShape.liftN_zero] using RX)
  obtain ⟨y', HY, EY⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ W hy rfl
    (by simpa only [ProofShape.liftN_zero] using RY)
  simp only [ProofShape.liftN_zero] at EX EY
  exact .compute
    (proofErase_scoped_compute_apply_argument hΓ hf HX (by rwa [EX]))
    (proofErase_scoped_compute_apply_argument hΓ hg HY (by rwa [EY]))
    (proofErase_scoped_apply_equal_arguments hstep hsubst hΓ hf hg HX.hasType.2 HY.hasType.2
      HF (EX.trans EY.symm))

/-- Inferred scoped function guards accept arbitrary common-compared
arguments. Reflection aligns dependent result types and proof classification. -/
theorem proofErase_scoped_apply_independent
    (hstep : ErasedScopedPrimitiveDescent Step) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HF : ProofShape.ScopedCompare Step (proofEraseCtx Γ) false (proofErase Γ f) (proofErase Γ g))
    (HX : ProofShape.ScopedCompare Step (proofEraseCtx Γ) true (proofErase Γ x) (proofErase Γ y)) :
    ProofShape.ScopedCompare Step (proofEraseCtx Γ) mode
      (proofErase Γ (.app f x)) (proofErase Γ (.app g y)) := by
  classical
  have Hxy := ((proofErase_scoped_compare_reflect hstep hΓ hx hy HX).1
    ⟨_, (hx.isType henv hΓ).choose_spec⟩).of_l henv hΓ hx
  have hfX := HasType.app hf hx
  have hgY := (IsDefEq.appDF hg Hxy).hasType.2
  by_cases hp : IsProof Γ (.app f x)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 (isProof_of_common_type hΓ hfX hgY hp)]
    exact .refl
  · have hp' : ¬ IsProof Γ (.app g y) := fun h => hp (isProof_of_common_type hΓ hgY hfX h)
    rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hp,
      show proofErase Γ (.app g y) = .app _ _ from if_neg hp']
    exact .app HF HX

/-- Every contextual prefix stage applies common function guards to one typed
argument without increasing the stage, including recursive eta and field guards. -/
theorem proofErase_scoped_prefix_apply_same
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A)
    (H : ProofShape.ScopedCompare (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ) mode
      (proofErase Γ f) (proofErase Γ g)) :
    ProofShape.ScopedCompare (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ) true
      (proofErase Γ (.app f x)) (proofErase Γ (.app g x)) :=
  proofErase_scoped_apply_same (erased_scoped_prefix_stage_descent heq hs stage)
    (erased_scoped_prefix_stage_subst stage) hΓ hf hg hx H

/-- Joined arguments also preserve the same contextual prefix stage. -/
theorem proofErase_scoped_prefix_apply_joined
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HF : ProofShape.ScopedCompare (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ) mode
      (proofErase Γ f) (proofErase Γ g))
    (RX : ProofShape.ScopedCompute (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ)
      (proofErase Γ x) shared)
    (RY : ProofShape.ScopedCompute (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ)
      (proofErase Γ y) shared) :
    ProofShape.ScopedCompare (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ) true
      (proofErase Γ (.app f x)) (proofErase Γ (.app g y)) :=
  proofErase_scoped_apply_joined_arguments (erased_scoped_prefix_stage_descent heq hs stage)
    (erased_scoped_prefix_stage_subst stage) hΓ hf hg hx hy HF RX RY

end Lean4Lean.VEnv.Strengthening
