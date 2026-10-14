import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRawApplication
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrefixOnly

/-! # Raw application with computationally joined arguments

Common-compared functions accept arguments with a literal erased computational
join. Typed replay supplies both argument representatives, and their exact
erasure equality avoids any general transitivity premise for raw checking.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- Equal argument erasures at a common type give equal application erasures.
Typed reflection aligns the possibly dependent result types and proofness. -/
theorem proofErase_app_arg_eq (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (E : proofErase Γ x = proofErase Γ y) :
    proofErase Γ (.app f x) = proofErase Γ (.app f y) := by
  obtain ⟨_, HC⟩ := (proofErase_reflect hΓ hx hy E).1 ⟨_, (hx.isType henv hΓ).choose_spec⟩
  have HE := IsDefEq.appDF hf ((HC.defeq hΓ).of_l henv hΓ hx)
  have HP := isProof_congr hΓ HE
  classical
  simp only [proofErase, HP, E]

/-- A typed argument computation extends under a fixed function. Result type
conversion is replayed from the original argument equality. -/
theorem proofErase_compute_apply_argument (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (Hxy : env.IsDefEq univs Γ x y A)
    (R : ProofShape.Compute Step (proofErase Γ x) (proofErase Γ y)) :
    ProofShape.Compute Step (proofErase Γ (.app f x)) (proofErase Γ (.app f y)) := by
  classical
  have HE := IsDefEq.appDF hf Hxy
  by_cases hp : IsProof Γ (.app f x)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HE).1 hp)]
    exact .refl
  · have hp' := mt (isProof_congr hΓ HE).2 hp
    rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hp,
      show proofErase Γ (.app f y) = .app _ _ from if_neg hp']
    exact .app .refl R

/-- Common raw function comparison applies to distinct arguments having the
same erasure. This includes distinct proof terms at the shared domain. -/
theorem proofErase_raw_apply_equal_arguments
    (hstep : ErasedPrimitiveDescent Step)
    (hsubst : ∀ {a b} {τ : ProofShape.Subst}, Step a b → Step (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HF : ProofShape.RawCheckedCompare Step mode (proofErase Γ f) (proofErase Γ g))
    (E : proofErase Γ x = proofErase Γ y) :
    ProofShape.RawCheckedCompare Step true
      (proofErase Γ (.app f x)) (proofErase Γ (.app g y)) := by
  rw [← proofErase_app_arg_eq hΓ hg hx hy E]
  exact proofErase_rawChecked_raw_apply_same hstep hsubst hΓ hf hg hx HF

/-- Common raw function comparison applies to distinct computationally joined
arguments. The theorem needs no confluence or comparison composition law. -/
theorem proofErase_raw_apply_joined_arguments
    (hstep : ErasedPrimitiveDescent Step)
    (hsubst : ∀ {a b} {τ : ProofShape.Subst}, Step a b → Step (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HF : ProofShape.RawCheckedCompare Step mode (proofErase Γ f) (proofErase Γ g))
    (RX : ProofShape.Compute Step (proofErase Γ x) shared)
    (RY : ProofShape.Compute Step (proofErase Γ y) shared) :
    ProofShape.RawCheckedCompare Step true
      (proofErase Γ (.app f x)) (proofErase Γ (.app g y)) := by
  have W : Ctx.LiftN 0 0 Γ Γ := .zero []
  obtain ⟨x', HX, EX⟩ := proofErase_compute_typed_descend hstep hΓ hΓ W hx
    (by simpa only [ProofShape.liftN_zero] using RX)
  obtain ⟨y', HY, EY⟩ := proofErase_compute_typed_descend hstep hΓ hΓ W hy
    (by simpa only [ProofShape.liftN_zero] using RY)
  simp only [ProofShape.liftN_zero] at EX EY
  exact .compute
    (proofErase_compute_apply_argument hΓ hf HX (by rwa [EX]))
    (proofErase_compute_apply_argument hΓ hg HY (by rwa [EY]))
    (proofErase_raw_apply_equal_arguments hstep hsubst hΓ hf hg HX.hasType.2 HY.hasType.2
      HF (EX.trans EY.symm))

/-- All finite prefix-only stages retain raw application closure for common
function guards and computationally joined arguments at the same stage. -/
theorem proofErase_prefix_only_raw_apply_joined
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HF : ProofShape.RawCheckedCompare (ErasedPrefixOnlyStage D stage) mode
      (proofErase Γ f) (proofErase Γ g))
    (RX : ProofShape.Compute (ErasedPrefixOnlyStage D stage) (proofErase Γ x) shared)
    (RY : ProofShape.Compute (ErasedPrefixOnlyStage D stage) (proofErase Γ y) shared) :
    ProofShape.RawCheckedCompare (ErasedPrefixOnlyStage D stage) true
      (proofErase Γ (.app f x)) (proofErase Γ (.app g y)) :=
  proofErase_raw_apply_joined_arguments (erased_prefix_only_descent heq hs)
    (fun H => erased_prefix_only_subst stage H) hΓ hf hg hx hy HF RX RY

end Lean4Lean.VEnv.Strengthening
