import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationEq

/-! # Dependent application congruence for typed computation chains

Intermediate argument values have changing dependent result assignments. Actual
equality of their types permits retagging each chain segment; no generic
fixed-result template or computational confluence is required.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

/-- Two typed forward computations lift through dependent application.
The actual appDF equality ensures that proof erasure agrees at the endpoints. -/
theorem proofErase_scoped_compute_app_eq
    (hΓ : OnCtx Γ (env.IsType univs))
    (HF : env.IsDefEq univs Γ f g (.forallE A B)) (HX : env.IsDefEq univs Γ x y A)
    (RF : ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ f) (proofErase Γ g))
    (RX : ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ y)) :
    ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ (.app f x)) (proofErase Γ (.app g y)) := by
  have HE := IsDefEq.appDF HF HX
  classical
  by_cases hp : IsProof Γ (.app f x)
  · have hp' := (isProof_congr hΓ HE).1 hp
    rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 hp']
    exact .refl
  have hp' : ¬ IsProof Γ (.app g y) := fun h => hp ((isProof_congr hΓ HE).2 h)
  rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hp,
    show proofErase Γ (.app g y) = .app _ _ from if_neg hp']
  exact .app RF RX

/-- A computation chain in function position lifts through any fixed typed
argument, including a dependent codomain. No joining premise is required. -/
theorem TypedComputationEq.app_fn
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : TypedComputationEq D Γ f g (.forallE A B)) (hx : env.HasType univs Γ x A) :
    TypedComputationEq D Γ (.app f x) (.app g x) (B.inst x) := by
  generalize ET : VExpr.forallE A B = T at H
  induction H generalizing A B x with
  | step HE R =>
    cases ET
    exact .step (.appDF HE hx) (proofErase_scoped_compute_app_eq hΓ HE hx R .refl)
  | symm _ ih => exact (ih hx ET).symm
  | trans _ _ ih₁ ih₂ => exact (ih₁ hx ET).trans (ih₂ hx ET)

/-- A computation chain in argument position lifts through a dependent
function. Symmetry and transitivity retag intermediate results using ordinary
codomain instantiation equality. No data confluence or native coverage is used. -/
theorem TypedComputationEq.app_arg
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : TypedComputationEq D Γ x y A)
    (hf : env.HasType univs Γ f (.forallE A B)) :
    TypedComputationEq D Γ (.app f x) (.app f y) (B.inst x) := by
  induction H with
  | step HE R =>
    exact .step (.appDF hf HE) (proofErase_scoped_compute_app_eq hΓ hf HE .refl R)
  | symm H ih =>
    obtain ⟨_, hPi⟩ := hf.isType henv hΓ
    obtain ⟨⟨u, hA⟩, _, hB⟩ := hPi.forallE_inv henv
    have HT := hB.instN_DF Ctx.InstN.zero ⟨hΓ, u, hA⟩ H.defeq
    exact ((ih hf).symm).convert HT
  | trans H₁ _ ih₁ ih₂ =>
    obtain ⟨_, hPi⟩ := hf.isType henv hΓ
    obtain ⟨⟨u, hA⟩, _, hB⟩ := hPi.forallE_inv henv
    have HT := hB.instN_DF Ctx.InstN.zero ⟨hΓ, u, hA⟩ H₁.defeq
    exact (ih₁ hf).trans ((ih₂ hf).convert HT.symm)

/-- Full dependent application congruence follows for typed computation
chains. This covers arbitrary retained data arguments, without assuming they
are proofs, types, or computationally joinable. -/
theorem TypedComputationEq.app
    (hΓ : OnCtx Γ (env.IsType univs))
    (HF : TypedComputationEq D Γ f g (.forallE A B))
    (HX : TypedComputationEq D Γ x y A) :
    TypedComputationEq D Γ (.app f x) (.app g y) (B.inst x) :=
  (HF.app_fn hΓ HX.defeq.hasType.1).trans (HX.app_arg hΓ HF.defeq.hasType.2)

end Lean4Lean.VEnv.Strengthening
