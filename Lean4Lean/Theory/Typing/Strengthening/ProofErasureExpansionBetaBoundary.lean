import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionBetaSquares

/-! # Why arbitrary reverse beta cannot replace controlled expansion

A closed Prop can expand to a constant function applied to the freshly inserted
Type variable. The expanded term is well typed above, but its retained argument
is outside the image of lifting. This refutes primitive descent, not strengthening.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private ProofShape.liftN_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
variable [Params]

/-- The problematic reverse-beta endpoint is an ordinarily typed term in the
extended context, beta-equal there to the closed source Prop. -/
theorem fresh_argument_constant_beta :
    env.IsDefEq univs [.sort (.succ .zero)]
      (.app (.lam (.sort (.succ .zero)) (.sort .zero)) (.bvar 0))
      (.sort .zero) (.sort (.succ .zero)) :=
  .beta (HasType.sort (by trivial)) (HasType.bvar .zero)

/-- Every visible component of the upper redex survives proof erasure,
including the fresh Type variable that prevents a lower representative. -/
theorem fresh_argument_constant_erasure :
    proofErase [VExpr.sort (.succ .zero)]
      (.app (.lam (.sort (.succ .zero)) (.sort .zero)) (.bvar 0)) =
      .app (.lam (.sort (.succ .zero)) (.sort .zero)) (.bvar 0) := by
  have hΓ : OnCtx [VExpr.sort (.succ .zero)] (env.IsType univs) :=
    ⟨by trivial, _, HasType.sort (by trivial)⟩
  have hΓA : OnCtx [VExpr.sort (.succ .zero), .sort (.succ .zero)] (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  have hf : env.HasType univs [VExpr.sort (.succ .zero)]
      (.lam (.sort (.succ .zero)) (.sort .zero))
      (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) :=
    .lam (HasType.sort (by trivial)) (HasType.sort (by trivial))
  have hx : env.HasType univs [VExpr.sort (.succ .zero)] (.bvar 0) (.sort (.succ .zero)) := .bvar .zero
  rw [show proofErase _ (.app _ _) = .app _ _ from
    if_neg (not_isProof_of_sort hΓ fresh_argument_constant_beta.hasType.1)]
  rw [show proofErase _ (.lam _ _) = .lam _ _ from
    if_neg (not_isProof_function_to_sort hΓ hf)]
  rw [show proofErase _ (.sort (.succ .zero)) = .sort _ from
    if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial)))]
  rw [show proofErase _ (.sort .zero) = .sort _ from
    if_neg (not_isProof_of_sort hΓA (HasType.sort (by trivial)))]
  rw [show proofErase _ (.bvar 0) = .bvar 0 from if_neg (not_isProof_of_sort hΓ hx)]

omit [Params] in
/-- Retaining the freshly inserted argument prevents the raw redex from being
any lifted lower expression, irrespective of the lower expression's typing. -/
theorem ProofShape.fresh_argument_constant_not_lift (e : ProofShape) :
    e.liftN 1 ≠ .app (.lam (.sort (.succ .zero)) (.sort .zero)) (.bvar 0) := by
  intro E
  obtain ⟨f, a, _, _, Ea⟩ := ProofShape.liftN_app_inv E
  cases a <;> simp [ProofShape.liftN, liftVar] at Ea

/-- Allowing every reversed beta reduction as a primitive destroys arbitrary
binder descent, even though the witness's upper expanded endpoint is typed.
The result holds for every Params environment, including canonical Eq ones. -/
theorem erased_typed_reverse_beta_descent_failure :
    ¬ ErasedScopedPrimitiveDescent (fun Δ a b => ProofShape.BetaRed b a ∧ TypedSource Δ b) := by
  intro H
  have hΓ : OnCtx [] (env.IsType univs) := by trivial
  have hΓ' : OnCtx [VExpr.sort (.succ .zero)] (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  have ht : env.HasType univs [] (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have E : proofErase [] (.sort .zero) = .sort .zero := if_neg (not_isProof_of_sort hΓ ht)
  have R : ProofShape.BetaRed
      (.app (.lam (.sort (.succ .zero)) (.sort .zero)) (.bvar 0))
      ((proofErase [] (.sort .zero)).liftN 1) := by
    rw [E]
    exact .beta
  have HT : TypedSource (proofEraseCtx [VExpr.sort (.succ .zero)])
      (.app (.lam (.sort (.succ .zero)) (.sort .zero)) (.bvar 0)) :=
    ⟨_, _, _, hΓ', rfl, fresh_argument_constant_beta.hasType.1, fresh_argument_constant_erasure⟩
  obtain ⟨e', _, Ee⟩ := H hΓ hΓ' Ctx.LiftN.one ht ⟨R, HT⟩
  exact ProofShape.fresh_argument_constant_not_lift _ Ee

/-- Dropping even the upper typing restriction cannot restore descent. -/
theorem erased_reverse_beta_descent_failure :
    ¬ ErasedScopedPrimitiveDescent (fun _ a b => ProofShape.BetaRed b a) := by
  intro H
  apply erased_typed_reverse_beta_descent_failure
  intro Γ Γ' n k e T out hΓ hΓ' W ht R
  exact H hΓ hΓ' W ht R.1

end Lean4Lean.VEnv.Strengthening
