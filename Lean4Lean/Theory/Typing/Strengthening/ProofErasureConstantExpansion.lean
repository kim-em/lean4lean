import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming

/-! # Source-typed constant beta expansion

A fixed closed argument permits backward beta expansion without importing free
variables from an arbitrary redex. Proof sources are excluded because their
expansions erase to the proof marker, not to an application.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives

namespace ProofShape
/-- Add an unused Type-valued binder and apply it to Prop. -/
def constantExpansion (a : ProofShape) : ProofShape :=
  .app (.lam (.sort (.succ .zero)) (a.liftN 1)) (.sort .zero)

/-- Expansion is allowed precisely when its application survives erasure. -/
inductive ConstantExpansion : ProofShape → ProofShape → Prop where
  | intro : a ≠ .proof → ConstantExpansion a (constantExpansion a)

/-- The fixed argument introduces no variables, including below inserted blocks. -/
theorem constantExpansion_liftN : (constantExpansion a).liftN n k =
    constantExpansion (a.liftN n k) := by
  simp only [constantExpansion, liftN,
    ← liftN_comm _ n 1 k 0 (Nat.zero_le _)]

/-- The unused binder is compatible with arbitrary raw substitution. The
primitive's non-proof side condition is handled separately at typed sources. -/
theorem constantExpansion_subst : (constantExpansion a).subst τ =
    constantExpansion (a.subst τ) := by
  simp only [constantExpansion, subst, lift_subst_lift]
end ProofShape

variable [Params]
/-- An actual expansion always has its source's original type. -/
theorem constantExpansion_equal (ht : env.HasType univs Γ e T) :
    env.IsDefEq univs Γ (.app (.lam (.sort (.succ .zero)) e.lift) (.sort .zero)) e T := by
  simpa only [VExpr.inst_lift] using
    (IsDefEq.beta (ht.weak henv) (HasType.sort (l := .zero) (by trivial)))

/-- Non-proof sources retain the complete constant expansion after erasure. -/
theorem proofErase_constantExpansion (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ e T) (hn : ¬ IsProof Γ e) :
    proofErase Γ (.app (.lam (.sort (.succ .zero)) e.lift) (.sort .zero)) =
      constantExpansion (proofErase Γ e) := by
  have HH := constantExpansion_equal ht
  have hn' := mt (isProof_congr hΓ HH).1 hn
  have hS : env.HasType univs Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) := .sort (by trivial)
  have hΓS : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType univs) := ⟨hΓ, _, hS⟩
  have hf := HasType.lam hS (ht.weak henv)
  have hx : env.HasType univs Γ (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  rw [show proofErase Γ (.app _ _) = .app _ _ from if_neg hn']
  rw [show proofErase Γ (.lam _ _) = .lam _ _ from if_neg (not_isProof_fn hΓ hf hx hn')]
  rw [show proofErase Γ (.sort (.succ .zero)) = .sort _ from if_neg (not_isProof_of_sort hΓ hS)]
  rw [show proofErase Γ (.sort .zero) = .sort _ from if_neg (not_isProof_of_sort hΓ hx)]
  rw [proofErase_liftN hΓ hΓS Ctx.LiftN.one ht]
  rfl

/-- Constant expansion descends through any inserted binder block. No native
coverage, semantic head exposure or strengthening assumption is used. -/
theorem erased_constantExpansion_descent :
    ErasedScopedPrimitiveDescent (fun _ => ConstantExpansion) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht H
  cases H with
  | intro hn =>
    have hne : ¬ IsProof Γ e := by
      intro hp
      exact hn (by rw [proofErase_eq_proof.2 hp]; rfl)
    refine ⟨_, (constantExpansion_equal ht).symm, ?_⟩
    rw [proofErase_constantExpansion hΓ ht hne, constantExpansion_liftN]

/-- Renamings preserve the primitive even for raw sources without a typing. -/
theorem ProofShape.ConstantExpansion.rename (H : ConstantExpansion a b)
    (W : ContextRenaming Δ Δ' τ) : ConstantExpansion (a.subst τ) (b.subst τ) := by
  cases H with
  | intro hn =>
    rw [constantExpansion_subst]
    apply ConstantExpansion.intro
    cases a with
    | proof => exact (hn rfl).elim
    | bvar i => obtain ⟨j, E, _⟩ := W.lookup i; simp only [subst, E]; intro E; cases E
    | sort | const | app | proj | lam | forallE => intro E; cases E

/-- Typed substitution preserves the non-proof side condition, even when
untyped substitution could replace a retained raw variable by a proof marker. -/
theorem ProofShape.ConstantExpansion.subst_typed (H : ConstantExpansion source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : ContextSubstitution Δ Δ' τ) : ConstantExpansion (source.subst τ) (out.subst τ) := by
  cases H with
  | intro hn =>
    rw [constantExpansion_subst]
    apply ConstantExpansion.intro
    obtain ⟨Γ₀, σ, hΓ₀, _, WS, ES⟩ := W hΓ EΓ
    rw [← Ee, ← proofErase_subst_with hΓ₀ WS ht ES]
    intro E
    exact hn (Ee ▸ proofErase_eq_proof.2 ((isProof_subst hΓ₀ WS ht).1 (proofErase_eq_proof.1 E)))

end Lean4Lean.VEnv.Strengthening
