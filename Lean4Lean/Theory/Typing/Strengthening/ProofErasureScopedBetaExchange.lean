import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedBinderComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSubstitutionSquare

/-! # Head beta against finite scoped function and argument computation

Lambda inversion retains the body path in its original context. The substitution
square then joins head beta with independently computed function and argument
paths, including computations in the displayed lambda annotation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Contracting beta before arbitrary finite computation of its lambda and
argument joins with contracting beta afterwards. The latter residual is one
beta step; the former uses the same scoped relation, with no confluence premise.
Only the initial domain, body and argument have supplied original typings. -/
theorem proofErase_scoped_beta_exchange
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hroot : ∀ {Δ a b}, Step Δ a b → ProofShape.PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (RF : ProofShape.ScopedCompute Step (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) functionOut)
    (RX : ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ x) argumentOut) :
    ∃ D bodyOut, functionOut = .lam D bodyOut ∧
      ProofShape.ScopedCompute Step (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) (bodyOut.inst argumentOut) ∧
      ProofShape.BetaRed (.app functionOut argumentOut) (bodyOut.inst argumentOut) := by
  obtain ⟨D, bodyOut, rfl, _, RB⟩ := RF.lam_inv_typed hstep hsubst hroot hΓ hA rfl
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
  have square := proofErase_scoped_compute_subst_square hstep hsubst hΓ W
    (erasedSubstAgreement_one hΓA hx) hb RB (τ := ProofShape.Subst.one argumentOut)
    (fun i => by cases i with | zero => exact RX | succ i => exact .refl)
  refine ⟨D, bodyOut, rfl, ?_, .beta⟩
  rw [proofErase_instN hΓA hx Ctx.InstN.zero hb]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using square.1.trans square.2.2.1

/-- The head-beta/function-argument overlap closes at every finite contextual
prefix stage without increasing its bound, even if the paths contain K steps. -/
theorem proofErase_scoped_prefix_beta_exchange
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (RF : ProofShape.ScopedCompute (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) functionOut)
    (RX : ProofShape.ScopedCompute (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ)
      (proofErase Γ x) argumentOut) :
    ∃ D' bodyOut, functionOut = .lam D' bodyOut ∧
      ProofShape.ScopedCompute (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) (bodyOut.inst argumentOut) ∧
      ProofShape.BetaRed (.app functionOut argumentOut) (bodyOut.inst argumentOut) :=
  proofErase_scoped_beta_exchange (erased_scoped_prefix_stage_descent heq hs stage)
    (erased_scoped_prefix_stage_subst stage) (erased_scoped_prefix_stage_head stage)
    hΓ hA hb hx RF RX

end Lean4Lean.VEnv.Strengthening
