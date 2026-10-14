import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedCoverage

/-! # Reindexing scoped certificates along original context conversion -/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

namespace ProofShape
/-- Original context conversion interprets the identity raw substitution.
The raw contexts may differ; retained variables keep their literal indices. -/
theorem ContextSubstitution.of_defeqCtx (hΓ : OnCtx Γ (env.IsType univs))
    (H : IsDefEqCtx env univs Γ Γ₁ Γ₂) :
    ContextSubstitution (proofEraseCtx Γ₁) (proofEraseCtx Γ₂) Subst.id := by
  have H₀ : IsDefEqCtx env univs [] Γ₁ Γ₂ := by
    induction H with
    | zero => exact .refl hΓ
    | succ _ hA ih => exact .succ ih hA
  have hΓ₂ := (H₀.symm henv.ordered).isType
  have W : Ctx.SubstEq env univs Γ₂ VExpr.Subst.id VExpr.Subst.id Γ₁ :=
    substEq_source_convert hΓ₂ (H₀.symm henv.ordered)
      (Ctx.SubstEq.id henv.ordered hΓ₂)
  apply ContextSubstitution.of_typed hΓ₂ W
  intro i A hl hn
  have hn' : ¬ IsProof Γ₂ (.bvar i) := mt (isProof_defeqCtx H).2 hn
  simp only [VExpr.Subst.id, proofErase, if_neg hn', Subst.id]

/-- Context conversion preserves a raw scoped path with exactly its original
endpoints, without requiring separate endpoint typings. -/
theorem ScopedCompute.defeqCtx
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (H : IsDefEqCtx env univs Γ Γ₁ Γ₂)
    (R : ScopedCompute Step (proofEraseCtx Γ₁) a b) :
    ScopedCompute Step (proofEraseCtx Γ₂) a b := by
  simpa only [subst_id] using R.subst hsubst (ContextSubstitution.of_defeqCtx hΓ H)

/-- Context conversion also preserves every scoped comparison mode and every
recursive sort or field guard. -/
theorem ScopedCompare.defeqCtx
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (H : IsDefEqCtx env univs Γ Γ₁ Γ₂)
    (R : ScopedCompare Step (proofEraseCtx Γ₁) mode a b) :
    ScopedCompare Step (proofEraseCtx Γ₂) mode a b := by
  simpa only [subst_id] using R.subst hsubst (ContextSubstitution.of_defeqCtx hΓ H)
end ProofShape

end Lean4Lean.VEnv.Strengthening
