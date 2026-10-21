import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointImageComputation

/-! # Exact assigned-type recovery before one identity beta step

Every typed argument has a typed identity-redex expansion with exact recovery
at its assigned type whenever it is non-proof. The expansion computes to the
original argument by beta. This direction is deliberately opposite to computing
the original argument to a recoverable image.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- An identity-redex expansion provides exact assigned-type recovery for every
typed non-proof image. Proof images require no recovery. The cover is an actual
typed term, definitionally equal to the image, and contracts to it by beta;
no canonical-Eq, confluence or recovery-existence premise is needed. -/
theorem proofErase_identity_recovery_cover
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x A) :
    let y := VExpr.app (.lam A (.bvar 0)) x
    env.HasType univs Γ y A ∧ env.IsDefEq univs Γ y x A ∧
      ProofShape.BetaRed (proofErase Γ y) (proofErase Γ x) ∧
      (¬ IsProof Γ y → ScopedTypeRecovery Step (proofEraseCtx Γ)
        (proofErase Γ y) (proofErase Γ A)) := by
  obtain ⟨u, hA⟩ := hx.isType henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hv : env.HasType univs (A :: Γ) (.bvar 0) A.lift := .bvar .zero
  have hf := HasType.lam hA hv
  have hy : env.HasType univs Γ (.app (.lam A (.bvar 0)) x) A := by
    simpa only [VExpr.inst_lift] using hf.app hx
  have RB : VExpr.BetaRed (.app (.lam A (.bvar 0)) x) x := by
    simpa [VExpr.inst, instVar, VExpr.liftN_zero] using
      (VExpr.BetaRed.beta (A := A) (b := .bvar 0) (a := x))
  have HE := RB.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ hy
  refine ⟨hy, HE, proofErase_beta_forward hΓ hy RB, ?_⟩
  intro hny
  have hnx : ¬ IsProof Γ x := fun hp => hny ((isProof_congr hΓ HE).2 hp)
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
  have hnv : ¬ IsProof (A :: Γ) (.bvar 0) := by
    intro hp
    have hp' := (isProof_subst hΓ W hv).2 hp
    exact hnx (by simpa [VExpr.Subst.one, VExpr.Subst.cons, VExpr.Subst.liftN] using hp')
  have hnf := not_isProof_fn hΓ hf hx hny
  rw [show proofErase Γ (.app (.lam A (.bvar 0)) x) = .app _ _ from if_neg hny,
    show proofErase Γ (.lam A (.bvar 0)) = .lam _ _ from if_neg hnf,
    show proofErase (A :: Γ) (.bvar 0) = .bvar 0 from if_neg hnv]
  have RI : ScopedTypeRecovery Step (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (.bvar 0))
      (.forallE (proofErase Γ A) ((proofErase Γ A).liftN 1)) := .lam .bvar
  have RA := ScopedTypeRecovery.app (a := proofErase Γ x) RI
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
    ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id] using RA

end Lean4Lean.VEnv.Strengthening
