import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointPropSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedContextConversion

/-! # Proposition comparison across beta and context conversion

The same proposition beta-stability premise transports both endpoints and
converted contexts. Context conversion is interpreted as a typed identity
substitution; no exact recovery of that identity substitution is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- One-sided proposition beta stability gives independent beta residuals of
both endpoints. Replay supplies the intermediate proposition typing. -/
theorem JointPropBetaStability.forward (Hbeta : JointPropBetaStability Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero)) (hQ : env.HasType univs Γ Q (.sort .zero))
    (H : JointCompare Step (proofEraseCtx Γ) true (proofErase Γ P) (proofErase Γ Q))
    (RP : ProofShape.BetaRed (proofErase Γ P) p) (RQ : ProofShape.BetaRed (proofErase Γ Q) q) :
    JointCompare Step (proofEraseCtx Γ) true p q := by
  obtain ⟨P', RP', EP⟩ := proofErase_beta_replay hΓ hP RP
  have HP := (Hbeta hΓ hQ hP H.symm RP).symm
  rw [← EP] at HP ⊢
  exact Hbeta hΓ (beta_eq hΓ hP RP').hasType.2 hQ HP RQ

/-- Under proposition beta stability, a comparison of typed propositions
transports across arbitrary original context conversion with unchanged raw
endpoints. This statement is restricted to propositions, not arbitrary joint
comparison modes or selected type-recovery certificates. -/
theorem JointPropBetaStability.defeqCtx
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (Hbeta : JointPropBetaStability (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs)) (W : IsDefEqCtx env univs Γ Γ₁ Γ₂)
    (hP : env.HasType univs Γ₁ P (.sort .zero)) (hQ : env.HasType univs Γ₁ Q (.sort .zero))
    (H : JointCompare (ErasedJointUnion D) (proofEraseCtx Γ₁) true
      (proofErase Γ₁ P) (proofErase Γ₁ Q)) :
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ₂) true
      (proofErase Γ₁ P) (proofErase Γ₁ Q) := by
  have W₀ : IsDefEqCtx env univs [] Γ₁ Γ₂ := by
    clear hP hQ H
    induction W with
    | zero => exact .refl hΓ
    | succ _ hA ih => exact .succ ih hA
  have hΓ₂ := (W₀.symm henv.ordered).isType
  have WS : Ctx.SubstEq env univs Γ₂ VExpr.Subst.id VExpr.Subst.id Γ₁ :=
    substEq_source_convert hΓ₂ (W₀.symm henv.ordered) (Ctx.SubstEq.id henv.ordered hΓ₂)
  have HC := Hbeta.subst heq hs hΓ₂ WS hP hQ H
  simpa only [VExpr.subst_id, ← proofErase_defeqCtx W₀.isType W hP,
    ← proofErase_defeqCtx W₀.isType W hQ] using HC

end Lean4Lean.VEnv.Strengthening
