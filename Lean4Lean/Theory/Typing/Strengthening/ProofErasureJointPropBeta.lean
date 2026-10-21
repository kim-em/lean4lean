import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIdentityRecoveryCover

/-! # Proposition beta stability as a guard-substitution obligation

The identity expansion gives exact recovery before substitution. If common
comparison of propositions survives beta contraction, its copies can then be
contracted in both endpoints. This isolates a proposition-only stability law;
the law itself, and its sufficiency for the original front, remain unproved.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Missing stability law: a common comparison of two typed propositions
survives beta reduction of its right endpoint in the same primitive relation.
This asks neither for type recovery nor for comparisons of arbitrary terms. -/
def JointPropBetaStability (Step : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ P Q out}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ P (.sort .zero) → env.HasType univs Γ Q (.sort .zero) →
    JointCompare Step (proofEraseCtx Γ) true (proofErase Γ P) (proofErase Γ Q) →
    ProofShape.BetaRed (proofErase Γ Q) out →
    JointCompare Step (proofEraseCtx Γ) true (proofErase Γ P) out

private theorem beta_images (e : ProofShape) {σ τ : ProofShape.Subst}
    (H : ∀ i, ProofShape.BetaRed (σ i) (τ i)) :
    ProofShape.BetaRed (e.subst σ) (e.subst τ) := by
  induction e generalizing σ τ with
  | proof | sort | const => exact .refl
  | bvar i => exact H i
  | app f a ihf iha => exact .app (ihf H) (iha H)
  | proj s i m ih => exact .proj (ih H)
  | lam A b ihA ihb | forallE A b ihA ihb =>
    have HB : ∀ i, ProofShape.BetaRed (σ.lift i) (τ.lift i) := by
      intro i
      cases i with
      | zero => exact .refl
      | succ i => exact (H i).liftN
    first | exact .lam (ihA H) (ihb HB) | exact .forallE (ihA H) (ihb HB)

private theorem beta_inst_image (e : ProofShape) (R : ProofShape.BetaRed x y) :
    ProofShape.BetaRed (e.inst x) (e.inst y) := by
  simp only [ProofShape.inst_eq_subst]
  apply beta_images
  intro i
  cases i with
  | zero => exact R
  | succ i => exact .refl

/-- Proposition beta stability of the joint union removes the recovery premise
from arbitrary typed instantiation of proposition comparisons. The input may
be any finite joint stage, and the output has a finite later stage. No raw
confluence or carrier-domain re-synthesis hypothesis is used. -/
theorem JointPropBetaStability.inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (Hbeta : JointPropBetaStability (ErasedJointUnion D))
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hP : env.HasType univs (A :: Γ) P (.sort .zero))
    (hQ : env.HasType univs (A :: Γ) Q (.sort .zero))
    (hx : env.HasType univs Γ x A)
    (H : JointCompare (ErasedJointStage D stage) (proofEraseCtx (A :: Γ)) true
      (proofErase (A :: Γ) P) (proofErase (A :: Γ) Q)) :
    ∃ later, stage ≤ later ∧
      JointCompare (ErasedJointStage D later) (proofEraseCtx Γ) true
        (proofErase Γ (P.inst x)) (proofErase Γ (Q.inst x)) := by
  let y := VExpr.app (.lam A (.bvar 0)) x
  obtain ⟨hy, _, RY, HR⟩ := proofErase_identity_recovery_cover
    (Step := ErasedJointStage D 0) hΓA.1 hx
  have hy : env.HasType univs Γ y A := hy
  have H' := proofErase_joint_compare_inst_recoverable heq hs hΓA.1 hy HR hP hQ H
  simp only [Nat.zero_add] at H'
  have hPy : env.HasType univs Γ (P.inst y) (.sort .zero) := hP.instN henv Ctx.InstN.zero hy
  have hQy : env.HasType univs Γ (Q.inst y) (.sort .zero) := hQ.instN henv Ctx.InstN.zero hy
  have hQx : env.HasType univs Γ (Q.inst x) (.sort .zero) := hQ.instN henv Ctx.InstN.zero hx
  have RP : ProofShape.BetaRed (proofErase Γ (P.inst y)) (proofErase Γ (P.inst x)) := by
    rw [proofErase_instN hΓA hy Ctx.InstN.zero hP, proofErase_instN hΓA hx Ctx.InstN.zero hP]
    exact beta_inst_image _ RY
  have RQ : ProofShape.BetaRed (proofErase Γ (Q.inst y)) (proofErase Γ (Q.inst x)) := by
    rw [proofErase_instN hΓA hy Ctx.InstN.zero hQ, proofErase_instN hΓA hx Ctx.InstN.zero hQ]
    exact beta_inst_image _ RY
  have HQ := Hbeta hΓA.1 hPy hQy (H'.mono (fun R => ⟨stage, R⟩)) RQ
  have HP := (Hbeta hΓA.1 hQx hPy HQ.symm RP).symm
  obtain ⟨later, HL⟩ := HP.finite_stage erased_joint_stage_mono
  exact ⟨max stage later, Nat.le_max_left _ _, HL.mono (erased_joint_stage_mono (Nat.le_max_right _ _))⟩

end Lean4Lean.VEnv.Strengthening
