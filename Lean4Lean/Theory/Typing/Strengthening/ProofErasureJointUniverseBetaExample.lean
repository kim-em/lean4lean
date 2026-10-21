import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUniverseHeadBeta

/-! # A retained proposition argument without displayed-domain recovery

The displayed domain beta-expands Prop. A fresh proposition variable recovers
Prop but cannot recover that application-shaped expansion. The universe-domain
head-beta theorem nevertheless applies to arbitrary compared bodies.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Exact recovery of the displayed domain can fail in the entire union even
for a retained proposition argument. All inferred comparisons of proposition
lambdas at the expanded domain still survive diagonal beta; the bodies may
retain their variable and have arbitrary internal computations. -/
theorem proofErase_joint_universe_beta_without_domain_recovery
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ Δ A, OnCtx Δ (env.IsType univs) ∧
      env.IsDefEq univs Δ A (.sort .zero) (.sort (.succ .zero)) ∧
      env.HasType univs Δ (.bvar 0) (.sort .zero) ∧
      ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Δ)
        (proofErase Δ (.bvar 0)) (.sort .zero) ∧
      (¬ ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Δ)
        (proofErase Δ (.bvar 0)) (proofErase Δ A)) ∧
      ∀ {b c : VExpr},
        env.HasType univs Δ (.lam A b) (.forallE (.sort .zero) (.sort .zero)) →
        env.HasType univs Δ (.lam A c) (.forallE (.sort .zero) (.sort .zero)) →
        JointCompare (ErasedJointUnion D) (proofEraseCtx Δ) false
          (proofErase Δ (.lam A b)) (proofErase Δ (.lam A c)) →
        JointCompare (ErasedJointUnion D) (proofEraseCtx Δ) true
          (proofErase Δ (b.inst (.bvar 0))) (proofErase Δ (c.inst (.bvar 0))) := by
  let Δ : List VExpr := .sort .zero :: Γ
  let A : VExpr := .app (.lam (.sort (.succ .zero)) (.bvar 0)) (.sort .zero)
  have hS : env.HasType univs Γ (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have hΔ : OnCtx Δ (env.IsType univs) := ⟨hΓ, _, hS⟩
  have hp : env.HasType univs Δ (.bvar 0) (.sort .zero) := .bvar .zero
  have HE : env.IsDefEq univs Δ A (.sort .zero) (.sort (.succ .zero)) := by
    simpa [A, VExpr.inst, VExpr.lift, VExpr.liftN] using
      (IsDefEq.beta (env := env) (uvars := univs) (Γ := Δ)
        (HasType.bvar (A := VExpr.sort (.succ .zero)) .zero)
        (HasType.sort (by trivial : VLevel.zero.WF univs)))
  have Ep : proofErase Δ (.bvar 0) = .bvar 0 := if_neg (not_isProof_of_sort hΔ hp)
  have EO : contextOracle (proofEraseCtx Δ) 0 = .sort .zero := by
    change (proofErase Γ (.sort .zero)).liftN 1 = .sort .zero
    rw [show proofErase Γ (.sort .zero) = .sort .zero from if_neg (not_isProof_of_sort hΓ hS)]
    rfl
  have HR : ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Δ)
      (proofErase Δ (.bvar 0)) (.sort .zero) := by
    rw [Ep, ← EO]
    exact .bvar
  refine ⟨Δ, A, hΔ, HE, hp, HR, ?_, ?_⟩
  · intro R
    rw [Ep] at R
    have RC := R.bvar_compute
    rw [EO] at RC
    have E := RC.sort_fixed erased_joint_union_head
    have EA : proofErase Δ A = .app
        (proofErase Δ (.lam (.sort (.succ .zero)) (.bvar 0)))
        (proofErase Δ (.sort .zero)) := if_neg (not_isProof_of_sort hΔ HE.hasType.1)
    rw [EA] at E
    cases E
  · intro b c hf hg H
    exact proofErase_joint_union_proposition_head_beta_universe heq hs hΔ hp hp rfl hf hg HR H

end Lean4Lean.VEnv.Strengthening
