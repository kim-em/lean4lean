import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUnusedBodyBeta
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary

/-! # Nonjoining, unrecoverable arguments for the unused-body beta result

Two copies of a neutral variable keep the same native carrier, while their
assigned carrier eta-expands a parameter. Exact recovery at the assigned type
fails for both variables, and distinct variables cannot computationally join.
The unused-body theorem still applies at every finite comparison stage.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private context context_wf native assigned nativeRaw native_typed types_equal
  source_typed erasures normal_forms
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary
open private scoped_normal_fixed from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
open private not_proof_at_positive_type from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params]

private theorem native_variable_not_assigned_recovery (D : PureObservation.Definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ¬ ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx (context Γ))
      (proofErase (context Γ) (.bvar 0)) (proofErase (context Γ) assigned) := by
  have hC := context_wf hΓ
  have hn := not_proof_at_positive_type hC native_typed source_typed
  obtain ⟨EN, EA⟩ := erasures hΓ
  have EO : contextOracle (proofEraseCtx (context Γ)) 0 = nativeRaw := by
    rw [proofEraseCtx_oracle, erasedTypeOracle_valid hC (Lookup.zero (ty := VExpr.app (.bvar 0) (.bvar 1)))]
    exact EN
  intro R
  rw [show proofErase (context Γ) (.bvar 0) = .bvar 0 from if_neg hn] at R
  have HR := R.bvar_compute
  rw [EO] at HR
  have E := scoped_normal_fixed HR
    (fun Δ => (normal_forms (Step := ErasedJointUnion D) erased_joint_union_head Δ).1)
  rw [EA] at E
  cases E

/-- Every well-formed base context admits two typed non-proof variables with
no common computation and no exact assigned-type recovery in the entire union.
Nevertheless all inferred comparisons of their argument-free proposition
lambdas survive paired head beta at the original finite stage. The failed
recoveries are at exactly the displayed lambda domain in this conclusion. -/
theorem proofErase_joint_unused_beta_nonjoining_unrecoverable
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ Δ T, OnCtx Δ (env.IsType univs) ∧
      env.HasType univs Δ (.bvar 0) T ∧ env.HasType univs Δ (.bvar 1) T ∧
      ¬ IsProof Δ (.bvar 0) ∧ ¬ IsProof Δ (.bvar 1) ∧
      (¬ ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Δ)
        (proofErase Δ (.bvar 0)) (proofErase Δ T)) ∧
      (¬ ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Δ)
        (proofErase Δ (.bvar 1)) (proofErase Δ T)) ∧
      (¬ ∃ out, ScopedCompute (ErasedJointUnion D) (proofEraseCtx Δ) (proofErase Δ (.bvar 0)) out ∧
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Δ) (proofErase Δ (.bvar 1)) out) ∧
      ∀ stage {b c : VExpr} {rawB rawC : ProofShape},
        env.HasType univs Δ (.lam T b) (.forallE T (.sort .zero)) →
        env.HasType univs Δ (.lam T c) (.forallE T (.sort .zero)) →
        proofErase (T :: Δ) b = rawB.liftN 1 → proofErase (T :: Δ) c = rawC.liftN 1 →
        JointCompare (ErasedJointStage D stage) (proofEraseCtx Δ) false
          (proofErase Δ (.lam T b)) (proofErase Δ (.lam T c)) →
        JointCompare (ErasedJointStage D stage) (proofEraseCtx Δ) true
          (proofErase Δ (b.inst (.bvar 0))) (proofErase Δ (c.inst (.bvar 1))) := by
  let Δ := native :: context Γ
  have hC := context_wf hΓ
  have hΔ : OnCtx Δ (env.IsType univs) := ⟨hC, _, native_typed⟩
  have W₀ : Ctx.LiftN 1 0 (context Γ) Δ := .one
  have W₁ : Ctx.LiftN 1 1 (context Γ) Δ := Ctx.LiftN.one.succ
  have ht : env.HasType univs (context Γ) (.bvar 0) assigned := types_equal.symm.defeq source_typed
  have hn : ¬ IsProof (context Γ) (.bvar 0) := not_proof_at_positive_type hC native_typed source_typed
  have hx : env.HasType univs Δ (.bvar 0) assigned.lift := ht.weakN henv W₁
  have hy : env.HasType univs Δ (.bvar 1) assigned.lift := ht.weakN henv W₀
  have hnx : ¬ IsProof Δ (.bvar 0) := mt (isProof_liftN hC hΔ W₁ ht).1 hn
  have hny : ¬ IsProof Δ (.bvar 1) := mt (isProof_liftN hC hΔ W₀ ht).1 hn
  have no := native_variable_not_assigned_recovery D hΓ
  have Ex := proofErase_liftN hC hΔ W₁ ht
  have Ey := proofErase_liftN hC hΔ W₀ ht
  have ETx := proofErase_liftN hC hΔ W₁ types_equal.hasType.1
  have ETy := proofErase_liftN hC hΔ W₀ types_equal.hasType.1
  change proofErase Δ (.bvar 0) = _ at Ex
  change proofErase Δ (.bvar 1) = _ at Ey
  change proofErase Δ assigned.lift = _ at ETx ETy
  refine ⟨Δ, assigned.lift, hΔ, hx, hy, hnx, hny, ?_, ?_, ?_, ?_⟩
  · intro R
    apply no
    apply (proofErase_joint_union_recovery_lift_iff heq hs hC hΔ W₁ ht).1
    rwa [← Ex, ← ETx]
  · intro R
    apply no
    apply (proofErase_joint_union_recovery_lift_iff heq hs hC hΔ W₀ ht).1
    rwa [← Ey, ← ETy]
  · rintro ⟨out, RX, RY⟩
    rw [show proofErase Δ (.bvar 0) = .bvar 0 from if_neg hnx] at RX
    rw [show proofErase Δ (.bvar 1) = .bvar 1 from if_neg hny] at RY
    have E := (RX.bvar_fixed erased_joint_union_head).symm.trans (RY.bvar_fixed erased_joint_union_head)
    cases E
  · intro stage b c rawB rawC hf hg Eb Ec H
    exact proofErase_joint_stage_unused_proposition_head_beta heq hs hΔ hx hy hf hg Eb Ec H

end Lean4Lean.VEnv.Strengthening
