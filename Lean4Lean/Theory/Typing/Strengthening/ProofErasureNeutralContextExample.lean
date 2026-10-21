import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralDomainGuard
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointFunctionAlignmentExample

/-! # Neutral input transport where exact recovery is impossible

The eta-different types F (fun p => f p) and F f have no joint computation
join. All certified body checks and all dependent function guards nevertheless
transport between them. Requiring identical recovered outputs would still
fail, even if the target recovery were allowed the entire joint union.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private context native assigned nativeRaw assignedRaw erasures context_wf
  types_equal normal_forms
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary
open private normal_types
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointFunctionAlignmentExample
open private scoped_normal_fixed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
variable [Params]

/-- A checked separation between preserving all joint checks and preserving
each recovered type literally. Actual convertible neutral binders have no
union join, yet their certified body judgments and dependent function guards
are equivalent. A source variable recovery has no identical target output
even with unrestricted union computation. -/
theorem certified_neutral_context_without_exact_recovery
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ Γ' A B, OnCtx Γ' (env.IsType univs) ∧
      env.IsDefEq univs Γ' A B (.sort (.succ .zero)) ∧
      (¬ ∃ shared,
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ') (proofErase Γ' A) shared ∧
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ') (proofErase Γ' B) shared) ∧
      (∀ kind a b,
        JointCheck (ErasedBetaStableJoint D) (proofEraseCtx (A :: Γ')) kind a b ↔
        JointCheck (ErasedBetaStableJoint D) (proofEraseCtx (B :: Γ')) kind a b) ∧
      (∀ C v, env.HasType univs (A :: Γ') C (.sort v) → ∀ a b,
        JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ')
          (proofErase Γ' (.forallE A C)) a b ↔
        JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ')
          (proofErase Γ' (.forallE B C)) a b) ∧
      ∃ out, ScopedTypeRecovery (ErasedBetaStableJoint D) (proofEraseCtx (A :: Γ')) (.bvar 0) out ∧
        ¬ ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx (B :: Γ')) (.bvar 0) out := by
  have hC := context_wf hΓ
  obtain ⟨EN, EA⟩ := erasures hΓ
  have EA' : proofErase (context Γ) assigned = ProofShape.mkApps (.bvar 1)
      [.lam (.sort .zero) (.app (.bvar 3) (.bvar 0))] := EA
  have EN' : proofErase (context Γ) native = ProofShape.mkApps (.bvar 1) [.bvar 2] := EN
  refine ⟨context Γ, assigned, native, hC, types_equal, ?_, ?_, ?_, ?_⟩
  · rintro ⟨shared, RA, RN⟩
    rw [EA] at RA
    rw [EN] at RN
    have HA := scoped_normal_fixed RA (fun Δ =>
      (normal_forms (Step := ErasedJointUnion D) (@erased_joint_union_head _ D) Δ).2)
    have HN := scoped_normal_fixed RN (fun Δ =>
      (normal_forms (Step := ErasedJointUnion D) (@erased_joint_union_head _ D) Δ).1)
    cases HA.symm.trans HN
  · intro kind a b
    exact ⟨proofErase_certified_neutral_context heq hs hC types_equal EA' EN',
      proofErase_certified_neutral_context heq hs hC types_equal.symm EN' EA'⟩
  · intro C v hCod a b
    exact ⟨proofErase_certified_neutral_domain_guard heq hs hC types_equal hCod EA' EN',
      proofErase_certified_neutral_domain_guard heq hs hC types_equal.symm
        (hCod.defeqDFC henv (.succ .zero types_equal)) EN' EA'⟩
  · refine ⟨_, ScopedTypeRecovery.bvar, ?_⟩
    intro R
    have RC := R.bvar_compute
    change ScopedCompute _ _ ((proofErase (context Γ) native).liftN 1)
      ((proofErase (context Γ) assigned).liftN 1) at RC
    rw [EN, EA] at RC
    have HE := scoped_normal_fixed RC (fun Δ =>
      (normal_types (Step := ErasedJointUnion D) (@erased_joint_union_head _ D) Δ).1.2.2)
    cases HE

end Lean4Lean.VEnv.Strengthening
