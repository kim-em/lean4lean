import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointDomainPullback

/-! # Exact recovered types need not survive forward annotation reduction

A beta-redex annotation reduces to Prop. The fresh non-proof variable then
recovers Prop, but cannot recover the original redex from this normal oracle.
This rules out reversing exact-recovery pullback, even at the full joint union.
It does not rule out computation transport or recovery with a new output.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private not_proof_at_positive_type from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params]
namespace DomainDirection

private def annotation : VExpr := .app (.lam (.sort (.succ .zero)) (.bvar 0)) (.sort .zero)
private def rawAnnotation : ProofShape := .app (.lam (.sort (.succ .zero)) (.bvar 0)) (.sort .zero)
private theorem typed : env.HasType univs Γ annotation (.sort (.succ .zero)) :=
  .app (.lam (.sort (by trivial)) (.bvar .zero)) (.sort (by trivial))

private theorem erased (hΓ : OnCtx Γ (env.IsType univs)) : proofErase Γ annotation = rawAnnotation := by
  have hΓT : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  have hf : env.HasType univs Γ (.lam (.sort (.succ .zero)) (.bvar 0))
      (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) :=
    .lam (.sort (by trivial)) (.bvar .zero)
  change proofErase Γ (.app (.lam (.sort (.succ .zero)) (.bvar 0)) (.sort .zero)) = _
  rw [show proofErase Γ (.app (.lam (.sort (.succ .zero)) (.bvar 0)) (.sort .zero)) = .app _ _ from
    if_neg (not_isProof_of_sort hΓ typed)]
  rw [show proofErase Γ (.lam (.sort (.succ .zero)) (.bvar 0)) = .lam _ _ from
    if_neg (not_isProof_function_to_sort hΓ hf)]
  rw [show proofErase Γ (.sort (.succ .zero)) = .sort (.succ .zero) from
    if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial)))]
  rw [show proofErase (.sort (.succ .zero) :: Γ) (.bvar 0) = .bvar 0 from
    if_neg (not_isProof_of_sort hΓT (HasType.bvar Lookup.zero))]
  rw [show proofErase Γ (.sort .zero) = .sort .zero from
    if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial)))]
  rfl

private theorem no_recovery (D : PureObservation.Definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ¬ ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx (.sort .zero :: Γ))
      (.bvar 0) (contextOracle (proofEraseCtx (annotation :: Γ)) 0) := by
  intro R
  have EP : proofErase Γ (.sort .zero) = .sort .zero :=
    if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial)))
  have RC := R.bvar_compute
  simp only [proofEraseCtx, contextOracle, TypeOracle.cons, EP, erased hΓ,
    rawAnnotation, ProofShape.liftN, liftVar] at RC
  have E := RC.sort_fixed erased_joint_union_head
  cases E

/-- Forward annotation reduction can destroy the exact selected recovery of
an actual typed non-proof variable. The failure holds for every joint stage
simultaneously, even though the annotation reduction itself is stage-zero beta. -/
theorem forward_recovery_failure (D : PureObservation.Definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ A e T out, env.HasType univs Γ A (.sort (.succ .zero)) ∧
      env.HasType univs (A :: Γ) e T ∧ ¬ IsProof (A :: Γ) e ∧
      ScopedCompute (ErasedJointStage D 0) (proofEraseCtx Γ) (proofErase Γ A) (.sort .zero) ∧
      ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx (A :: Γ))
        (proofErase (A :: Γ) e) out ∧
      ¬ ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx (.sort .zero :: Γ))
        (proofErase (.sort .zero :: Γ) e) out := by
  have hΓA : OnCtx (annotation :: Γ) (env.IsType univs) := ⟨hΓ, _, typed⟩
  have hx : env.HasType univs (annotation :: Γ) (.bvar 0) annotation.lift := .bvar .zero
  have hn := not_proof_at_positive_type hΓA (typed.weak henv) hx
  have hΓP : OnCtx (.sort .zero :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  have hn' := not_isProof_of_sort hΓP (show env.HasType univs (.sort .zero :: Γ)
    (.bvar 0) (.sort .zero) from .bvar .zero)
  refine ⟨annotation, .bvar 0, annotation.lift,
    contextOracle (proofEraseCtx (annotation :: Γ)) 0, typed, hx, hn, ?_, ?_, ?_⟩
  · rw [erased hΓ]; exact .beta .beta
  · rw [show proofErase (annotation :: Γ) (.bvar 0) = .bvar 0 from if_neg hn]
    exact .bvar
  · rw [show proofErase (.sort .zero :: Γ) (.bvar 0) = .bvar 0 from if_neg hn']
    exact no_recovery D hΓ

/-- A genuine typed beta reduction of an annotation supports contravariant
stage-zero recovery transport, but its identity map in the forward direction
fails exact image recovery even in the entire joint union. -/
theorem forward_not_recovering (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ A, env.HasType univs Γ A (.sort (.succ .zero)) ∧
      ScopedCompute (ErasedJointStage D 0) (proofEraseCtx Γ)
        (proofErase Γ A) (.sort .zero) ∧
      RecoveringSubstitution (ErasedJointStage D 0)
        (proofEraseCtx (.sort .zero :: Γ)) (proofEraseCtx (A :: Γ)) ProofShape.Subst.id ∧
      ¬ RecoveringSubstitution (ErasedJointUnion D)
        (proofEraseCtx (A :: Γ)) (proofEraseCtx (.sort .zero :: Γ)) ProofShape.Subst.id := by
  have hP : env.HasType univs Γ (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have EP : proofErase Γ (.sort .zero) = .sort .zero := if_neg (not_isProof_of_sort hΓ hP)
  have RA : ScopedCompute (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ annotation) (.sort .zero) := by
    rw [erased hΓ]
    exact .beta .beta
  refine ⟨annotation, typed, RA,
    proofErase_joint_domain_pullback heq hs hΓ typed hP (by simpa only [EP] using RA), ?_⟩
  intro W
  have hΓA : OnCtx (annotation :: Γ) (env.IsType univs) := ⟨hΓ, _, typed⟩
  have hn : ¬ IsProof (annotation :: Γ) (.bvar 0) := by
    have hx : env.HasType univs (annotation :: Γ) (.bvar 0) annotation.lift := .bvar .zero
    exact not_proof_at_positive_type hΓA (typed.weak henv) hx
  have R := W.lookup hΓA rfl Lookup.zero hn
  simp only [ProofShape.subst_id] at R
  simp only [ProofShape.Subst.id] at R
  exact no_recovery D hΓ R

end DomainDirection
end Lean4Lean.VEnv.Strengthening
