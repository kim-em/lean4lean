import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecoverableInstantiation

/-! # A genuine non-proof lambda image for joint substitution

The identity on propositions recovers its native Pi at stage zero, so it
instantiates every joint stage without increasing the bound. It is not a
retained renaming, whose non-proof images must be variables.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]
namespace RecoverableLambda

private def type : VExpr := .forallE (.sort .zero) (.sort .zero)
private def value : VExpr := .lam (.sort .zero) (.bvar 0)
private theorem typed : env.HasType univs Γ value type := .lam (.sort (by trivial)) (.bvar .zero)
private theorem type_typed : env.HasType univs Γ type (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .forallE (.sort (by trivial)) (.sort (by trivial))

private theorem erase_value (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase Γ value = .lam (.sort .zero) (.bvar 0) := by
  have hΓP : OnCtx (.sort .zero :: Γ) (env.IsType univs) := ⟨hΓ, _, HasType.sort (by trivial)⟩
  change proofErase Γ (.lam (.sort .zero) (.bvar 0)) = _
  rw [show proofErase Γ (.lam (.sort .zero) (.bvar 0)) = .lam _ _ from
    if_neg (not_isProof_function_to_sort hΓ typed)]
  rw [show proofErase Γ (.sort .zero) = .sort .zero from
    if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial)))]
  rw [show proofErase (.sort .zero :: Γ) (.bvar 0) = .bvar 0 from
    if_neg (not_isProof_of_sort hΓP (HasType.bvar Lookup.zero))]

private theorem recovered (hΓ : OnCtx Γ (env.IsType univs)) :
    ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ value) (proofErase Γ type) := by
  have hΓP : OnCtx (.sort .zero :: Γ) (env.IsType univs) := ⟨hΓ, _, HasType.sort (by trivial)⟩
  rw [erase_value hΓ]
  change ScopedTypeRecovery Step (proofEraseCtx Γ) _ (proofErase Γ (.forallE (.sort .zero) (.sort .zero)))
  rw [show proofErase Γ (.forallE (.sort .zero) (.sort .zero)) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ type_typed)]
  rw [show proofErase Γ (.sort .zero) = .sort .zero from
    if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial)))]
  rw [show proofErase (.sort .zero :: Γ) (.sort .zero) = .sort .zero from
    if_neg (not_isProof_of_sort hΓP (HasType.sort (by trivial)))]
  exact .lam .bvar

/-- In every well-formed context there is an actual non-proof lambda image
whose stage-zero exact recovery supplies the new substitution invariant, while
the same raw substitution cannot satisfy retained renaming. -/
theorem strict_extension (D : PureObservation.Definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ p P, env.HasType univs Γ p P ∧ ¬ IsProof Γ p ∧
      ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ P) ∧
      RecoveringSubstitution (ErasedJointStage D 0) (proofEraseCtx (P :: Γ)) (proofEraseCtx Γ)
        (ProofShape.Subst.one (proofErase Γ p)) ∧
      ¬ RetainedRenaming (proofEraseCtx (P :: Γ)) (proofEraseCtx Γ)
        (ProofShape.Subst.one (proofErase Γ p)) := by
  have hΓT : OnCtx (type :: Γ) (env.IsType univs) := ⟨hΓ, _, type_typed⟩
  have hv : env.HasType univs (type :: Γ) (.bvar 0) type := .bvar .zero
  refine ⟨value, type, typed, not_isProof_function_to_sort hΓ typed, recovered hΓ,
    RecoveringSubstitution.inst hΓ typed (fun _ => recovered hΓ), ?_⟩
  intro WR
  obtain ⟨j, Ej, _⟩ := WR.lookup hΓT rfl Lookup.zero (not_isProof_function_to_sort hΓT hv)
  simp only [ProofShape.Subst.one, ProofShape.Subst.cons, erase_value hΓ] at Ej
  cases Ej

/-- Substitution of the proposition identity into any typed body computation
keeps its finite joint stage. Its exact recovery premise is discharged here. -/
theorem compute_inst_identity (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs (.forallE (.sort .zero) (.sort .zero) :: Γ) e T)
    (R : ScopedCompute (ErasedJointStage D stage)
      (proofEraseCtx (.forallE (.sort .zero) (.sort .zero) :: Γ))
      (proofErase (.forallE (.sort .zero) (.sort .zero) :: Γ) e) out) :
    ScopedCompute (ErasedJointStage D stage) (proofEraseCtx Γ)
      (proofErase Γ (e.inst (.lam (.sort .zero) (.bvar 0))))
      (out.inst (.lam (.sort .zero) (.bvar 0))) := by
  have H := proofErase_joint_compute_inst_recoverable (imageStage := 0) heq hs hΓ
    (typed (Γ := Γ)) (fun _ => recovered hΓ) he R
  rw [erase_value hΓ] at H
  simpa only [Nat.zero_add, value] using H

end RecoverableLambda
end Lean4Lean.VEnv.Strengthening
