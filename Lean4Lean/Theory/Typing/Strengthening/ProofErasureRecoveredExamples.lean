import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredThinning

/-! # Inferred recovered eta beneath a retained binder

The comparison of `fun f => fun x => f x` with `fun f => f` uses inferred mode
at the outer lambda and its body. The short inner endpoint is a variable, so its
Pi type comes from the extended erased context oracle.
-/
namespace Lean4Lean.VEnv.Strengthening.ErasedRecoveredExamples
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions} {stage : Nat}

def expanded (A B : VExpr) : VExpr :=
  .lam (VExpr.forallE A B) (.lam A.lift (.app (.bvar 1) (.bvar 0)))

def identity (A B : VExpr) : VExpr := .lam (VExpr.forallE A B) (.bvar 0)

/-- Both originals have the same function type by ordinary typed eta. -/
theorem originals (hF : env.HasType univs Γ (VExpr.forallE A B) (.sort u)) :
    env.IsDefEq univs Γ (expanded A B) (identity A B)
      (.forallE (VExpr.forallE A B) (VExpr.forallE A B).lift) := by
  have hf : env.HasType univs (VExpr.forallE A B :: Γ) (.bvar 0) (VExpr.forallE A B).lift := .bvar .zero
  exact IsDefEq.lamDF hF (IsDefEq.eta hf)

/-- The inner variable's recovered Pi permits inferred eta at both lambda depths.
Proof-valued functions give the whole-proof or inner-identity alternatives. -/
theorem inferred_comparison (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (VExpr.forallE A B) (.sort u)) :
    ErasedRecoveredComparison D stage false Γ (expanded A B) (identity A B) := by
  have HE := originals hF
  by_cases hp : IsProof Γ (expanded A B)
  · unfold ErasedRecoveredComparison
    rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HE).1 hp)]
    exact .base .refl
  · have hq := mt (isProof_congr hΓ HE).2 hp
    have EL : proofErase Γ (expanded A B) = .lam (proofErase Γ (VExpr.forallE A B))
        (proofErase (VExpr.forallE A B :: Γ) (.lam A.lift (.app (.bvar 1) (.bvar 0)))) := if_neg hp
    have ER : proofErase Γ (identity A B) = .lam (proofErase Γ (VExpr.forallE A B))
        (proofErase (VExpr.forallE A B :: Γ) (.bvar 0)) := if_neg hq
    unfold ErasedRecoveredComparison
    rw [EL, ER]
    apply ProofShape.RecoveredCompare.lam (.base .refl)
    have hΓF : OnCtx (VExpr.forallE A B :: Γ) (env.IsType univs) := ⟨hΓ, u, hF⟩
    have hl : Lookup (VExpr.forallE A B :: Γ) 0 (VExpr.forallE A B).lift := .zero
    have H := proofErase_lookup_eta_forward (Step := ErasedComparedKStage D stage) hΓF hl
    rcases H with H | H
    · change proofErase (VExpr.forallE A B :: Γ) (.lam A.lift (.app (.bvar 1) (.bvar 0))) =
        proofErase (VExpr.forallE A B :: Γ) (.bvar 0) at H
      rw [H]
      exact .base .refl
    · exact H.compare

/-- The nested certificate survives insertion at any depth and still descends to
the original equality through the concrete common-type interface. -/
theorem weakened_descends (stage : Nat) (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (hF : env.HasType univs Γ (VExpr.forallE A B) (.sort u)) :
    env.IsDefEq univs Γ (expanded A B) (identity A B)
      (.forallE (VExpr.forallE A B) (VExpr.forallE A B).lift) := by
  have HE := originals hF
  have H := (inferred_comparison (D := D) (stage := stage) hΓ hF).weakN
    hΓ hΓ' W HE.hasType.1 HE.hasType.2
  exact ErasedRecoveredComparison.common_descendN heq hs hΓ hΓ' W HE.hasType.1 HE.hasType.2
    (ProofShape.RecoveredCompare.common H)

/-- The nested inferred-eta certificate also weakens and descends through an
arbitrary thinning, including several interleaved inserted declarations. -/
theorem thinned_descends (stage : Nat) (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.Lift' ρ Γ Γ') (hF : env.HasType univs Γ (VExpr.forallE A B) (.sort u)) :
    env.IsDefEq univs Γ (expanded A B) (identity A B)
      (.forallE (VExpr.forallE A B) (VExpr.forallE A B).lift) := by
  have HE := originals hF
  have H := (inferred_comparison (D := D) (stage := stage) hΓ hF).weak'
    hΓ hΓ' W HE.hasType.1 HE.hasType.2
  exact ErasedRecoveredComparison.common_descend heq hs hΓ hΓ' W HE.hasType.1 HE.hasType.2
    (ProofShape.RecoveredCompare.common H)

end Lean4Lean.VEnv.Strengthening.ErasedRecoveredExamples
