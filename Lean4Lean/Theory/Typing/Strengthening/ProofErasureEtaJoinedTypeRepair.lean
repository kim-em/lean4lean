import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaPiOriginRepair

/-! # Assigned eta repair from a common type reduct

An assigned Pi need not compute to the literal native output. A common reduct
is enough: native conversion follows its own branch, then full eta-aware Pi
origin supplies the component histories from the assigned branch.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Joining an assigned Pi and an existing native type suffices to join the
short function and its assigned eta expansion. Neither type branch needs to
reach the other's original syntax, and both may use arbitrary eta stages. -/
theorem proofErase_eta_union_joined_type_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (RN : ScopedTypeRecovery (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ f) native)
    (RT : ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) common)
    (RU : ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ) native common) :
    ∃ expanded, ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ f) expanded ∧
      ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.lam A (.app f.lift (.bvar 0)))) expanded :=
  proofErase_eta_union_type_path_square heq hs hΓ hA hf (RN.convert RU) RT

/-- Independent finite bounds for native recovery and its continuation are
combined before the eta guard. The assigned branch supplies a finite later
component bound; no relation between the original three bounds is required. -/
theorem proofErase_eta_stage_joined_type_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (RN : ScopedTypeRecovery (ErasedEtaExpansionStage D k) (proofEraseCtx Γ)
      (proofErase Γ f) native)
    (RT : ScopedCompute (ErasedEtaExpansionStage D n) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) common)
    (RU : ScopedCompute (ErasedEtaExpansionStage D m) (proofEraseCtx Γ) native common) :
    ∃ later expanded, n ≤ later ∧
      ScopedCompute (ErasedEtaExpansionStage D (max (max k m + 1) later)) (proofEraseCtx Γ)
        (proofErase Γ f) expanded ∧
      ScopedCompute (ErasedEtaExpansionStage D (max (max k m + 1) later)) (proofEraseCtx Γ)
        (proofErase Γ (.lam A (.app f.lift (.bvar 0)))) expanded := by
  have RN' := RN.mono (fun H => erased_eta_expansion_stage_mono (Nat.le_max_left k m) H)
  have RU' := RU.mono (fun H => erased_eta_expansion_stage_mono (Nat.le_max_right k m) H)
  exact proofErase_eta_stage_type_path_square heq hs hΓ hA hf (RN'.convert RU') RT

end Lean4Lean.VEnv.Strengthening
