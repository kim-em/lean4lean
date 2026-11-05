import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedLambdaBody

/-! # The application boundary in inferred lambda-body extraction

Literal structural and displayed-eta boundaries have already been discharged.
An induction on the complete comparison grammar isolates the three application
constructors; outer computation and symmetry retain the original histories.
This is a conditional reduction, not a proof of its application premise or a
claim of a strictly smaller sufficient obligation for strengthening.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- The unresolved application case of inferred lambda-body extraction.
Two original lambdas compute to applications. Their functions compare in
inferred mode, and arguments have one of the grammar's three exact checks.
What remains to prove is a comparison of the original bodies under their
original common binder, allowing arbitrary generated wrappers and interleavings.
This interface is not asserted to be strictly smaller than PropFront. -/
def StageZeroLambdaApplicationExtraction (D : PureObservation.Definitions) : Prop :=
  ∀ {Γ C u a b T f g x y}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ C (.sort u) →
    env.HasType univs (C :: Γ) a T → env.HasType univs (C :: Γ) b T →
    ¬ IsProof Γ (.lam C a) → ¬ IsProof Γ (.lam C b) →
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.lam (proofErase Γ C) (proofErase (C :: Γ) a)) (.app f x) →
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.lam (proofErase Γ C) (proofErase (C :: Γ) b)) (.app g y) →
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) false f g →
    (ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) true x y ∨
      (∃ A B, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) f (.forallE A B) ∧
        ComputedJointCarrierGuard (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) A x y) ∨
      (∃ A body, ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) f (.lam A body) ∧
        ComputedJointCarrierGuard (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) A x y)) →
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (C :: Γ)) false
      (proofErase (C :: Γ) a) (proofErase (C :: Γ) b)

private theorem inferred_body_of_application_boundary
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (happ : StageZeroLambdaApplicationExtraction D)
    (H : ComputedJointCheck (ErasedStaticStructureEtaExpansionStage D 0) Δ kind sa sb)
    (hk : kind = .compare false)
    (hΓ : OnCtx Γ (env.IsType univs)) (hC : env.HasType univs Γ C (.sort u))
    (ha : env.HasType univs (C :: Γ) a T) (hb : env.HasType univs (C :: Γ) b T)
    (hna : ¬ IsProof Γ (.lam C a)) (hnb : ¬ IsProof Γ (.lam C b))
    (EΓ : proofEraseCtx Γ = Δ)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.lam (proofErase Γ C) (proofErase (C :: Γ) a)) sa)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.lam (proofErase Γ C) (proofErase (C :: Γ) b)) sb) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (C :: Γ)) false
      (proofErase (C :: Γ) a) (proofErase (C :: Γ) b) := by
  induction H generalizing Γ C u a b T with
  | leaf H =>
    cases hk
    cases H with
    | refl => exact (proofErase_stage_zero_lambda_join_compares heq hs hΓ hC ha hC hb hna hnb RA RB
        (domainMode := false)).2
    | sort => exact (proofErase_stage_zero_lambda_observation heq hs hΓ hC ha hna RA).not_sort.elim
    | const => exact ((proofErase_stage_zero_lambda_observation heq hs hΓ hC ha hna RA).not_primitiveHead trivial).elim
  | app HF HX _ _ =>
    exact happ hΓ hC ha hb hna hnb RA RB (EΓ ▸ HF) (.inl (EΓ ▸ HX))
  | appCarrier RN HF HX _ _ =>
    exact happ hΓ hC ha hb hna hnb RA RB (EΓ ▸ HF) (.inr (.inl ⟨_, _, EΓ ▸ RN, EΓ ▸ HX⟩))
  | appComputed RF HF HX _ _ =>
    exact happ hΓ hC ha hb hna hnb RA RB (EΓ ▸ HF) (.inr (.inr ⟨_, _, EΓ ▸ RF, EΓ ▸ HX⟩))
  | proj => exact (proofErase_stage_zero_lambda_observation heq hs hΓ hC ha hna RA).not_proj.elim
  | lam HD HB _ _ | lamSorted _ _ HD HB _ _ =>
    cases hk
    exact stage_zero_computed_lambda_body_compare heq hs hΓ hC ha hb hna hnb RA RB (EΓ ▸ HB)
  | forallE | forallSorted =>
    exact (proofErase_stage_zero_lambda_observation heq hs hΓ hC ha hna RA).not_forallE.elim
  | etaLams HD HE _ =>
    exact stage_zero_computed_lambda_eta_body_compare heq hs hΓ hC ha hb hna hnb RA RB HE
  | compute R₁ R₂ HC ih =>
    exact ih hk hΓ hC ha hb hna hnb EΓ (RA.trans (EΓ ▸ R₁)) (RB.trans (EΓ ▸ R₂))
  | symm HC ih => exact (ih hk hΓ hC hb ha hnb hna EΓ RB RA).symm
  | lamCommon | etaBodyL | etaBodyR | structFields | carrierIntro | carrierChecked |
      carrierSubsingleton | carrierFunction | carrierSymm | carrierCompute | carrierReduce |
      carrierNested => cases hk

/-- The application boundary suffices for all inferred comparisons between
computed original lambdas. The proof handles every constructor, including
arbitrary outer computation and symmetry; the application premise remains
unproved and carries precisely the remaining three structural application cases. -/
theorem stage_zero_inferred_lambda_body_of_applications
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (happ : StageZeroLambdaApplicationExtraction D)
    (hΓ : OnCtx Γ (env.IsType univs)) (hC : env.HasType univs Γ C (.sort u))
    (ha : env.HasType univs (C :: Γ) a T) (hb : env.HasType univs (C :: Γ) b T)
    (hna : ¬ IsProof Γ (.lam C a)) (hnb : ¬ IsProof Γ (.lam C b))
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.lam (proofErase Γ C) (proofErase (C :: Γ) a)) f)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.lam (proofErase Γ C) (proofErase (C :: Γ) b)) g)
    (H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) false f g) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (C :: Γ)) false
      (proofErase (C :: Γ) a) (proofErase (C :: Γ) b) :=
  inferred_body_of_application_boundary heq hs happ H rfl hΓ hC ha hb hna hnb rfl RA RB

end Lean4Lean.VEnv.Strengthening
