import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointTestedSubstitution

/-! # Recursive binder conversion at specializable target domains

The generic target value has one actual interpretation making it a type.
Shared-test recovery paths preserve this interpretation through the entire
stage-zero checker, including local beta instantiation under new binders.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- An equal target binder whose generic variable admits a sort specialization
gives a shared-test interpreted identity substitution. The test is carried
through all recursive binders and local beta steps by the transport theorem. -/
theorem TestedImageSubstitution.specialized_context
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HB : SortSpecialization (B :: Γ) (.bvar 0)) :
    TestedImageSubstitution D (proofEraseCtx (A :: Γ)) (proofEraseCtx (B :: Γ))
      ProofShape.Subst.id := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.2⟩
  have HC : IsDefEqCtx env univs [] (A :: Γ) (B :: Γ) :=
    .succ (.refl hΓ) HAB
  have W : Ctx.SubstEq env univs (B :: Γ) VExpr.Subst.id VExpr.Subst.id (A :: Γ) :=
    substEq_source_convert hΓB (HC.symm henv.ordered) (Ctx.SubstEq.id henv.ordered hΓB)
  have ES : ErasedSubstAgreement (A :: Γ) (B :: Γ) VExpr.Subst.id ProofShape.Subst.id := by
    intro i T hl hn
    have hn' : ¬ IsProof (B :: Γ) (.bvar i) := mt (isProof_defeqCtx HC).2 hn
    simp only [VExpr.Subst.id, proofErase, if_neg hn', ProofShape.Subst.id]
  obtain ⟨Γt, ν, v, hΓt, WT, hx⟩ := HB
  apply TestedImageSubstitution.of_typed hΓB W ES hΓt WT
  intro i T hl _
  cases hl with
  | zero =>
    apply Or.inr
    exact ⟨0, .atom hx⟩
  | @succ _ i T _ hl =>
    apply Or.inl
    simp only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.subst_id]
    simpa only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.Subst.id] using
      (ScopedTypeRecovery.bvar (Step := ErasedJointStage D 0)
        (Δ := proofEraseCtx (B :: Γ)) (i := i + 1))

/-- Full recursive comparison survives conversion to a specializable target binder.
The raw expression endpoints are unchanged, while the context oracle changes. -/
theorem proofErase_computed_joint_zero_specialized_context
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HB : SortSpecialization (B :: Γ) (.bvar 0))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (B :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  simpa only [ProofShape.subst_id] using H.transport_testedImages hs hΓA ha hb rfl rfl rfl
    (TestedImageSubstitution.specialized_context hΓ HAB HB)

/-- Carrier checking survives the same specializable-target context conversion,
retaining the raw carrier and endpoint syntax. -/
theorem proofErase_computed_joint_zero_carrier_specialized_context
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HB : SortSpecialization (B :: Γ) (.bvar 0))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) T) (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (B :: Γ))
      (proofErase (A :: Γ) T) (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  simpa only [ProofShape.subst_id] using H.transport_testedImages hs hΓA ha hb rfl rfl rfl rfl
    (TestedImageSubstitution.specialized_context hΓ HAB HB)

end Lean4Lean.VEnv.Strengthening
