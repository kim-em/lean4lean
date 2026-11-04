import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointAnchoredSubstitution

/-! # Recursive checking under neutral-typed substitution and context conversion

The selected output may be neutral even when the image has no native recovery
at that output. The terminal case carries this information through checking.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Every value at a neutral assigned type transports all common-typed
recursive comparisons. No recovery of the value at that type is needed. -/
theorem proofErase_computed_joint_zero_compare_inst_neutral
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p T) (HT : AnchoredCarrier 0 (proofErase Γ T))
    (ha : env.HasType univs (T :: Γ) a A) (hb : env.HasType univs (T :: Γ) b A)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (T :: Γ)) mode
      (proofErase (T :: Γ) a) (proofErase (T :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) :=
  proofErase_computed_joint_zero_compare_inst_anchored hs hΓ hp
    (AnchoredFamilyRecovery.neutral HT) ha hb H

/-- Converting a binder with neutral source annotation gives an interpreted
anchored-image identity substitution. The target annotation need only be
ordinarily equal and typed; no computational annotation join is required. -/
theorem AnchoredImageSubstitution.neutral_context
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HA : AnchoredCarrier 0 (proofErase Γ A)) :
    AnchoredImageSubstitution D (proofEraseCtx (A :: Γ)) (proofEraseCtx (B :: Γ))
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
  apply AnchoredImageSubstitution.of_typed (cut := 0) hΓB W ES
  intro i T hl _
  cases hl with
  | zero =>
    apply Or.inr
    refine ⟨0, .neutral ?_⟩
    simp only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.subst_id]
    obtain ⟨i, args, hi, E⟩ := HA
    rw [E]
    refine ⟨1 + i, args.map (·.liftN 1), by omega, ?_⟩
    simp only [ProofShape.liftN_mkApps, ProofShape.liftN, liftVar, Nat.not_lt_zero, ↓reduceIte]
  | @succ _ i T _ hl =>
    apply Or.inl
    simp only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.subst_id]
    simpa only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.Subst.id] using
      (ScopedTypeRecovery.bvar (Step := ErasedJointStage D 0)
        (Δ := proofEraseCtx (B :: Γ)) (i := i + 1))

/-- Full recursive comparison survives conversion of a neutral source binder.
The raw expression endpoints are unchanged, while the context oracle changes. -/
theorem proofErase_computed_joint_zero_neutral_context
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HA : AnchoredCarrier 0 (proofErase Γ A))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (B :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  simpa only [ProofShape.subst_id] using H.transport_anchoredImages hs hΓA ha hb rfl rfl rfl
    (AnchoredImageSubstitution.neutral_context hΓ HAB HA)

/-- Carrier checking survives the same neutral-source context conversion,
retaining the raw carrier and endpoint syntax. -/
theorem proofErase_computed_joint_zero_carrier_neutral_context
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HA : AnchoredCarrier 0 (proofErase Γ A))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) T) (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (B :: Γ))
      (proofErase (A :: Γ) T) (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  simpa only [ProofShape.subst_id] using H.transport_anchoredImages hs hΓA ha hb rfl rfl rfl rfl
    (AnchoredImageSubstitution.neutral_context hΓ HAB HA)

/-- A finite function-body guard changes its neutral domain along any actual
type equality. This consumes the retained body and its typed realizations;
it does not infer body coverage from arbitrary whole-function equality. -/
theorem proofErase_computed_joint_function_neutral_domain
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HA : AnchoredCarrier 0 (proofErase Γ A))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (Ea : proofErase (A :: Γ) a = .app (f.liftN 1) (etaArgument u))
    (Eb : proofErase (A :: Γ) b = .app (g.liftN 1) (etaArgument u))
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) T) (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (.forallE (proofErase Γ B) (proofErase (A :: Γ) T)) f g := by
  have HB := proofErase_computed_joint_zero_carrier_neutral_context hs hΓ HAB HA ha hb H
  rw [Ea, Eb] at HB
  exact .carrierFunction (DomainSort.of_typed hΓ HAB.hasType.2) HB

end Lean4Lean.VEnv.Strengthening
