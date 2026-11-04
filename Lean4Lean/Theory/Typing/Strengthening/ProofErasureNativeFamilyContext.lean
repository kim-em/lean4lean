import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointNativeAlignedSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTerminalDomainContext

/-! # Binder conversion to native family trees

The generic target value natively recovers the new binder type. Alignment
retains the old selected output while allowing all recursive checker rules
to use the actual recovered domains, including higher-order inputs.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- An equal target binder with a native family tree gives an
interpreted identity substitution, using aligned native variable recovery. -/
theorem NativeAlignedImageSubstitution.nativeFamily_context
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HB : NativeFamilyTree Γ B) :
    NativeAlignedImageSubstitution D (proofEraseCtx (A :: Γ)) (proofEraseCtx (B :: Γ))
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
  apply NativeAlignedImageSubstitution.of_typed hΓB W ES
  intro i T hl hn
  cases hl with
  | zero =>
    apply Or.inr
    have HBlift : NativeFamilyTree (B :: Γ) B.lift := by
      have WB := substEq_of_thinning hΓ (Ctx.Lift'.skip (A := B) .refl)
      simpa only [← VExpr.lift'_subst, VExpr.subst_id, ← VExpr.lift_eq_lift'] using
        HB.subst hΓB WB HAB.hasType.2
    exact (NativeFamilyImage.bvar (D := D) (cut := 0) hΓB .zero HBlift (Nat.le_refl 0)
      (mt (isProof_defeqCtx HC).2 hn)).aligned
  | @succ _ i T _ hl =>
    apply Or.inl
    simp only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.subst_id]
    simpa only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.Subst.id] using
      (ScopedTypeRecovery.bvar (Step := ErasedJointStage D 0)
        (Δ := proofEraseCtx (B :: Γ)) (i := i + 1))

/-- Full recursive comparison survives conversion to a native family target binder.
The raw expression endpoints are unchanged, while the context oracle changes. -/
theorem proofErase_computed_joint_zero_nativeFamily_context
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HB : NativeFamilyTree Γ B)
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (B :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  simpa only [ProofShape.subst_id] using H.transport_nativeAlignedImages hs hΓA ha hb rfl rfl rfl
    (NativeAlignedImageSubstitution.nativeFamily_context hΓ HAB HB)

/-- Carrier checking survives the same native family context conversion,
retaining the raw carrier and endpoint syntax. -/
theorem proofErase_computed_joint_zero_carrier_nativeFamily_context
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HB : NativeFamilyTree Γ B)
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) T) (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (B :: Γ))
      (proofErase (A :: Γ) T) (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  simpa only [ProofShape.subst_id] using H.transport_nativeAlignedImages hs hΓA ha hb rfl rfl rfl rfl
    (NativeAlignedImageSubstitution.nativeFamily_context hΓ HAB HB)

end Lean4Lean.VEnv.Strengthening
