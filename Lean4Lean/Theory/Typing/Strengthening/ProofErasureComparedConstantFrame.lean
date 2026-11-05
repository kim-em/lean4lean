import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStageZeroSortExposure

/-! # Remove a compared constant control frame while retaining its body check

A constant frame's fixed argument is Prop. A compared sort-typed argument
computes to that exact sort, so native-image substitution can use a single
argument on both sides of the body check. Its lambda annotation is discarded
by beta and does not need a reverse computation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- A compared constant-frame argument computes to Prop, and the body check
survives contraction using Prop's exact native image. The body comparison is
supplied under the fixed Type binder; obtaining it through an arbitrary
computed function comparison remains a separate obligation. The raw right
lambda domain is unrestricted because beta discards it. -/
theorem stage_zero_compared_constant_frame
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a T)
    (hb : env.HasType univs (.sort (.succ .zero) :: Γ) b T.lift)
    (hx : env.HasType univs Γ x (.sort v))
    (HB : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx (.sort (.succ .zero) :: Γ)) false
      (proofErase (.sort (.succ .zero) :: Γ) a.lift)
      (proofErase (.sort (.succ .zero) :: Γ) b))
    (HX : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx Γ) mode (.sort .zero) (proofErase Γ x)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.app (.lam L (proofErase (.sort (.succ .zero) :: Γ) b)) (proofErase Γ x))
      (proofErase Γ (b.inst (.sort .zero))) ∧
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) false
        (proofErase Γ a) (proofErase Γ (b.inst (.sort .zero))) := by
  have hP : env.HasType univs Γ (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have hS : env.HasType univs Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) := .sort (by trivial)
  have hΓS : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType univs) := ⟨hΓ, _, hS⟩
  have EP : proofErase Γ (.sort .zero) = .sort .zero := if_neg (not_isProof_of_sort hΓ hP)
  have ES : proofErase Γ (.sort (.succ .zero)) = .sort (.succ .zero) :=
    if_neg (not_isProof_of_sort hΓ hS)
  have RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (.sort .zero)) (proofErase Γ (.sort (.succ .zero))) := by
    rw [EP, ES]; exact .sort (by trivial)
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := VExpr.sort .zero)
    (A₀ := VExpr.sort (.succ .zero))).substEq hΓS hP
  have WI : StaticStructureEtaNativeSubstitution.ImageSubstitution D 0
      (proofEraseCtx (.sort (.succ .zero) :: Γ)) (proofEraseCtx Γ)
      (ProofShape.Subst.one (proofErase Γ (.sort .zero))) :=
    NativeImageTransport.ImageSubstitution.of_typed hΓ W
      (erasedSubstAgreement_one hΓS hP) (NativeImageTransport.Images.inst RN)
  have HC := StaticStructureEtaNativeSubstitution.check heq hs (k := 0) HB
    hΓS (ha.weak henv) hb rfl rfl rfl WI
  have HC' : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) false
      (proofErase Γ (a.lift.inst (.sort .zero))) (proofErase Γ (b.inst (.sort .zero))) := by
    rw [proofErase_instN hΓS hP Ctx.InstN.zero (ha.weak henv), proofErase_instN hΓS hP Ctx.InstN.zero hb]
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HC
  have RX := stage_zero_compared_sort_returns heq hs hΓ (by trivial) hx HX
  have EB : proofErase Γ (b.inst (.sort .zero)) =
      (proofErase (.sort (.succ .zero) :: Γ) b).inst (.sort .zero) := by
    rw [proofErase_instN hΓS hP Ctx.InstN.zero hb, EP]
  refine ⟨(ScopedCompute.app .refl RX).trans (.beta ?_), ?_⟩
  · rw [EB]; exact .beta
  · simpa only [VExpr.inst_lift] using HC'

end Lean4Lean.VEnv.Strengthening
