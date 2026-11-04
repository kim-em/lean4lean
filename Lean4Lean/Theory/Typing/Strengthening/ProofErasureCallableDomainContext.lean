import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointCallableSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTerminalDomainContext

/-! # Binder conversion at callable and projectable domains

The generic target value carries an actual finite elimination tree. Independent
recovery paths transport the whole checker through the converted binder without
using SelectedLambdaDomain or its structural recovery consumers.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- The generic value at this domain has an actual typed call/projection tree.
This is a structural image certificate, not an assumed transport theorem. -/
def CallableDomain (Γ : List VExpr) (A : VExpr) : Prop :=
  TypeInputImage (A :: Γ) (.bvar 0)

/-- Actual typed substitution preserves the generic target certificate. -/
theorem CallableDomain.subst (H : CallableDomain Γ A)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (hA : env.HasType univs Γ A (.sort u)) : CallableDomain Γ₀ (A.subst σ) := by
  have hΓA : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) :=
    ⟨hΓ₀, u, hA.subst henv.orderedStrong W hΓ₀⟩
  exact (show TypeInputImage (A :: Γ) (.bvar 0) from H).subst (σ := σ.lift) hΓA (W.lift henv.ordered hA)

/-- A finite tree on the actual domain certifies its generic value. -/
theorem CallableDomain.of_tree (H : TypeInputTree env A) : CallableDomain Γ A :=
  .typed (HasType.bvar .zero) H.lift

/-- Terminal-valued domains are included in the call/projection certificate. -/
theorem TerminalDomain.callable (H : TerminalDomain Γ A) : CallableDomain Γ A :=
  .projection (.closed (.terminal H))

/-- An equal target binder with a callable/projectable generic value gives an
interpreted identity substitution, independently of selected-domain conversion. -/
theorem CallableImageSubstitution.callable_context
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HB : CallableDomain Γ B) :
    CallableImageSubstitution D (proofEraseCtx (A :: Γ)) (proofEraseCtx (B :: Γ))
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
  apply CallableImageSubstitution.of_typed hΓB W ES
  intro i T hl _
  cases hl with
  | zero =>
    apply Or.inr
    exact ⟨0, .atom HB⟩
  | @succ _ i T _ hl =>
    apply Or.inl
    simp only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.subst_id]
    simpa only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.Subst.id] using
      (ScopedTypeRecovery.bvar (Step := ErasedJointStage D 0)
        (Δ := proofEraseCtx (B :: Γ)) (i := i + 1))

/-- Full recursive comparison survives conversion to a callable/projectable target binder.
The raw expression endpoints are unchanged, while the context oracle changes. -/
theorem proofErase_computed_joint_zero_callable_context
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HB : CallableDomain Γ B)
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (B :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  simpa only [ProofShape.subst_id] using H.transport_callableImages hs hΓA ha hb rfl rfl rfl
    (CallableImageSubstitution.callable_context hΓ HAB HB)

/-- Carrier checking survives the same callable/projectable-target context conversion,
retaining the raw carrier and endpoint syntax. -/
theorem proofErase_computed_joint_zero_carrier_callable_context
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HB : CallableDomain Γ B)
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) T) (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (B :: Γ))
      (proofErase (A :: Γ) T) (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  simpa only [ProofShape.subst_id] using H.transport_callableImages hs hΓA ha hb rfl rfl rfl rfl
    (CallableImageSubstitution.callable_context hΓ HAB HB)

end Lean4Lean.VEnv.Strengthening
