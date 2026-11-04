import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJoinedNativeTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTerminalDomainContext

/-! # Context conversion through common carrier reducts

Both binder annotations compute to a common raw type. The target variable
recovers that type, and full substitution transports checking while retaining
the original selected carrier. Neither computation direction between the two
annotations nor a finite carrier-shape restriction is needed.
-/
namespace Lean4Lean.VEnv.Strengthening.ErasedQuotCore.JoinedNative
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]
variable {hq : QuotRegistered env}

/-- A common core reduct of two typed carriers supplies their ordinary
conversion; the join premise does not require conversion to be assumed too. -/
theorem join_defeq
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs Γ B (.sort u))
    (RA : Compute (Step hq) (proofErase Γ A) shared)
    (RB : Compute (Step hq) (proofErase Γ B) shared) :
    env.IsDefEq univs Γ A B (.sort u) := by
  have hstep : ErasedScopedPrimitiveDescent (fun _ => Step hq) :=
    ErasedPrimitiveReplay.toDescent (sound hq) (erased_iota_replay (sound hq))
  exact proofErase_computed_joint_carrier_reflect hstep hΓ hA hB
    (.carrierChecked (.compute (RA.scoped (fun H => .base H))
      (RB.scoped (fun H => .base H)) (.leaf .refl)))

/-- Computationally joined equal binders give an interpreted identity
substitution whose native image outputs meet the original assigned carriers. -/
theorem ImageSubstitution.joined_context
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (RA : Compute (Step hq) (proofErase Γ A) shared)
    (RB : Compute (Step hq) (proofErase Γ B) shared) :
    ImageSubstitution hq (proofEraseCtx (A :: Γ)) (proofEraseCtx (B :: Γ))
      ProofShape.Subst.id := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.2⟩
  have HC : IsDefEqCtx env univs [] (A :: Γ) (B :: Γ) :=
    .succ (.refl hΓ) HAB
  have W : Ctx.SubstEq env univs (B :: Γ) VExpr.Subst.id VExpr.Subst.id (A :: Γ) :=
    substEq_source_convert hΓB (HC.symm henv.ordered) (Ctx.SubstEq.id henv.ordered hΓB)
  have ES : ErasedSubstAgreement (A :: Γ) (B :: Γ) VExpr.Subst.id ProofShape.Subst.id := by
    intro i T hl _hn
    have hn' : ¬ IsProof (B :: Γ) (.bvar i) := mt (isProof_defeqCtx HC).2 _hn
    simp only [VExpr.Subst.id, proofErase, if_neg hn', ProofShape.Subst.id]
  apply ImageSubstitution.of_typed hΓB W ES
  intro i T hl _hn
  cases hl with
  | zero =>
    refine ⟨shared.liftN 1, ?_, ?_⟩
    · apply ScopedTypeRecovery.convert (.bvar (i := 0))
      simpa only [proofEraseCtx, contextOracle, TypeOracle.cons] using
        (RB.liftN (fun H => erased_iota_primitive_liftN H)).scoped (fun H => .base H)
    · simpa only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.subst_id] using
        RA.liftN (fun H => erased_iota_primitive_liftN H)
  | succ hl =>
    refine ⟨_, .bvar, ?_⟩
    simp only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.subst_id]
    exact .refl

/-- Full recursive comparison survives conversion between computationally joined binders.
The raw expression endpoints are unchanged, while the context oracle changes. -/
theorem compare_context
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (RA : Compute (Step hq) (proofErase Γ A) shared)
    (RB : Compute (Step hq) (proofErase Γ B) shared)
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : ComputedJointCompare (fun _ => Step hq) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ComputedJointCompare (fun _ => Step hq) (proofEraseCtx (B :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  simpa only [ProofShape.subst_id] using transport hcon H hΓA ha hb rfl rfl rfl
    (ImageSubstitution.joined_context hΓ HAB RA RB)

/-- Carrier checking survives the same computational context conversion,
retaining the raw carrier and endpoint syntax. -/
theorem carrier_context
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (RA : Compute (Step hq) (proofErase Γ A) shared)
    (RB : Compute (Step hq) (proofErase Γ B) shared)
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : ComputedJointCarrierGuard (fun _ => Step hq) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) T) (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ComputedJointCarrierGuard (fun _ => Step hq) (proofEraseCtx (B :: Γ))
      (proofErase (A :: Γ) T) (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  simpa only [ProofShape.subst_id] using transport hcon H hΓA ha hb rfl rfl rfl rfl
    (ImageSubstitution.joined_context hΓ HAB RA RB)

end Lean4Lean.VEnv.Strengthening.ErasedQuotCore.JoinedNative
