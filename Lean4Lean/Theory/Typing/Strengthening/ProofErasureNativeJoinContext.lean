import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeJoinTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTerminalDomainContext

/-! # Binder conversion by computation followed by native family alignment

A source annotation first computes to a selected intermediate carrier. Finite
alignment connects the actual target binder to that carrier, so the complete
checker transports even when neither ingredient alone covers the conversion.
-/
namespace Lean4Lean.VEnv.Strengthening.ErasedQuotCore.NativeJoinFramework
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]
variable {hq : QuotRegistered env} {F : List VExpr → VExpr → Prop}
variable [NativeFamilyFramework.InputLaws (definitions hq) F]

/-- A target carrier aligned to a reduct of the source annotation gives the
combined native identity substitution across the changed binder. -/
theorem ImageSubstitution.aligned_context
    (hΓ : OnCtx Γ (env.IsType univs)) (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HB : NativeFamilyFramework.Alignment (definitions hq) F Γ B mid)
    (RA : Compute (Step hq) (proofErase Γ A) mid) :
    ImageSubstitution hq F (proofEraseCtx (A :: Γ)) (proofEraseCtx (B :: Γ))
      ProofShape.Subst.id := by
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.2⟩
  have HC : IsDefEqCtx env univs [] (A :: Γ) (B :: Γ) := .succ (.refl hΓ) HAB
  have W : Ctx.SubstEq env univs (B :: Γ) VExpr.Subst.id VExpr.Subst.id (A :: Γ) :=
    substEq_source_convert hΓB (HC.symm henv.ordered) (Ctx.SubstEq.id henv.ordered hΓB)
  have ES : ErasedSubstAgreement (A :: Γ) (B :: Γ) VExpr.Subst.id ProofShape.Subst.id := by
    intro i T hl hn
    have hn' : ¬ IsProof (B :: Γ) (.bvar i) := mt (isProof_defeqCtx HC).2 hn
    simp only [VExpr.Subst.id, proofErase, if_neg hn', ProofShape.Subst.id]
  apply ImageSubstitution.of_typed hΓB W ES
  intro i T hl hn
  cases hl with
  | zero =>
    apply Or.inr
    have WB := substEq_of_thinning hΓ (Ctx.Lift'.skip (A := B) .refl)
    have EB : ErasedSubstAgreement Γ (B :: Γ) (fun i => .bvar (i + 1))
        (fun i => .bvar (liftVar 1 i 0)) := by
      intro i C hl hn
      have hx : env.HasType univs Γ (.bvar i) C := .bvar hl
      have EE := proofErase_liftN hΓ hΓB Ctx.LiftN.one hx
      rw [show proofErase Γ (.bvar i) = .bvar i from if_neg hn] at EE
      simpa [VExpr.liftN, ProofShape.liftN, liftVar, Nat.add_comm] using EE
    have HL : NativeFamilyFramework.Alignment (definitions hq) F (B :: Γ) B.lift (mid.liftN 1) := by
      simpa only [← VExpr.lift'_subst, VExpr.subst_id, ← VExpr.lift_eq_lift',
        subst_bvar_liftN] using HB.subst hΓB WB EB HAB.hasType.2
    have hn' : ¬ IsProof (B :: Γ) (.bvar 0) := mt (isProof_defeqCtx HC).2 hn
    have HR : NativeFamilyFramework.Recovery (definitions hq) F (B :: Γ) (.bvar 0) (mid.liftN 1) :=
      ⟨B.lift, HasType.bvar .zero, HL, proofErase_scoped_lookup_recovery hΓB .zero hn' .refl⟩
    simpa only [VExpr.Subst.id, proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.subst_id] using (show Recovery hq F (B :: Γ) (.bvar 0) ((proofErase Γ A).liftN 1) from
        ⟨mid.liftN 1, HR, RA.liftN (fun H => erased_iota_primitive_liftN H)⟩)
  | @succ _ i T _ hl =>
    apply Or.inl
    simp only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.subst_id]
    simpa only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.Subst.id] using
      (ScopedTypeRecovery.bvar (Step := fun _ => Step hq)
        (Δ := proofEraseCtx (B :: Γ)) (i := i + 1))

/-- Full recursive carrier checking transports through a changed binder with
combined dependent-result alignment, retaining all source raw syntax. -/
theorem aligned_carrier_context
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HB : NativeFamilyFramework.Alignment (definitions hq) F Γ B mid)
    (RA : Compute (Step hq) (proofErase Γ A) mid)
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : ComputedJointCarrierGuard (fun _ => Step hq) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) T) (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ComputedJointCarrierGuard (fun _ => Step hq) (proofEraseCtx (B :: Γ))
      (proofErase (A :: Γ) T) (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  simpa only [ProofShape.subst_id] using transport hcon H hΓA ha hb rfl rfl rfl rfl
    (ImageSubstitution.aligned_context hΓ HAB HB RA)

/-- Ordinary recursive comparisons use the same aligned native interpretation. -/
theorem aligned_compare_context
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HB : NativeFamilyFramework.Alignment (definitions hq) F Γ B mid)
    (RA : Compute (Step hq) (proofErase Γ A) mid)
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : ComputedJointCompare (fun _ => Step hq) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ComputedJointCompare (fun _ => Step hq) (proofEraseCtx (B :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  simpa only [ProofShape.subst_id] using transport hcon H hΓA ha hb rfl rfl rfl
    (ImageSubstitution.aligned_context hΓ HAB HB RA)

end Lean4Lean.VEnv.Strengthening.ErasedQuotCore.NativeJoinFramework
