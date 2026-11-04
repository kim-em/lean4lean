import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeFrameworkContext

/-! # Native binder conversion retaining exact dependent results

Input conversion can change a function annotation while its dependent output
remains exactly aligned. The output need not be a sort or another finite family:
after application, exact native recovery resumes at the instantiated carrier.
-/
namespace Lean4Lean.VEnv.Strengthening.NativeFamilyFramework
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]
variable {D : PureObservation.Definitions} {F : List VExpr → VExpr → Prop} [InputLaws D F]

/-- Any actual target carrier aligned to the source annotation gives a native
identity interpretation of the changed binder. No shape restriction on its
result is required beyond the supplied finite alignment certificate. -/
theorem ImageSubstitution.aligned_context
    (hΓ : OnCtx Γ (env.IsType univs)) (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HB : Alignment D F Γ B (proofErase Γ A)) :
    ImageSubstitution D F (proofEraseCtx (A :: Γ)) (proofEraseCtx (B :: Γ))
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
    have HL : Alignment D F (B :: Γ) B.lift ((proofErase Γ A).liftN 1) := by
      simpa only [← VExpr.lift'_subst, VExpr.subst_id, ← VExpr.lift_eq_lift',
        subst_bvar_liftN] using HB.subst hΓB WB EB HAB.hasType.2
    have hn' : ¬ IsProof (B :: Γ) (.bvar 0) := mt (isProof_defeqCtx HC).2 hn
    have HR : Recovery D F (B :: Γ) (.bvar 0) ((proofErase Γ A).liftN 1) :=
      ⟨B.lift, HasType.bvar .zero, HL, proofErase_scoped_lookup_recovery hΓB .zero hn' .refl⟩
    simpa only [VExpr.Subst.id, proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.subst_id] using HR
  | @succ _ i T _ hl =>
    apply Or.inl
    simp only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.subst_id]
    simpa only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.Subst.id] using
      (ScopedTypeRecovery.bvar (Step := ErasedJointStage D 0)
        (Δ := proofEraseCtx (B :: Γ)) (i := i + 1))

/-- Full recursive carrier checking transports through a changed binder with
exact dependent-result alignment, retaining all source raw syntax. -/
theorem aligned_carrier_context
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HB : Alignment D F Γ B (proofErase Γ A))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) T) (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (B :: Γ))
      (proofErase (A :: Γ) T) (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  simpa only [ProofShape.subst_id] using transport hs H hΓA ha hb rfl rfl rfl rfl
    (ImageSubstitution.aligned_context hΓ HAB HB)

/-- Ordinary recursive comparisons use the same aligned native interpretation. -/
theorem aligned_compare_context
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HB : Alignment D F Γ B (proofErase Γ A))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (B :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  simpa only [ProofShape.subst_id] using transport hs H hΓA ha hb rfl rfl rfl
    (ImageSubstitution.aligned_context hΓ HAB HB)

omit [InputLaws D F] in
/-- Forward core computation of the dependent result suffices as well as
literal agreement. The target result is otherwise unrestricted. -/
theorem Alignment.input_computed_result
    (hΓ : OnCtx Γ (env.IsType univs)) (hSE : env.HasType univs Γ (.forallE S E) (.sort u))
    (HT : F Γ T)
    (RC : Compute (ErasedIotaPrimitive D) (proofErase (T :: Γ) B) (proofErase (S :: Γ) E)) :
    Alignment D F Γ (.forallE T B) (proofErase Γ (.forallE S E)) := by
  rw [show proofErase Γ (.forallE S E) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hSE)]
  exact .input HT (.convert .exact RC)

omit [InputLaws D F] in
/-- Equal input annotations with identical dependent codomain syntax admit
alignment without classifying that codomain. It may depend on the input and
become a function or structure after instantiation. -/
theorem Alignment.equal_input_exact_result
    (hΓ : OnCtx Γ (env.IsType univs)) (HST : env.IsDefEq univs Γ S T (.sort u))
    (HT : F Γ T) (hE : env.HasType univs (S :: Γ) E (.sort v)) :
    Alignment D F Γ (.forallE T E) (proofErase Γ (.forallE S E)) := by
  have hΓS : OnCtx (S :: Γ) (env.IsType univs) := ⟨hΓ, u, HST.hasType.1⟩
  have HC : IsDefEqCtx env univs [] (S :: Γ) (T :: Γ) := .succ (.refl hΓ) HST
  rw [show proofErase Γ (.forallE S E) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ (HasType.forallE HST.hasType.1 hE)),
    proofErase_defeqCtx hΓS HC hE]
  exact .input HT .exact

/-- A concrete binder-conversion criterion for functions with arbitrary
unchanged dependent outputs, discharged by the certified actual input alone. -/
theorem equal_input_carrier_context
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (HST : env.IsDefEq univs Γ S T (.sort u)) (HT : F Γ T)
    (hE : env.HasType univs (S :: Γ) E (.sort v))
    (ha : env.HasType univs (.forallE S E :: Γ) a C)
    (hb : env.HasType univs (.forallE S E :: Γ) b C)
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (.forallE S E :: Γ))
      (proofErase (.forallE S E :: Γ) C) (proofErase (.forallE S E :: Γ) a)
      (proofErase (.forallE S E :: Γ) b)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (.forallE T E :: Γ))
      (proofErase (.forallE S E :: Γ) C) (proofErase (.forallE S E :: Γ) a)
      (proofErase (.forallE S E :: Γ) b) :=
  aligned_carrier_context hs hΓ (IsDefEq.forallEDF HST hE)
    (Alignment.equal_input_exact_result hΓ HST HT hE) ha hb H

end Lean4Lean.VEnv.Strengthening.NativeFamilyFramework
