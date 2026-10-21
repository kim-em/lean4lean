import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointBetaExchange

/-! # Substitution joins after computing to a recoverable argument

Recovery of the original image is unnecessary when it computes to an image
recovering its assigned type. Instantiation then produces a common reduct,
rather than preserving the original substituted output by a directed path.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- A body computation survives substitution up to a common computational
output if the argument first computes to an exactly recoverable image. Both
arms meet at the body's raw output instantiated by that computed image. No
exact recovery is assumed for the original image. -/
theorem proofErase_joint_inst_join_computed_recovery
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (RX : ScopedCompute (ErasedJointStage D argumentStage) (proofEraseCtx Γ)
      (proofErase Γ x) image)
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedJointStage D recoveryStage)
      (proofEraseCtx Γ) image (proofErase Γ A))
    (RB : ScopedCompute (ErasedJointStage D bodyStage) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) out) :
    let later := max argumentStage (recoveryStage + bodyStage)
    ScopedCompute (ErasedJointStage D later) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (out.inst image) ∧
    ScopedCompute (ErasedJointStage D later) (proofEraseCtx Γ)
      (out.inst (proofErase Γ x)) (out.inst image) := by
  have hΓ := hΓA.1
  have WX : Ctx.LiftN 0 0 Γ Γ := .zero []
  obtain ⟨x', HX, EX⟩ := proofErase_scoped_compute_descend
    (erased_joint_stage_descent heq hs argumentStage) hΓ hΓ WX hx rfl
    (by simpa only [ProofShape.liftN_zero] using RX)
  simp only [ProofShape.liftN_zero] at EX
  have HR' : ¬ IsProof Γ x' → ScopedTypeRecovery (ErasedJointStage D recoveryStage)
      (proofEraseCtx Γ) (proofErase Γ x') (proofErase Γ A) := by
    intro hn
    rw [EX]
    apply HR
    exact fun hp => hn ((isProof_congr hΓ HX).1 hp)
  have Rfirst := proofErase_joint_compute_inst_argument heq hs hΓA hb hx RX
  have Rnext := proofErase_joint_compute_inst_recoverable heq hs hΓ HX.hasType.2 HR' hb RB
  rw [proofErase_instN hΓA HX.hasType.2 Ctx.InstN.zero hb, EX] at Rnext
  have WB : Ctx.LiftN 0 0 (A :: Γ) (A :: Γ) := .zero []
  obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_descend
    (erased_joint_stage_descent heq hs bodyStage) hΓA hΓA WB hb rfl
    (by simpa only [ProofShape.liftN_zero] using RB)
  simp only [ProofShape.liftN_zero] at EB
  have Rlast := proofErase_joint_compute_inst_argument heq hs hΓA HB.hasType.2 hx RX
  rw [proofErase_instN hΓA hx Ctx.InstN.zero HB.hasType.2, EB] at Rlast
  exact ⟨(Rfirst.mono (erased_joint_stage_mono (Nat.le_max_left _ _))).trans
    (Rnext.mono (erased_joint_stage_mono (Nat.le_max_right _ _))),
    Rlast.mono (erased_joint_stage_mono (Nat.le_max_left _ _))⟩

/-- The head-beta overlap also closes when the computed argument, rather than
the original one, recovers the displayed domain. This alternative permits
original arguments that have no exact recovery at any joint stage. -/
theorem proofErase_joint_beta_exchange_computed_recovery
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.lam A b))
    (RF : ScopedCompute (ErasedJointStage D stage) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) functionOut)
    (RX : ScopedCompute (ErasedJointStage D stage) (proofEraseCtx Γ)
      (proofErase Γ x) argumentOut)
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedJointStage D imageStage)
      (proofEraseCtx Γ) argumentOut (proofErase Γ A)) :
    ∃ later A' bodyOut, stage ≤ later ∧ functionOut = .lam A' bodyOut ∧
      ScopedCompute (ErasedJointStage D later) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) (bodyOut.inst argumentOut) ∧
      ProofShape.BetaRed (.app functionOut argumentOut) (bodyOut.inst argumentOut) := by
  obtain ⟨bodyStage, A', bodyOut, hstage, rfl, _, RB⟩ :=
    proofErase_joint_lam_inv_later heq hs hΓ hA hb hn RF
  have H := proofErase_joint_inst_join_computed_recovery heq hs
    (show OnCtx (A :: Γ) (env.IsType univs) from ⟨hΓ, u, hA⟩) hb hx RX HR RB
  exact ⟨max stage (imageStage + bodyStage), A', bodyOut, Nat.le_max_left _ _, rfl, H.1, .beta⟩

/-- Either joint comparison mode instantiates at an argument that computes to
an exactly recoverable image. Endpoint computations restore the original
instantiated endpoints, so the conclusion compares those exact endpoints. -/
theorem proofErase_joint_compare_inst_computed_recovery
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (hx : env.HasType univs Γ x A)
    (RX : ScopedCompute (ErasedJointStage D argumentStage) (proofEraseCtx Γ)
      (proofErase Γ x) image)
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedJointStage D recoveryStage)
      (proofEraseCtx Γ) image (proofErase Γ A))
    (H : JointCompare (ErasedJointStage D stage) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    JointCompare (ErasedJointStage D (max argumentStage (recoveryStage + stage)))
      (proofEraseCtx Γ) mode (proofErase Γ (a.inst x)) (proofErase Γ (b.inst x)) := by
  have hΓ := hΓA.1
  have WX : Ctx.LiftN 0 0 Γ Γ := .zero []
  obtain ⟨x', HX, EX⟩ := proofErase_scoped_compute_descend
    (erased_joint_stage_descent heq hs argumentStage) hΓ hΓ WX hx rfl
    (by simpa only [ProofShape.liftN_zero] using RX)
  simp only [ProofShape.liftN_zero] at EX
  have HR' : ¬ IsProof Γ x' → ScopedTypeRecovery (ErasedJointStage D recoveryStage)
      (proofEraseCtx Γ) (proofErase Γ x') (proofErase Γ A) := by
    intro hn
    rw [EX]
    exact HR (fun hp => hn ((isProof_congr hΓ HX).1 hp))
  have H' := proofErase_joint_compare_inst_recoverable heq hs hΓ HX.hasType.2 HR' ha hb H
  rw [proofErase_instN hΓA HX.hasType.2 Ctx.InstN.zero ha,
    proofErase_instN hΓA HX.hasType.2 Ctx.InstN.zero hb, EX] at H'
  exact .compute
    ((proofErase_joint_compute_inst_argument heq hs hΓA ha hx RX).mono
      (erased_joint_stage_mono (Nat.le_max_left _ _)))
    ((proofErase_joint_compute_inst_argument heq hs hΓA hb hx RX).mono
      (erased_joint_stage_mono (Nat.le_max_left _ _)))
    (H'.mono (erased_joint_stage_mono (Nat.le_max_right _ _)))

/-- Full joint carrier checking also instantiates at computed recoverable
images. The carrier and both endpoints compute together, retaining the exact
original substituted carrier and endpoints in the resulting certificate. -/
theorem proofErase_joint_carrier_inst_computed_recovery
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (hx : env.HasType univs Γ x A)
    (RX : ScopedCompute (ErasedJointStage D argumentStage) (proofEraseCtx Γ)
      (proofErase Γ x) image)
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedJointStage D recoveryStage)
      (proofEraseCtx Γ) image (proofErase Γ A))
    (H : JointCarrierGuard (ErasedJointStage D stage) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) T) (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    JointCarrierGuard (ErasedJointStage D (max argumentStage (recoveryStage + stage)))
      (proofEraseCtx Γ) (proofErase Γ (T.inst x))
      (proofErase Γ (a.inst x)) (proofErase Γ (b.inst x)) := by
  have hΓ := hΓA.1
  have WX : Ctx.LiftN 0 0 Γ Γ := .zero []
  obtain ⟨x', HX, EX⟩ := proofErase_scoped_compute_descend
    (erased_joint_stage_descent heq hs argumentStage) hΓ hΓ WX hx rfl
    (by simpa only [ProofShape.liftN_zero] using RX)
  simp only [ProofShape.liftN_zero] at EX
  have HR' : ¬ IsProof Γ x' → ScopedTypeRecovery (ErasedJointStage D recoveryStage)
      (proofEraseCtx Γ) (proofErase Γ x') (proofErase Γ A) := by
    intro hn
    rw [EX]
    exact HR (fun hp => hn ((isProof_congr hΓ HX).1 hp))
  obtain ⟨u, hT⟩ := ha.isType henv hΓA
  have H' := proofErase_joint_carrier_inst_recoverable heq hs hΓ HX.hasType.2 HR' ha hb H
  rw [proofErase_instN hΓA HX.hasType.2 Ctx.InstN.zero hT,
    proofErase_instN hΓA HX.hasType.2 Ctx.InstN.zero ha,
    proofErase_instN hΓA HX.hasType.2 Ctx.InstN.zero hb, EX] at H'
  exact .carrierCompute
    ((proofErase_joint_compute_inst_argument heq hs hΓA hT hx RX).mono
      (erased_joint_stage_mono (Nat.le_max_left _ _)))
    (.carrierReduce
      ((proofErase_joint_compute_inst_argument heq hs hΓA ha hx RX).mono
        (erased_joint_stage_mono (Nat.le_max_left _ _)))
      ((proofErase_joint_compute_inst_argument heq hs hΓA hb hx RX).mono
        (erased_joint_stage_mono (Nat.le_max_left _ _)))
      (H'.mono (erased_joint_stage_mono (Nat.le_max_right _ _))))

end Lean4Lean.VEnv.Strengthening
