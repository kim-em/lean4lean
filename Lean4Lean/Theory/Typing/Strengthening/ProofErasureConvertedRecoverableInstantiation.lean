import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointRecoverableInstantiation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedNeutralStageContext

/-! # Higher-stage instantiation at a convertible recoverable type

The assigned type may lack exact image recovery. A recursive neutral context
conversion moves the body to an equal type at which the image recovers. Both
stages are finite, and their sum bounds the instantiated certificate.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Every typed body computation instantiates if the image recovers at a
recursively neutral-related equal type. The exact output substitutes, and the
image recovery stage adds to the body stage. -/
theorem proofErase_computed_joint_compute_inst_converted_recoverable
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HTU : env.IsDefEq univs Γ T U (.sort u))
    (HT : NeutralTypeChange 0 (proofErase Γ T) (proofErase Γ U))
    (hp : env.HasType univs Γ p U)
    (HR : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedComputedJointStage D imageStage)
      (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ U))
    (he : env.HasType univs (T :: Γ) e A)
    (R : ScopedCompute (ErasedComputedJointStage D stage) (proofEraseCtx (T :: Γ))
      (proofErase (T :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D (imageStage + stage)) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst (proofErase Γ p)) := by
  have RC := proofErase_computed_joint_stage_compute_neutral_context heq hs hΓ HTU HT he R
  have W : IsDefEqCtx env univs [] (T :: Γ) (U :: Γ) := .succ (.refl hΓ) HTU
  exact proofErase_computed_joint_compute_inst_recoverable heq hs hΓ hp HR (he.defeqDFC henv W) RC

/-- Complete recursive body comparison admits the same converted recovery
criterion at any finite stage. No image recovery at the assigned type is assumed. -/
theorem proofErase_computed_joint_compare_inst_converted_recoverable
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HTU : env.IsDefEq univs Γ T U (.sort u))
    (HT : NeutralTypeChange 0 (proofErase Γ T) (proofErase Γ U))
    (hp : env.HasType univs Γ p U)
    (HR : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedComputedJointStage D imageStage)
      (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ U))
    (ha : env.HasType univs (T :: Γ) a A) (hb : env.HasType univs (T :: Γ) b A)
    (H : ComputedJointCompare (ErasedComputedJointStage D stage) (proofEraseCtx (T :: Γ)) mode
      (proofErase (T :: Γ) a) (proofErase (T :: Γ) b)) :
    ComputedJointCompare (ErasedComputedJointStage D (imageStage + stage)) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) := by
  have HC := proofErase_computed_joint_stage_recursive_neutral_context heq hs hΓ HTU HT ha hb H
  have W : IsDefEqCtx env univs [] (T :: Γ) (U :: Γ) := .succ (.refl hΓ) HTU
  exact proofErase_computed_joint_compare_inst_recoverable heq hs hΓ hp HR
    (ha.defeqDFC henv W) (hb.defeqDFC henv W) HC

/-- Whole carrier guards instantiate with their literal substituted carrier
under the converted recovery criterion, at the same additive stage bound. -/
theorem proofErase_computed_joint_carrier_inst_converted_recoverable
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HTU : env.IsDefEq univs Γ T U (.sort u))
    (HT : NeutralTypeChange 0 (proofErase Γ T) (proofErase Γ U))
    (hp : env.HasType univs Γ p U)
    (HR : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedComputedJointStage D imageStage)
      (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ U))
    (ha : env.HasType univs (T :: Γ) a A) (hb : env.HasType univs (T :: Γ) b A)
    (H : ComputedJointCarrierGuard (ErasedComputedJointStage D stage) (proofEraseCtx (T :: Γ))
      (proofErase (T :: Γ) A) (proofErase (T :: Γ) a) (proofErase (T :: Γ) b)) :
    ComputedJointCarrierGuard (ErasedComputedJointStage D (imageStage + stage)) (proofEraseCtx Γ)
      (proofErase Γ (A.inst p)) (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) := by
  have hΓT : OnCtx (T :: Γ) (env.IsType univs) := ⟨hΓ, u, HTU.hasType.1⟩
  have W : IsDefEqCtx env univs [] (T :: Γ) (U :: Γ) := .succ (.refl hΓ) HTU
  have HO : ∀ i, NeutralTypeChange 0 (contextOracle (proofEraseCtx (T :: Γ)) i)
      (contextOracle (proofEraseCtx (U :: Γ)) i) := by
    intro i
    cases i with
    | zero => exact (HT.liftN (n := 1) (by omega)).mono (by omega)
    | succ i => exact .refl
  obtain ⟨_, hA⟩ := ha.isType henv hΓT
  have HC := H.recursive_neutral_stage heq hs hΓT ha hb rfl rfl rfl rfl W HO ⟨_, hA⟩ .refl
  rw [proofErase_defeqCtx hΓT W hA, proofErase_defeqCtx hΓT W ha,
    proofErase_defeqCtx hΓT W hb] at HC
  exact proofErase_computed_joint_carrier_inst_recoverable heq hs hΓ hp HR
    (ha.defeqDFC henv W) (hb.defeqDFC henv W) HC

private theorem finite_recovery
    (HR : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedComputedJointUnion D)
      (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ U)) :
    ∃ imageStage, ¬ IsProof Γ p → ScopedTypeRecovery (ErasedComputedJointStage D imageStage)
      (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ U) := by
  classical
  by_cases hp : IsProof Γ p
  · exact ⟨0, fun hn => (hn hp).elim⟩
  obtain ⟨stage, R⟩ := (HR hp).finite_stage erased_computed_joint_stage_mono
  exact ⟨stage, fun _ => R⟩

/-- Closed-union compute instantiation follows from the finite additive
bound. The image only needs recovery at the equal converted type in the union. -/
theorem proofErase_computed_joint_union_compute_inst_converted_recoverable
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HTU : env.IsDefEq univs Γ T U (.sort u))
    (HT : NeutralTypeChange 0 (proofErase Γ T) (proofErase Γ U))
    (hp : env.HasType univs Γ p U)
    (HR : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedComputedJointUnion D)
      (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ U))
    (he : env.HasType univs (T :: Γ) e A)
    (R : ScopedCompute (ErasedComputedJointUnion D) (proofEraseCtx (T :: Γ))
      (proofErase (T :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst (proofErase Γ p)) := by
  obtain ⟨imageStage, HR⟩ := finite_recovery HR
  obtain ⟨stage, R⟩ := R.finite_stage erased_computed_joint_stage_mono
  exact (proofErase_computed_joint_compute_inst_converted_recoverable heq hs hΓ HTU HT hp HR he R).mono
    (fun H => ⟨imageStage + stage, H⟩)

/-- Closed-union compare instantiation follows from the finite additive
bound. The image only needs recovery at the equal converted type in the union. -/
theorem proofErase_computed_joint_union_compare_inst_converted_recoverable
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HTU : env.IsDefEq univs Γ T U (.sort u))
    (HT : NeutralTypeChange 0 (proofErase Γ T) (proofErase Γ U))
    (hp : env.HasType univs Γ p U)
    (HR : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedComputedJointUnion D)
      (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ U))
    (ha : env.HasType univs (T :: Γ) a A) (hb : env.HasType univs (T :: Γ) b A)
    (H : ComputedJointCompare (ErasedComputedJointUnion D) (proofEraseCtx (T :: Γ)) mode
      (proofErase (T :: Γ) a) (proofErase (T :: Γ) b)) :
    ComputedJointCompare (ErasedComputedJointUnion D) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) := by
  obtain ⟨imageStage, HR⟩ := finite_recovery HR
  obtain ⟨stage, H⟩ := H.finite_stage erased_computed_joint_stage_mono
  exact (proofErase_computed_joint_compare_inst_converted_recoverable heq hs hΓ HTU HT hp HR ha hb H).mono
    (fun H => ⟨imageStage + stage, H⟩)

/-- Closed-union carrier instantiation follows from the finite additive
bound. The image only needs recovery at the equal converted type in the union. -/
theorem proofErase_computed_joint_union_carrier_inst_converted_recoverable
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HTU : env.IsDefEq univs Γ T U (.sort u))
    (HT : NeutralTypeChange 0 (proofErase Γ T) (proofErase Γ U))
    (hp : env.HasType univs Γ p U)
    (HR : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedComputedJointUnion D)
      (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ U))
    (ha : env.HasType univs (T :: Γ) a A) (hb : env.HasType univs (T :: Γ) b A)
    (H : ComputedJointCarrierGuard (ErasedComputedJointUnion D) (proofEraseCtx (T :: Γ))
      (proofErase (T :: Γ) A) (proofErase (T :: Γ) a) (proofErase (T :: Γ) b)) :
    ComputedJointCarrierGuard (ErasedComputedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (A.inst p)) (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) := by
  obtain ⟨imageStage, HR⟩ := finite_recovery HR
  obtain ⟨stage, H⟩ := H.finite_stage erased_computed_joint_stage_mono
  exact (proofErase_computed_joint_carrier_inst_converted_recoverable heq hs hΓ HTU HT hp HR ha hb H).mono
    (fun H => ⟨imageStage + stage, H⟩)

end Lean4Lean.VEnv.Strengthening
