import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeFamilyContext
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeFunctionExample

/-! # A substituted native lambda outside exact recovery and protected heads

The existing higher-order lambda applies its bound function parameter. Its
assigned annotation cannot be recovered, even in the full union, and its queried
head lies under its own binder. Actual native recovery and alignment nevertheless
transport every common-typed recursive comparison through its substitution.
-/
namespace Lean4Lean.VEnv.Strengthening.NativeAlignedExample
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open TypeFunctionExample
open private written_typed body_typed image_erasure
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeFunctionExample
variable [Params]

/-- The lambda natively recovers its written type, whose function input has a
family certificate. Selection can therefore retain the unrecoverable assigned type. -/
theorem image_aligned (hΓ : OnCtx Γ (env.IsType univs)) :
    AlignedNativeRecovery D Γ image (proofErase Γ assigned) := by
  have hΓW : OnCtx (written :: Γ) (env.IsType univs) := ⟨hΓ, _, written_typed⟩
  have ht := HasType.lam (Γ := Γ) written_typed body_typed
  have hw : PolymorphicTypeFamily Γ written := .function .sort .sort
  have hΓU : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  have hΓWU : OnCtx (.sort (.succ .zero) :: written :: Γ) (env.IsType univs) :=
    ⟨hΓW, _, HasType.sort (by trivial)⟩
  have ER : proofErase Γ (.forallE written (.sort .zero)) =
      .forallE (.forallE (.sort (.succ .zero)) (.sort .zero)) (.sort .zero) := by
    rw [show proofErase Γ (.forallE written (.sort .zero)) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ (HasType.forallE written_typed (HasType.sort (by trivial)))),
      show proofErase Γ written = .forallE _ _ from if_neg (not_isProof_of_sort hΓ written_typed),
      show proofErase Γ (.sort (.succ .zero)) = .sort _ from
        if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial))),
      show proofErase (.sort (.succ .zero) :: Γ) (.sort .zero) = .sort _ from
        if_neg (not_isProof_of_sort hΓU (HasType.sort (by trivial))),
      show proofErase (written :: Γ) (.sort .zero) = .sort _ from
        if_neg (not_isProof_of_sort hΓW (HasType.sort (by trivial)))]
  have EB : proofErase (written :: Γ) body = .app (.bvar 0) (.sort .zero) := by
    rw [show proofErase (written :: Γ) body = .app _ _ from if_neg (not_isProof_of_sort hΓW body_typed),
      show proofErase (written :: Γ) (.bvar 0) = .bvar 0 from
        if_neg (not_isProof_function_to_sort hΓW (show env.HasType univs (written :: Γ) (.bvar 0) written from .bvar .zero)),
      show proofErase (written :: Γ) (.sort .zero) = .sort _ from
        if_neg (not_isProof_of_sort hΓW (HasType.sort (by trivial)))]
  have RH : ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx (written :: Γ))
      (.bvar 0) (.forallE (.sort (.succ .zero)) (.sort .zero)) := by
    have R := proofErase_scoped_lookup_recovery (Step := ErasedJointStage D 0) hΓW
      (show Lookup (written :: Γ) 0 written from .zero)
      (not_isProof_function_to_sort hΓW (show env.HasType univs (written :: Γ) (.bvar 0) written from .bvar .zero)) .refl
    rw [show proofErase (written :: Γ) (.bvar 0) = .bvar 0 from
        if_neg (not_isProof_function_to_sort hΓW (show env.HasType univs (written :: Γ) (.bvar 0) written from .bvar .zero)),
      show proofErase (written :: Γ) written = .forallE _ _ from if_neg (not_isProof_of_sort hΓW written_typed),
      show proofErase (written :: Γ) (.sort (.succ .zero)) = .sort _ from
        if_neg (not_isProof_of_sort hΓW (HasType.sort (by trivial))),
      show proofErase (.sort (.succ .zero) :: written :: Γ) (.sort .zero) = .sort _ from
        if_neg (not_isProof_of_sort hΓWU (HasType.sort (by trivial)))] at R
    exact R
  have EN : proofErase Γ (.forallE written (.sort .zero)) = .forallE (proofErase Γ written)
      (proofErase (written :: Γ) (.sort .zero)) :=
    if_neg (not_isProof_of_sort hΓ (HasType.forallE written_typed (HasType.sort (by trivial))))
  have EW := (ProofShape.forallE.inj (EN.symm.trans ER)).1
  simp only [proofEraseCtx, EW] at RH
  refine ⟨_, ht, .family (.function hw .sort), ?_⟩
  rw [image_erasure hΓ, EB, ER]
  exact .lam (.app RH)

/-- The example fails both earlier sufficient image requirements: exact
assigned recovery and the protected native-head footprint. -/
theorem image_boundary (D : PureObservation.Definitions) (hΓ : OnCtx Γ (env.IsType univs)) :
    ¬ ScopedTypeRecovery (ErasedComputedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ image) (proofErase Γ assigned) ∧
    ¬ RecoveryHeadsAbove 0 (proofErase Γ image) := by
  refine ⟨assigned_recovery_failure D hΓ, ?_⟩
  have hΓW : OnCtx (written :: Γ) (env.IsType univs) := ⟨hΓ, _, written_typed⟩
  rw [image_erasure hΓ,
    show proofErase (written :: Γ) body = .app _ _ from if_neg (not_isProof_of_sort hΓW body_typed),
    show proofErase (written :: Γ) (.bvar 0) = .bvar 0 from
      if_neg (not_isProof_function_to_sort hΓW (show env.HasType univs (written :: Γ) (.bvar 0) written from .bvar .zero))]
  exact Nat.not_succ_le_zero 0

/-- Every common-typed recursive comparison transports through this image via
actual native recovery, without a protected-head condition or exact assigned recovery. -/
theorem compare_inst (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs (assigned :: Γ) a T)
    (hb : env.HasType univs (assigned :: Γ) b T)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (assigned :: Γ)) mode
      (proofErase (assigned :: Γ) a) (proofErase (assigned :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst image)) (proofErase Γ (b.inst image)) := by
  have hp : env.HasType univs Γ image assigned := image_typed
  obtain ⟨u, hA⟩ := hp.isType henv hΓ
  have hΓA : OnCtx (assigned :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := image) (A₀ := assigned)).substEq hΓA hp
  have ES : ErasedSubstAgreement (assigned :: Γ) Γ (VExpr.Subst.one image)
      (ProofShape.Subst.one (proofErase Γ image)) := erasedSubstAgreement_one hΓA hp
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN] using
    proofErase_computed_joint_zero_compare_subst_nativeAligned hs hΓ W ES
      (NativeAlignedOrRecoveringImages.inst (image_aligned hΓ)) ha hb H

end Lean4Lean.VEnv.Strengthening.NativeAlignedExample
