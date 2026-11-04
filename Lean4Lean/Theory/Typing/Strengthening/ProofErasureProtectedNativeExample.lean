import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeFamilyImage
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeFunctionExample

/-! # Higher-order application survives an unrecoverable argument image

A protected generic function accepts the earlier converted higher-order lambda.
The argument has no exact recovery at its assigned type, even in the full union.
Exact recovery of the application survives because it queries only the protected
function head. The same native head consumes a full guard at any equal carrier.
-/
namespace Lean4Lean.VEnv.Strengthening.ProtectedNativeExample
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- The argument's assigned type contains a beta-expanded higher-order input. -/
def argumentType : VExpr := TypeFunctionExample.assigned
/-- The protected function accepts that higher-order argument and returns a proposition. -/
def functionType : VExpr := .forallE argumentType (.sort .zero)
/-- The local body queries the protected function, never the argument's type. -/
def body : VExpr := .app (.bvar 1) (.bvar 0)

private theorem argumentType_typed : env.HasType univs Γ argumentType
    (.sort (.imax (.imax (.succ TypeFunctionExample.inputLevel)
      (.succ TypeFunctionExample.resultLevel)) (.succ .zero))) :=
  .forallE TypeFunctionExample.inputs_equal.hasType.1 (HasType.sort (by trivial))

private theorem functionType_typed : env.HasType univs Γ functionType
    (.sort (.imax (.imax (.imax (.succ TypeFunctionExample.inputLevel)
      (.succ TypeFunctionExample.resultLevel)) (.succ .zero)) (.succ .zero))) :=
  .forallE argumentType_typed (HasType.sort (by trivial))

private theorem context_wf (hΓ : OnCtx Γ (env.IsType univs)) :
    OnCtx (functionType :: Γ) (env.IsType univs) := ⟨hΓ, _, functionType_typed⟩

private theorem head_typed : env.HasType univs (functionType :: Γ) (.bvar 0) functionType :=
  .bvar .zero

private theorem source_head_typed : env.HasType univs (argumentType :: functionType :: Γ)
    (.bvar 1) functionType := .bvar (.succ .zero)

private theorem source_body_typed : env.HasType univs (argumentType :: functionType :: Γ)
    body (.sort .zero) := .app source_head_typed (.bvar .zero)

/-- The assigned argument type has a stable family certificate even though its
written input annotation is beta-expanded. -/
theorem argument_family (hΓ : OnCtx Γ (env.IsType univs)) :
    PolymorphicTypeFamily Γ argumentType := by
  have HW : CallableDomain Γ TypeFunctionExample.written :=
    .of_tree (.function (.projection (.closed (.terminal .sort))))
  exact .callable (HW.convert hΓ TypeFunctionExample.inputs_equal.symm) .sort

/-- The protected generic function is an actual native image with a higher-order input. -/
theorem head_image (hΓ : OnCtx Γ (env.IsType univs)) :
    NativeFamilyImage D 0 (functionType :: Γ) (.bvar 0) := by
  have hΔ := context_wf hΓ
  exact .bvar hΔ .zero (.function (argument_family hΔ) .sort) (by omega)
    (not_isProof_function_to_sort hΔ head_typed)

/-- Native recovery survives instantiating the local argument by a lambda that
has no exact assigned recovery. The recovered application type is still Prop. -/
theorem instantiation_boundary (D : PureObservation.Definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    env.HasType univs (functionType :: Γ) TypeFunctionExample.image argumentType ∧
    ¬ ScopedTypeRecovery (ErasedComputedJointUnion D) (proofEraseCtx (functionType :: Γ))
      (proofErase (functionType :: Γ) TypeFunctionExample.image)
      (proofErase (functionType :: Γ) argumentType) ∧
    ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx (functionType :: Γ))
      (proofErase (functionType :: Γ) (body.inst TypeFunctionExample.image)) (.sort .zero) ∧
    RecoveryHeadsAbove 0 (proofErase (functionType :: Γ) (body.inst TypeFunctionExample.image)) := by
  have hΔ := context_wf hΓ
  have hΔA : OnCtx (argumentType :: functionType :: Γ) (env.IsType univs) :=
    ⟨hΔ, _, argumentType_typed⟩
  have hp : env.HasType univs (functionType :: Γ) TypeFunctionExample.image argumentType :=
    TypeFunctionExample.image_typed
  have hn := not_isProof_function_to_sort hΔA source_head_typed
  have HE : proofErase (argumentType :: functionType :: Γ) body = .app (.bvar 1) (.bvar 0) := by
    rw [show proofErase (argumentType :: functionType :: Γ) body = .app _ _ from
      if_neg (not_isProof_of_sort hΔA source_body_typed),
      show proofErase (argumentType :: functionType :: Γ) (.bvar 1) = .bvar 1 from if_neg hn,
      show proofErase (argumentType :: functionType :: Γ) (.bvar 0) = .bvar 0 from
        if_neg (not_isProof_function_to_sort hΔA (show env.HasType univs
          (argumentType :: functionType :: Γ) (.bvar 0) argumentType from .bvar .zero))]
  have RH : ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx (argumentType :: functionType :: Γ))
      (proofErase (argumentType :: functionType :: Γ) (.bvar 1))
      (proofErase (argumentType :: functionType :: Γ) functionType) :=
    proofErase_scoped_lookup_recovery hΔA (.succ .zero) hn .refl
  have hΔAA : OnCtx (argumentType :: argumentType :: functionType :: Γ) (env.IsType univs) :=
    ⟨hΔA, _, argumentType_typed⟩
  rw [show proofErase (argumentType :: functionType :: Γ) functionType = .forallE _ _ from
      if_neg (not_isProof_of_sort hΔA functionType_typed),
    show proofErase (argumentType :: argumentType :: functionType :: Γ) (.sort .zero) = .sort .zero from
      if_neg (not_isProof_of_sort hΔAA (HasType.sort (by trivial)))] at RH
  have R : ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx (argumentType :: functionType :: Γ))
      (proofErase (argumentType :: functionType :: Γ) body) (.sort .zero) := by
    rw [HE]
    rw [show proofErase (argumentType :: functionType :: Γ) (.bvar 1) = .bvar 1 from if_neg hn] at RH
    exact .app RH
  have HH : RecoveryHeadsAbove (0 + 1) (proofErase (argumentType :: functionType :: Γ) body) := by
    rw [HE]; exact Nat.le_refl 1
  have HR := proofErase_scoped_recovery_inst_protected (Step' := ErasedJointStage D 0)
    (fun H _ => erased_iota_primitive_subst H) hΔ hp source_body_typed R HH
  exact ⟨hp, TypeFunctionExample.assigned_recovery_failure D hΔ, HR⟩

/-- At any ordinarily equal selected input carrier, the native head consumes
an arbitrary full argument guard. The arguments need no native recovery. -/
theorem application_at_equal_domain
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (HE : env.IsDefEq univs (functionType :: Γ) C argumentType (.sort u))
    (hx : env.HasType univs (functionType :: Γ) x C)
    (hy : env.HasType univs (functionType :: Γ) y C)
    (HX : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (functionType :: Γ))
      (proofErase (functionType :: Γ) C)
      (proofErase (functionType :: Γ) x) (proofErase (functionType :: Γ) y)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (functionType :: Γ)) mode
      (.app (proofErase (functionType :: Γ) (.bvar 0)) (proofErase (functionType :: Γ) x))
      (.app (proofErase (functionType :: Γ) (.bvar 0)) (proofErase (functionType :: Γ) y)) := by
  have hΔ := context_wf hΓ
  have HF : env.HasType univs (functionType :: Γ) (.bvar 0) (.forallE C (.sort .zero)) :=
    (IsDefEq.forallEDF HE.symm (HasType.sort (l := .zero) (by trivial))).defeq head_typed
  exact (head_image hΓ).application_checked hs hΔ HF hx hy rfl (.leaf .refl) HX

end Lean4Lean.VEnv.Strengthening.ProtectedNativeExample
