import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePolymorphicInstantiation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeFunctionExample

/-! # Converted higher-order inputs with genuinely callable generic values

The input family is (Type → Type) → Prop. Its generic input is a function,
so neither terminality nor sort specialization can justify binder conversion.
The image passes a real type-valued lambda to its higher-order parameter, with
a beta-expanded assigned domain and no exact assigned native recovery.
-/
namespace Lean4Lean.VEnv.Strengthening.CallableFamilyExample
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private lambda_domain_recovery
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeFunctionExample
variable [Params]

/-- The generic input to the family is itself callable. -/
def input : VExpr := .forallE (.sort (.succ .zero)) (.sort (.succ .zero))
/-- A concrete type-valued function passed to the higher-order parameter. -/
def argument : VExpr := .lam (.sort (.succ .zero)) (.sort .zero)
/-- The written higher-order input. -/
def written : VExpr := .forallE input (.sort .zero)
/-- The selected input beta-expands that written type. -/
def selected : VExpr := .app (.lam (.sort (.succ .zero)) written) (.sort .zero)
/-- The body actually calls its higher-order parameter. -/
def body : VExpr := .app (.bvar 0) argument
/-- The typed replacement image. -/
def image : VExpr := .lam written body
/-- The assigned type uses the expanded input. -/
def assigned : VExpr := .forallE selected (.sort .zero)

private theorem input_typed : env.HasType univs Γ input
    (.sort (.imax (.succ (.succ .zero)) (.succ (.succ .zero)))) :=
  .forallE (HasType.sort (by trivial)) (HasType.sort (by trivial))

private theorem argument_typed : env.HasType univs Γ argument input :=
  .lam (HasType.sort (by trivial)) (HasType.sort (by trivial))

private theorem written_typed : env.HasType univs Γ written
    (.sort (.imax (.imax (.succ (.succ .zero)) (.succ (.succ .zero))) (.succ .zero))) :=
  .forallE input_typed (HasType.sort (by trivial))

/-- The expanded selected input is actually equal to the written family. -/
theorem inputs_equal : env.IsDefEq univs Γ selected written
    (.sort (.imax (.imax (.succ (.succ .zero)) (.succ (.succ .zero))) (.succ .zero))) :=
  .beta written_typed (HasType.sort (by trivial))

private theorem body_typed : env.HasType univs (written :: Γ) body (.sort .zero) := by
  have hf : env.HasType univs (written :: Γ) (.bvar 0) written := .bvar .zero
  exact .app hf argument_typed

/-- Actual typing at the expanded selected annotation. -/
theorem image_typed : env.HasType univs Γ image assigned :=
  (IsDefEq.forallEDF inputs_equal.symm (HasType.sort (l := .zero) (by trivial))).defeq
    (HasType.lam written_typed body_typed)

/-- An explicit finite call tree justifies the higher-order family's input. -/
theorem input_callable : CallableDomain Γ input :=
  .of_tree (.function (.projection (.closed (.terminal .sort))))

/-- Both previously available input classifications fail for this generic
function value. The new certificate is needed before whole-family readout. -/
theorem input_boundary (hΓ : OnCtx Γ (env.IsType univs)) :
    CallableDomain Γ input ∧ ¬ TerminalDomain Γ input ∧
      ¬ SortSpecialization (input :: Γ) (.bvar 0) := by
  have hΓI : OnCtx (input :: Γ) (env.IsType univs) := ⟨hΓ, _, input_typed⟩
  have hv : env.HasType univs (input :: Γ) (.bvar 0)
      (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) := .bvar .zero
  exact ⟨input_callable, fun H => H.not_function hΓI hv, fun H => H.not_function hv⟩

/-- The new callable branch builds a substitution-stable whole-family certificate. -/
theorem family_certificate : PolymorphicTypeFamily Γ written :=
  .callable input_callable .sort

private theorem erase_sort (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs) :
    proofErase Γ (.sort u) = .sort u :=
  if_neg (not_isProof_of_sort hΓ (HasType.sort hu))

private theorem written_erasure (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase Γ written =
      .forallE (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) (.sort .zero) := by
  have hΓU : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  have hΓI : OnCtx (input :: Γ) (env.IsType univs) := ⟨hΓ, _, input_typed⟩
  rw [show proofErase Γ written = .forallE _ _ from if_neg (not_isProof_of_sort hΓ written_typed),
    show proofErase Γ input = .forallE _ _ from if_neg (not_isProof_of_sort hΓ input_typed),
    erase_sort hΓ (by trivial), erase_sort hΓU (by trivial), erase_sort hΓI (by trivial)]

/-- The normal written family cannot reduce to the application-headed assigned
input, even using full computed-union native recovery. -/
theorem assigned_recovery_failure (D : PureObservation.Definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ¬ ScopedTypeRecovery (ErasedComputedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ image) (proofErase Γ assigned) := by
  intro R
  have EA : proofErase Γ assigned = .forallE _ _ :=
    if_neg (not_isProof_of_sort hΓ
      (HasType.forallE inputs_equal.hasType.1 (HasType.sort (l := .zero) (by trivial))))
  have ES : proofErase Γ selected = .app _ _ :=
    if_neg (not_isProof_of_sort hΓ inputs_equal.hasType.1)
  rw [show proofErase Γ image = .lam _ _ from
    if_neg (not_isProof_function_to_sort hΓ image_typed), written_erasure hΓ, EA, ES] at R
  have HN : ∀ Δ, NormalSyntax (ErasedComputedJointUnion D Δ)
      (.forallE (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) (.sort .zero)) := by
    intro Δ
    exact ⟨(fun _ H => erased_computed_joint_union_head H),
      ⟨(fun _ H => erased_computed_joint_union_head H),
        ⟨fun _ H => erased_computed_joint_union_head H, trivial⟩,
        ⟨fun _ H => erased_computed_joint_union_head H, trivial⟩⟩,
      ⟨fun _ H => erased_computed_joint_union_head H, trivial⟩⟩
  obtain ⟨_, E⟩ := lambda_domain_recovery erased_computed_joint_union_head HN R
  cases E

private theorem body_path (hΓ : OnCtx Γ (env.IsType univs)) :
    StructuralFamilyRecovery D 1 (written :: Γ) body
      (proofErase (written :: Γ) (.sort .zero)) 0 := by
  rw [erase_sort (Γ := written :: Γ) ⟨hΓ, _, written_typed⟩ (by trivial)]
  exact .type body_typed

/-- Complete recursive comparison instantiation through the higher-order image. -/
theorem compare_inst (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs (assigned :: Γ) a T)
    (hb : env.HasType univs (assigned :: Γ) b T)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (assigned :: Γ)) mode
      (proofErase (assigned :: Γ) a) (proofErase (assigned :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst image)) (proofErase Γ (b.inst image)) :=
  proofErase_computed_joint_zero_compare_inst_polymorphicFamily hs hΓ inputs_equal
    family_certificate image_typed .refl (body_path hΓ) ha hb H

/-- Exact first-layer guarded computation through the same image. -/
theorem compute_inst (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs (assigned :: Γ) e T)
    (R : ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx (assigned :: Γ))
      (proofErase (assigned :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (e.inst image)) (out.inst (proofErase Γ image)) :=
  proofErase_computed_joint_one_compute_inst_polymorphicFamily heq hs hΓ inputs_equal
    family_certificate image_typed .refl (body_path hΓ) he R

end Lean4Lean.VEnv.Strengthening.CallableFamilyExample
