import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePolymorphicInstantiation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeFunctionExample

/-! # Converted polymorphic inputs used at an external generic type

The image accepts a polymorphic predicate and applies it to the existing generic
type and value in its context. Its assigned input beta-expands the written family.
The example supplies actual typings, a finite body path, and both complete
comparison and first-layer computation consumers.
-/
namespace Lean4Lean.VEnv.Strengthening.PolymorphicExample
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private lambda_domain_recovery
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeFunctionExample
variable [Params]

/-- An external type X : Type and value x : X. -/
def context (Γ : List VExpr) : List VExpr := .bvar 0 :: .sort (.succ .zero) :: Γ
/-- The polymorphic predicate input binds its own type parameter. -/
def written : VExpr := .forallE (.sort (.succ .zero)) (.forallE (.bvar 0) (.sort .zero))
/-- The actual assigned input has an application head. -/
def selected : VExpr := .app (.lam (.sort (.succ .zero)) written) (.sort .zero)
/-- The image calls its function parameter with the external X and x. -/
def body : VExpr := .app (.app (.bvar 0) (.bvar 2)) (.bvar 1)
/-- The higher-order image consumes its polymorphic argument. -/
def image : VExpr := .lam written body
/-- Its assigned input differs syntactically from its written annotation. -/
def assigned : VExpr := .forallE selected (.sort .zero)

private theorem written_typed : env.HasType univs Γ written
    (.sort (.imax (.succ (.succ .zero)) (.imax (.succ .zero) (.succ .zero)))) :=
  polymorphic_predicate_type_typed

/-- The beta-expanded input is ordinarily equal to the written polymorphic family. -/
theorem inputs_equal : env.IsDefEq univs Γ selected written
    (.sort (.imax (.succ (.succ .zero)) (.imax (.succ .zero) (.succ .zero)))) :=
  .beta written_typed (HasType.sort (by trivial))

private theorem body_typed : env.HasType univs (written :: context Γ) body (.sort .zero) := by
  have hf : env.HasType univs (written :: context Γ) (.bvar 0) written := .bvar .zero
  exact HasType.app (HasType.app hf (.bvar (.succ (.succ .zero)))) (.bvar (.succ .zero))

/-- Actual typing at the expanded selected domain. -/
theorem image_typed : env.HasType univs (context Γ) image assigned :=
  (IsDefEq.forallEDF inputs_equal.symm (HasType.sort (l := .zero) (by trivial))).defeq
    (HasType.lam written_typed body_typed)

private theorem context_wf (hΓ : OnCtx Γ (env.IsType univs)) :
    OnCtx (context Γ) (env.IsType univs) :=
  ⟨⟨hΓ, _, HasType.sort (by trivial)⟩, _, HasType.bvar .zero⟩

/-- The written input has the new certificate and provably lacks the previous one. -/
theorem input_certificate_boundary (hΓ : OnCtx Γ (env.IsType univs)) :
    PolymorphicTypeFamily (context Γ) written ∧ ¬ TerminalTypeFamily (context Γ) written :=
  ⟨polymorphicTypeFamily_predicate, terminalTypeFamily_polymorphic_predicate_failure (context_wf hΓ)⟩

private theorem erase_sort (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs) :
    proofErase Γ (.sort u) = .sort u :=
  if_neg (not_isProof_of_sort hΓ (HasType.sort hu))

private theorem written_erasure (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase Γ written = .forallE (.sort (.succ .zero)) (.forallE (.bvar 0) (.sort .zero)) := by
  have hΓU : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  have hΓX : OnCtx (.bvar 0 :: .sort (.succ .zero) :: Γ) (env.IsType univs) :=
    ⟨hΓU, _, HasType.bvar .zero⟩
  rw [show proofErase Γ written = .forallE _ _ from if_neg (not_isProof_of_sort hΓ written_typed)]
  rw [erase_sort hΓ (by trivial)]
  rw [show proofErase (.sort (.succ .zero) :: Γ) (.forallE (.bvar 0) (.sort .zero)) =
    .forallE _ _ from if_neg (not_isProof_of_sort hΓU
      (HasType.forallE (HasType.bvar .zero) (HasType.sort (by trivial))))]
  rw [show proofErase (.sort (.succ .zero) :: Γ) (.bvar 0) = .bvar 0 from
    if_neg (not_isProof_of_sort hΓU (HasType.bvar .zero)), erase_sort hΓX (by trivial)]

/-- Exact assigned recovery fails even over the full computed union: the
normal written family cannot reduce to the application-headed assigned input. -/
theorem assigned_recovery_failure (D : PureObservation.Definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ¬ ScopedTypeRecovery (ErasedComputedJointUnion D) (proofEraseCtx (context Γ))
      (proofErase (context Γ) image) (proofErase (context Γ) assigned) := by
  intro R
  have hΔ := context_wf hΓ
  have EA : proofErase (context Γ) assigned = .forallE _ _ :=
    if_neg (not_isProof_of_sort hΔ
      (HasType.forallE inputs_equal.hasType.1 (HasType.sort (l := .zero) (by trivial))))
  have ES : proofErase (context Γ) selected = .app _ _ :=
    if_neg (not_isProof_of_sort hΔ inputs_equal.hasType.1)
  rw [show proofErase (context Γ) image = .lam _ _ from
    if_neg (not_isProof_function_to_sort hΔ image_typed), written_erasure hΔ, EA, ES] at R
  have HN : ∀ Δ, NormalSyntax (ErasedComputedJointUnion D Δ)
      (.forallE (.sort (.succ .zero)) (.forallE (.bvar 0) (.sort .zero))) := by
    intro Δ
    exact ⟨(fun _ H => erased_computed_joint_union_head H),
      ⟨fun _ H => erased_computed_joint_union_head H, trivial⟩,
      ⟨(fun _ H => erased_computed_joint_union_head H),
        ⟨fun _ H => erased_computed_joint_union_head H, trivial⟩,
        ⟨fun _ H => erased_computed_joint_union_head H, trivial⟩⟩⟩
  obtain ⟨_, E⟩ := lambda_domain_recovery erased_computed_joint_union_head HN R
  cases E

private theorem body_path (hΓ : OnCtx Γ (env.IsType univs)) :
    StructuralFamilyRecovery D 1 (written :: context Γ) body
      (proofErase (written :: context Γ) (.sort .zero)) 0 := by
  rw [erase_sort (Γ := written :: context Γ) ⟨context_wf hΓ, _, written_typed⟩ (by trivial)]
  exact .type body_typed

/-- Every common-typed recursive comparison survives the converted polymorphic
image, whose body actually applies its parameter to the external generic value. -/
theorem compare_inst (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs (assigned :: context Γ) a T)
    (hb : env.HasType univs (assigned :: context Γ) b T)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (assigned :: context Γ)) mode
      (proofErase (assigned :: context Γ) a) (proofErase (assigned :: context Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (context Γ)) mode
      (proofErase (context Γ) (a.inst image)) (proofErase (context Γ) (b.inst image)) :=
  proofErase_computed_joint_zero_compare_inst_polymorphicFamily hs (context_wf hΓ) inputs_equal
    polymorphicTypeFamily_predicate image_typed .refl (body_path hΓ) ha hb H

/-- First-layer computation retains its exact substituted target as well. -/
theorem compute_inst (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs (assigned :: context Γ) e T)
    (R : ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx (assigned :: context Γ))
      (proofErase (assigned :: context Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx (context Γ))
      (proofErase (context Γ) (e.inst image)) (out.inst (proofErase (context Γ) image)) :=
  proofErase_computed_joint_one_compute_inst_polymorphicFamily heq hs (context_wf hΓ) inputs_equal
    polymorphicTypeFamily_predicate image_typed .refl (body_path hΓ) he R

end Lean4Lean.VEnv.Strengthening.PolymorphicExample
