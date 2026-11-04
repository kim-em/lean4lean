import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeInputInstantiation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedStructuralDomainBoundary

/-! # Direct universe-input conversion without native image recovery

The written and assigned input universes are equal but syntactically distinct.
The callable image tree instantiates complete recursive certificates although
exact assigned recovery fails even in the full computed union.
-/
namespace Lean4Lean.VEnv.Strengthening.TypeInputConvertedExample
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private declared declared_equiv erase_sort
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveryJoinBoundary
open private lambda_recovery
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructuralDomainBoundary
variable [Params]

/-- A constant type-valued function with literal universe input. -/
def image : VExpr := .lam (.sort (.succ .zero)) (.sort .zero)
/-- The assigned function type instead uses equal nonliteral universe syntax. -/
def assigned : VExpr := .forallE (.sort declared) (.sort (.succ .zero))

private theorem native_typed : env.HasType univs Γ image
    (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) :=
  .lam (HasType.sort (by trivial)) (HasType.sort (by trivial))

/-- The converted assigned type is obtained by ordinary universe equality. -/
theorem image_typed : env.HasType univs Γ image assigned :=
  (IsDefEq.forallEDF
    (IsDefEq.sortDF (by trivial) (by trivial) declared_equiv.symm)
    (HasType.sort (l := .succ .zero) (by trivial))).defeq native_typed

/-- The actual native typing supplies a callable tree independently of the
assigned type syntax or any native recovery for the image. -/
theorem image_tree : TypeInputImage Γ image :=
  .typed native_typed (.function (.projection (.closed (.terminal .sort))))

private theorem erasures (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase Γ image = .lam (.sort (.succ .zero)) (.sort .zero) ∧
    proofErase Γ assigned = .forallE (.sort declared) (.sort (.succ .zero)) := by
  have hΓW : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  have hΓA : OnCtx (.sort declared :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  have hA := HasType.forallE (env := env) (U := univs) (Γ := Γ) (HasType.sort (l := declared) (by trivial))
    (HasType.sort (l := .succ .zero) (by trivial))
  constructor
  · rw [show proofErase Γ image = .lam _ _ from
      if_neg (not_isProof_function_to_sort hΓ native_typed), erase_sort hΓ (by trivial),
      erase_sort hΓW (by trivial)]
  · rw [show proofErase Γ assigned = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ hA), erase_sort hΓ (by trivial), erase_sort hΓA (by trivial)]

/-- Both the earlier non-function image class and exact assigned recovery fail
for this genuinely typed callable image. The negative recovery result applies
to all computed stages together; it is not a strengthening counterexample. -/
theorem assigned_recovery_failure (D : PureObservation.Definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ¬ InstanceProjectionImage Γ image ∧
    ¬ ScopedTypeRecovery (ErasedComputedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ image) (proofErase Γ assigned) := by
  constructor
  · intro H
    exact H.not_function hΓ native_typed
  · intro R
    rw [(erasures hΓ).1, (erasures hΓ).2] at R
    have HN : ∀ Δ, NormalSyntax (ErasedComputedJointUnion D Δ) (.sort (.succ .zero)) := by
      intro Δ
      exact ⟨fun _ H => erased_computed_joint_union_head H, trivial⟩
    have E := lambda_recovery erased_computed_joint_union_head HN R
    cases E

/-- The callable tree instantiates every common-typed body comparison despite
the converted selected input and the failed native recovery. -/
theorem compare_inst (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs (assigned :: Γ) a T)
    (hb : env.HasType univs (assigned :: Γ) b T)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (assigned :: Γ)) mode
      (proofErase (assigned :: Γ) a) (proofErase (assigned :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst image)) (proofErase Γ (b.inst image)) :=
  proofErase_computed_joint_zero_compare_inst_typeInput hs hΓ image_typed image_tree ha hb H

/-- All first-layer computations retain their exact substituted outputs for
the same callable image and converted assigned input. -/
theorem compute_inst (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs (assigned :: Γ) e T)
    (R : ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx (assigned :: Γ))
      (proofErase (assigned :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (e.inst image)) (out.inst (proofErase Γ image)) :=
  proofErase_computed_joint_one_compute_inst_typeInput heq hs hΓ image_typed image_tree he R

end Lean4Lean.VEnv.Strengthening.TypeInputConvertedExample
