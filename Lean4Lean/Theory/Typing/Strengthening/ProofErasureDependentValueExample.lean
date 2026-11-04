import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDependentValueInstantiation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDependentValueBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeFunctionExample

/-! # A converted input returning a generic value

The lambda accepts a polymorphic identity function and applies it to Prop and
an ambient proposition. Its assigned input beta-expands the written dependent
family. Exact native recovery at that assignment fails, but the new dependent
family certificate transports recursive comparisons and first-layer computation.
-/
namespace Lean4Lean.VEnv.Strengthening.DependentValueExample
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open NativeFamilyFramework NativeFamilyFramework.DependentValueBoundary
open private lambda_domain_recovery
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeFunctionExample
variable [Params]

/-- An ambient proposition P : Prop. -/
def context (Γ : List VExpr) : List VExpr := .sort .zero :: Γ
/-- The source input has an application head, unlike the written identity type. -/
def selected : VExpr := .app (.lam (.sort (.succ .zero)) identityType) (.sort .zero)
/-- Apply the polymorphic input to Prop, then to the ambient proposition. -/
def body : VExpr := .app (.app (.bvar 0) (.sort .zero)) (.bvar 1)
/-- The written lambda consumes the dependent polymorphic input. -/
def image : VExpr := .lam identityType body
/-- Its assigned function type uses the expanded input annotation. -/
def assigned : VExpr := .forallE selected (.sort .zero)

/-- The expanded assigned input is ordinarily equal to the written dependent family. -/
theorem inputs_equal : env.IsDefEq univs Γ selected identityType
    (.sort (.imax (.succ (.succ .zero)) (.imax (.succ .zero) (.succ .zero)))) :=
  .beta identityType_typed (HasType.sort (by trivial))

private theorem context_wf (hΓ : OnCtx Γ (env.IsType univs)) :
    OnCtx (context Γ) (env.IsType univs) := ⟨hΓ, _, HasType.sort (by trivial)⟩

private theorem body_typed : env.HasType univs (identityType :: context Γ) body (.sort .zero) := by
  have hf : env.HasType univs (identityType :: context Γ) (.bvar 0) identityType := .bvar .zero
  have hf' : env.HasType univs (identityType :: context Γ) (.app (.bvar 0) (.sort .zero))
      (.forallE (.sort .zero) (.sort .zero)) := .app hf (HasType.sort (by trivial))
  exact .app hf' (.bvar (.succ .zero))

/-- The image is actually typed at its beta-expanded assignment. -/
theorem image_typed : env.HasType univs (context Γ) image assigned :=
  (IsDefEq.forallEDF inputs_equal.symm (HasType.sort (l := .zero) (by trivial))).defeq
    (HasType.lam identityType_typed body_typed)

private theorem identity_erasure (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase Γ identityType = .forallE (.sort (.succ .zero)) (.forallE (.bvar 0) (.bvar 1)) := by
  have hΓU : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  have hX : env.HasType univs (.sort (.succ .zero) :: Γ) (.bvar 0) (.sort (.succ .zero)) := .bvar .zero
  have hΓX : OnCtx (.bvar 0 :: .sort (.succ .zero) :: Γ) (env.IsType univs) := ⟨hΓU, _, hX⟩
  have hX' : env.HasType univs (.bvar 0 :: .sort (.succ .zero) :: Γ) (.bvar 1) (.sort (.succ .zero)) :=
    .bvar (.succ .zero)
  rw [show proofErase Γ identityType = .forallE _ _ from if_neg (not_isProof_of_sort hΓ identityType_typed),
    show proofErase Γ (.sort (.succ .zero)) = .sort _ from if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial))),
    show proofErase (.sort (.succ .zero) :: Γ) (.forallE (.bvar 0) (.bvar 1)) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓU (HasType.forallE hX hX')),
    show proofErase (.sort (.succ .zero) :: Γ) (.bvar 0) = .bvar 0 from if_neg (not_isProof_of_sort hΓU hX),
    show proofErase (.bvar 0 :: .sort (.succ .zero) :: Γ) (.bvar 1) = .bvar 1 from if_neg (not_isProof_of_sort hΓX hX')]

/-- The application-headed assigned input is not natively recoverable, even
in the full computed union. The normal written domain cannot grow that head. -/
theorem assigned_recovery_failure (D : PureObservation.Definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ¬ ScopedTypeRecovery (ErasedComputedJointUnion D) (proofEraseCtx (context Γ))
      (proofErase (context Γ) image) (proofErase (context Γ) assigned) := by
  intro R
  have hΔ := context_wf hΓ
  rw [show proofErase (context Γ) image = .lam _ _ from
      if_neg (not_isProof_function_to_sort hΔ image_typed), identity_erasure hΔ,
    show proofErase (context Γ) assigned = .forallE _ _ from if_neg (not_isProof_of_sort hΔ
      (HasType.forallE inputs_equal.hasType.1 (HasType.sort (l := .zero) (by trivial)))),
    show proofErase (context Γ) selected = .app _ _ from if_neg (not_isProof_of_sort hΔ inputs_equal.hasType.1)] at R
  have HN : ∀ Δ, NormalSyntax (ErasedComputedJointUnion D Δ)
      (.forallE (.sort (.succ .zero)) (.forallE (.bvar 0) (.bvar 1))) := by
    intro Δ
    exact ⟨(fun _ H => erased_computed_joint_union_head H),
      ⟨fun _ H => erased_computed_joint_union_head H, trivial⟩,
      ⟨(fun _ H => erased_computed_joint_union_head H),
        ⟨fun _ H => erased_computed_joint_union_head H, trivial⟩,
        ⟨fun _ H => erased_computed_joint_union_head H, trivial⟩⟩⟩
  obtain ⟨_, E⟩ := lambda_domain_recovery erased_computed_joint_union_head HN R
  cases E

private theorem body_path (hΓ : OnCtx Γ (env.IsType univs)) :
    StructuralFamilyRecovery D 1 (identityType :: context Γ) body
      (proofErase (identityType :: context Γ) (.sort .zero)) 0 := by
  have hΔ : OnCtx (identityType :: context Γ) (env.IsType univs) :=
    ⟨context_wf hΓ, _, identityType_typed⟩
  rw [show proofErase (identityType :: context Γ) (.sort .zero) = .sort .zero from
    if_neg (not_isProof_of_sort hΔ (HasType.sort (by trivial)))]
  exact .type body_typed

/-- All common-typed recursive comparisons survive this converted dependent input. -/
theorem compare_inst (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs (assigned :: context Γ) a T)
    (hb : env.HasType univs (assigned :: context Γ) b T)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (assigned :: context Γ)) mode
      (proofErase (assigned :: context Γ) a) (proofErase (assigned :: context Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (context Γ)) mode
      (proofErase (context Γ) (a.inst image)) (proofErase (context Γ) (b.inst image)) :=
  proofErase_computed_joint_zero_compare_inst_valueFamily hs (context_wf hΓ) inputs_equal
    identity_family image_typed .refl (body_path hΓ) ha hb H

/-- First-layer guarded computation also retains its exact substituted output. -/
theorem compute_inst (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs (assigned :: context Γ) e T)
    (R : ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx (assigned :: context Γ))
      (proofErase (assigned :: context Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx (context Γ))
      (proofErase (context Γ) (e.inst image)) (out.inst (proofErase (context Γ) image)) :=
  proofErase_computed_joint_one_compute_inst_valueFamily heq hs (context_wf hΓ) inputs_equal
    identity_family image_typed .refl (body_path hΓ) he R

end Lean4Lean.VEnv.Strengthening.DependentValueExample
