import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTerminalDomainInstantiation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedStructuralDomainBoundary

/-! # A converted universe input beyond exact native recovery

A higher-order lambda is assigned a function input whose universe annotation
is ordinarily equal, but syntactically different, from the written annotation.
Terminal-domain conversion instantiates recursive certificates even though
native recovery in the full computed union cannot recover its assigned type.
-/
namespace Lean4Lean.VEnv.Strengthening.TerminalDomainExample
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private lambda_recovery
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructuralDomainBoundary
variable [Params]

/-- A universe expression equal to level one but with different syntax. -/
def universeAlias : VLevel := .imax (.succ .zero) (.succ .zero)
/-- The selected higher-order input uses the unsimplified universe. -/
def selected : VExpr := .forallE (.sort universeAlias) (.sort .zero)
/-- The written higher-order input uses literal level one. -/
def written : VExpr := .forallE (.sort (.succ .zero)) (.sort .zero)
/-- A type-valued lambda with the written input annotation. -/
def image : VExpr := .lam written (.sort .zero)
/-- Its assigned type instead carries the selected input annotation. -/
def assigned : VExpr := .forallE selected (.sort (.succ .zero))

private theorem inputs_equal : env.IsDefEq univs Γ (.sort universeAlias) (.sort (.succ .zero))
    (.sort (.succ universeAlias)) :=
  IsDefEq.sortDF (by trivial) (by trivial) VLevel.imax_self

private theorem written_typed : env.HasType univs Γ written
    (.sort (.imax (.succ (.succ .zero)) (.succ .zero))) :=
  HasType.forallE (HasType.sort (by trivial)) (HasType.sort (by trivial))

private theorem selected_typed : env.HasType univs Γ selected
    (.sort (.imax (.succ universeAlias) (.succ .zero))) :=
  HasType.forallE (HasType.sort (by trivial)) (HasType.sort (by trivial))

/-- The example is actually typed at the converted assigned type. -/
theorem image_typed : env.HasType univs Γ image assigned := by
  have HKK := IsDefEq.forallEDF (Γ := Γ) inputs_equal (HasType.sort (l := .zero) (by trivial))
  exact (IsDefEq.forallEDF HKK.symm (HasType.sort (l := .succ .zero) (by trivial))).defeq
    (HasType.lam written_typed (HasType.sort (by trivial)))

private theorem erase_sort (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs) :
    proofErase Γ (.sort u) = .sort u :=
  if_neg (not_isProof_of_sort hΓ (HasType.sort hu))

private theorem erasures (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase Γ image = .lam (.forallE (.sort (.succ .zero)) (.sort .zero)) (.sort .zero) ∧
    proofErase Γ assigned = .forallE
      (.forallE (.sort universeAlias) (.sort .zero)) (.sort (.succ .zero)) := by
  have hΓW : OnCtx (written :: Γ) (env.IsType univs) := ⟨hΓ, _, written_typed⟩
  have hΓS : OnCtx (selected :: Γ) (env.IsType univs) := ⟨hΓ, _, selected_typed⟩
  have hΓ₁ : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  have hΓ₂ : OnCtx (.sort universeAlias :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  have EW : proofErase Γ written = .forallE (.sort (.succ .zero)) (.sort .zero) := by
    rw [show proofErase Γ written = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ written_typed), erase_sort hΓ (by trivial),
      erase_sort hΓ₁ (by trivial)]
  have ES : proofErase Γ selected = .forallE (.sort universeAlias) (.sort .zero) := by
    rw [show proofErase Γ selected = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ selected_typed), erase_sort hΓ (by trivial),
      erase_sort hΓ₂ (by trivial)]
  constructor
  · rw [show proofErase Γ image = .lam _ _ from
      if_neg (not_isProof_function_to_sort hΓ image_typed), EW, erase_sort hΓW (by trivial)]
  · have hT := HasType.forallE (Γ := Γ) selected_typed (HasType.sort (l := .succ .zero) (by trivial))
    rw [show proofErase Γ assigned = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ hT), ES, erase_sort hΓS (by trivial)]

/-- Exact assigned recovery fails even with all computed stages available.
This is a recovery obstruction, not a counterexample to strengthening. -/
theorem assigned_recovery_failure (D : PureObservation.Definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ¬ ScopedTypeRecovery (ErasedComputedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ image) (proofErase Γ assigned) := by
  intro R
  rw [(erasures hΓ).1, (erasures hΓ).2] at R
  have HN : ∀ Δ, NormalSyntax (ErasedComputedJointUnion D Δ)
      (.forallE (.sort (.succ .zero)) (.sort .zero)) := by
    intro Δ
    exact ⟨(fun _ H => erased_computed_joint_union_head H),
      ⟨fun _ H => erased_computed_joint_union_head H, trivial⟩,
      ⟨fun _ H => erased_computed_joint_union_head H, trivial⟩⟩
  have E := lambda_recovery erased_computed_joint_union_head HN R
  cases E

private theorem body_path (hΓ : OnCtx Γ (env.IsType univs)) :
    StructuralFamilyRecovery D 1 (written :: Γ) (.sort .zero)
      (proofErase (written :: Γ) (.sort (.succ .zero))) 0 := by
  rw [erase_sort (Γ := written :: Γ) ⟨hΓ, _, written_typed⟩ (by trivial)]
  exact .type (HasType.sort (by trivial))

/-- The new terminal-domain case preserves every common-typed stage-zero
comparison when instantiating this image, despite the recovery obstruction. -/
theorem compare_inst (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs (assigned :: Γ) a T)
    (hb : env.HasType univs (assigned :: Γ) b T)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (assigned :: Γ)) mode
      (proofErase (assigned :: Γ) a) (proofErase (assigned :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst image)) (proofErase Γ (b.inst image)) :=
  proofErase_computed_joint_zero_compare_inst_terminalDomain hs hΓ inputs_equal
    TerminalDomain.sort image_typed .refl (body_path hΓ) ha hb H

/-- The same converted image preserves first-layer computation with its
exact substituted output. -/
theorem compute_inst (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs (assigned :: Γ) e T)
    (R : ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx (assigned :: Γ))
      (proofErase (assigned :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (e.inst image)) (out.inst (proofErase Γ image)) :=
  proofErase_computed_joint_one_compute_inst_terminalDomain heq hs hΓ inputs_equal
    TerminalDomain.sort image_typed .refl (body_path hΓ) he R

end Lean4Lean.VEnv.Strengthening.TerminalDomainExample
