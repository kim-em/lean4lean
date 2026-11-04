import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeFunctionInstantiation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTerminalDomainExample

/-! # A higher-order input with expanded head and changed result universe

The selected input beta-expands a Pi whose input and result universe syntax both
differ from the written function input. The image applies its retained function
parameter to Prop. Exact assigned recovery fails, but full body comparison and
first-layer computation survive instantiation.
-/
namespace Lean4Lean.VEnv.Strengthening.TypeFunctionExample
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private scoped_normal_fixed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
open private beta_forallE_parts
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin
variable [Params]

/-- An unsimplified input universe. -/
def inputLevel : VLevel := .imax (.succ .zero) (.succ .zero)
/-- An unsimplified result universe. -/
def resultLevel : VLevel := .max .zero .zero
/-- The selected Pi changes both written universe annotations. -/
def core : VExpr := .forallE (.sort inputLevel) (.sort resultLevel)
/-- The actual selected input has an application head. -/
def selected : VExpr := .app (.lam (.sort (.succ .zero)) core) (.sort .zero)
/-- The written function input. -/
def written : VExpr := .forallE (.sort (.succ .zero)) (.sort .zero)
/-- The body retains and calls its function parameter. -/
def body : VExpr := .app (.bvar 0) (.sort .zero)
/-- The image genuinely consumes a function-valued argument. -/
def image : VExpr := .lam written body
/-- Its assigned input has the expanded selected annotation. -/
def assigned : VExpr := .forallE selected (.sort .zero)

private theorem core_equal : env.IsDefEq univs Γ core written
    (.sort (.imax (.succ inputLevel) (.succ resultLevel))) :=
  .forallEDF (IsDefEq.sortDF (by trivial) (by trivial) VLevel.imax_self)
    (IsDefEq.sortDF (by trivial) (by trivial) VLevel.max_self)

/-- The expanded source is ordinarily equal to the written type-valued function. -/
theorem inputs_equal : env.IsDefEq univs Γ selected written
    (.sort (.imax (.succ inputLevel) (.succ resultLevel))) :=
  (IsDefEq.beta core_equal.hasType.1 (HasType.sort (by trivial))).trans core_equal

private theorem written_typed : env.HasType univs Γ written
    (.sort (.imax (.succ (.succ .zero)) (.succ .zero))) :=
  .forallE (HasType.sort (by trivial)) (HasType.sort (by trivial))

private theorem body_typed : env.HasType univs (written :: Γ) body (.sort .zero) :=
  by
  have hf : env.HasType univs (written :: Γ) (.bvar 0) written := .bvar .zero
  exact HasType.app hf (HasType.sort (l := .zero) (by trivial))

/-- The higher-order image is actually typed at the expanded selected input. -/
theorem image_typed : env.HasType univs Γ image assigned :=
  (IsDefEq.forallEDF inputs_equal.symm (HasType.sort (l := .zero) (by trivial))).defeq
    (HasType.lam written_typed body_typed)

omit [Params] in
/-- Neither a displayed source Pi nor preservation of its result annotation
can be used for this selected input and its beta reduct. -/
theorem source_shape_boundary :
    (∀ A C, selected ≠ .forallE A C) ∧
    (∀ A, core ≠ .forallE A (.sort .zero)) := by
  constructor <;> intros <;> intro E <;> cases E

private theorem erase_sort (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs) :
    proofErase Γ (.sort u) = .sort u :=
  if_neg (not_isProof_of_sort hΓ (HasType.sort hu))

private theorem image_erasure (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase Γ image = .lam (.forallE (.sort (.succ .zero)) (.sort .zero))
      (proofErase (written :: Γ) body) := by
  have hΓU : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  rw [show proofErase Γ image = .lam _ _ from
    if_neg (not_isProof_function_to_sort hΓ image_typed)]
  rw [show proofErase Γ written = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ written_typed), erase_sort hΓ (by trivial),
    erase_sort hΓU (by trivial)]

omit [Params] in
private theorem forall_fixed_domain
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (HN : ∀ Δ, NormalSyntax (Step Δ) X)
    (R : ScopedCompute Step Δ (.forallE X B) out) :
    ∃ C, out = .forallE X C := by
  generalize E : ProofShape.forallE X B = e at R
  induction R generalizing B with
  | base H => exact (E ▸ hhead H).elim
  | beta H =>
    obtain ⟨A, C, EO, HA, _⟩ := beta_forallE_parts (E ▸ H)
    have EA := scoped_normal_fixed (ScopedCompute.beta (Δ := []) HA) HN
    exact ⟨C, EA ▸ EO⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨B', EB⟩ := ih₁ E
    exact ih₂ EB.symm
  | forallE HA HB =>
    cases E
    have EA := scoped_normal_fixed HA HN
    subst EA
    exact ⟨_, rfl⟩
  | app | proj | lam => cases E

private theorem lambda_domain_recovery
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (HN : ∀ Δ, NormalSyntax (Step Δ) X)
    (R : ScopedTypeRecovery Step Δ (.lam X b) out) :
    ∃ C, out = .forallE X C := by
  generalize E : ProofShape.lam X b = e at R
  induction R with
  | lam => cases E; exact ⟨_, rfl⟩
  | convert R H ih =>
    obtain ⟨C, EC⟩ := ih E
    rw [EC] at H
    exact forall_fixed_domain hhead HN H
  | bvar | sort | const | app | forallE | proj => cases E

/-- Exact assigned recovery cannot recover the expanded input even in the
full computed union. This is not a strengthening counterexample. -/
theorem assigned_recovery_failure (D : PureObservation.Definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ¬ ScopedTypeRecovery (ErasedComputedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ image) (proofErase Γ assigned) := by
  intro R
  have hAssigned := HasType.forallE (Γ := Γ) inputs_equal.hasType.1 (HasType.sort (l := .zero) (by trivial))
  have EA : proofErase Γ assigned = .forallE (proofErase Γ selected)
      (proofErase (selected :: Γ) (.sort .zero)) :=
    if_neg (not_isProof_of_sort hΓ hAssigned)
  have ES : proofErase Γ selected = .app _ _ :=
    if_neg (not_isProof_of_sort hΓ inputs_equal.hasType.1)
  rw [image_erasure hΓ, EA, ES] at R
  have HN : ∀ Δ, NormalSyntax (ErasedComputedJointUnion D Δ)
      (.forallE (.sort (.succ .zero)) (.sort .zero)) := by
    intro Δ
    exact ⟨(fun _ H => erased_computed_joint_union_head H),
      ⟨fun _ H => erased_computed_joint_union_head H, trivial⟩,
      ⟨fun _ H => erased_computed_joint_union_head H, trivial⟩⟩
  obtain ⟨_, E⟩ := lambda_domain_recovery erased_computed_joint_union_head HN R
  cases E

private theorem body_path (hΓ : OnCtx Γ (env.IsType univs)) :
    StructuralFamilyRecovery D 1 (written :: Γ) body
      (proofErase (written :: Γ) (.sort .zero)) 0 := by
  rw [erase_sort (Γ := written :: Γ) ⟨hΓ, _, written_typed⟩ (by trivial)]
  exact .type body_typed

/-- Every common-typed recursive body comparison survives this image, whose
own body retains and applies its higher-order parameter. -/
theorem compare_inst (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs (assigned :: Γ) a T)
    (hb : env.HasType univs (assigned :: Γ) b T)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (assigned :: Γ)) mode
      (proofErase (assigned :: Γ) a) (proofErase (assigned :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst image)) (proofErase Γ (b.inst image)) :=
  proofErase_computed_joint_zero_compare_inst_typeFunction hs hΓ inputs_equal
    TerminalDomain.sort image_typed .refl (body_path hΓ) ha hb H

/-- Exact first-layer computation also survives the same converted image. -/
theorem compute_inst (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs (assigned :: Γ) e T)
    (R : ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx (assigned :: Γ))
      (proofErase (assigned :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (e.inst image)) (out.inst (proofErase Γ image)) :=
  proofErase_computed_joint_one_compute_inst_typeFunction heq hs hΓ inputs_equal
    TerminalDomain.sort image_typed .refl (body_path hΓ) he R

end Lean4Lean.VEnv.Strengthening.TypeFunctionExample
