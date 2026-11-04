import Lean4Lean.Theory.Typing.Strengthening.ProofErasureProjectionClosedInstantiation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTerminalFieldExamples

/-! # Nested record images beyond one-projection terminal coverage

A wrapper around a record with a retained type field has a finite projection
tree. Its first projection is not terminal, because another retained projection
is possible. The full recursive checking consumers still instantiate the wrapper.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params]

/-- A single declared field can carry any already certified record tree. -/
theorem StructureReplay.ProjectionClosedFields.single
    (hshape : info.ctorType = wrapForalls [A] result)
    (hp : info.nparams = 0) (hf : info.numFields = 1)
    (HA : ProjectionClosedType env A) : ProjectionClosedFields env info := by
  apply ProjectionClosedFields.of_telescope hshape (by simp [hp, hf])
  intro j hj _
  have : j = 0 := by simp only [List.length_cons, List.length_nil] at hj; omega
  subst j
  exact HA

/-- Wrapping a certified record adds one finite projection level. This rule
can be repeated and is independent of all runtime values and comparisons. -/
theorem StructureReplay.ProjectionClosedFields.nested
    (hshape : info.ctorType = wrapForalls [VExpr.mkApps (.const inner ls) args] result)
    (hp : info.nparams = 0) (hf : info.numFields = 1)
    (hi : env.projections inner innerInfo) (HF : ProjectionClosedFields env innerInfo) :
    ProjectionClosedFields env info :=
  .single hshape hp hf (.record hi HF)

/-- Two actually typed retained projections separate the finite-tree class
from the previous class requiring immediate terminal projection results. -/
theorem projection_closed_nested_record_boundary
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const outer []))
    (hI : env.HasType univs Γ (.const inner []) (.sort (.succ u)))
    (hiO : env.projections outer outerInfo) (hiI : env.projections inner innerInfo)
    (hshapeO : outerInfo.ctorType = wrapForalls [.const inner []] outerResult)
    (hpO : outerInfo.nparams = 0) (hxO : outerInfo.nindices = 0)
    (hfO : outerInfo.numFields = 1) (huO : outerInfo.uvars = 0)
    (hposO : (outerInfo.resultLevel.inst []).IsNeverZero)
    (hshapeI : innerInfo.ctorType = wrapForalls
      [.sort (.succ .zero), VExpr.mkApps (.const d us) [.bvar 0]] innerResult)
    (hpI : innerInfo.nparams = 0) (hxI : innerInfo.nindices = 0)
    (hfI : innerInfo.numFields = 2) (huI : innerInfo.uvars = 0)
    (hposI : (innerInfo.resultLevel.inst []).IsNeverZero)
    (hr : env.Rigid d) (hn : ∀ info, ¬ env.projections d info) :
    ProjectionClosedImage Γ m ∧
    env.HasType univs Γ (.proj outer 0 m) (.const inner []) ∧
    env.HasType univs Γ (.proj inner 0 (.proj outer 0 m)) (.sort (.succ .zero)) ∧
    ¬ IsProof Γ (.proj outer 0 m) ∧
    ¬ IsProof Γ (.proj inner 0 (.proj outer 0 m)) ∧
    ¬ ProjectionTerminalImage Γ m := by
  have HFI := StructureReplay.TerminalFields.dependent_type_data hshapeI hpI hfI hr hn
  have HFO := StructureReplay.ProjectionClosedFields.nested (ls := []) (args := []) hshapeO hpO hfO hiI HFI.projectionClosed
  have HI : ProjectionClosedImage Γ m := ProjectionClosedImage.of_fields (args := []) hm hiO HFO
  have hfield : outerInfo.fieldType outer [] [] 0 m = some (.const inner []) := by
    have H := outerInfo.fieldType_eq_instOuter (typeName := outer) (major := m) hshapeO
      (levels := []) (by simp [huO]) (params := []) (by simp [hpO])
      (index := 0) (by simp [hpO])
    simpa only [hpO, Nat.zero_add, List.getElem_cons_zero, VExpr.instL, List.map_nil,
      VExpr.instOuter_const] using H
  obtain ⟨_, hc⟩ := henv.ordered.constWF (henv.ordered.projectionConstructor hiO)
  have hclosed := hc.closedN henv.ordered
    (show OnCtx ([] : List VExpr) (env.IsType outerInfo.uvars) from trivial)
  have hproj : env.HasType univs Γ (.proj outer 0 m) (.const inner []) :=
    .projDF (indexArgs := []) hiO (by simp) (by simp [huO]) (by simp [hpO])
      (by simp [hxO]) hfield hI hm hm hclosed (.inl hposO)
  have hnO := not_proof_at_positive_type hΓ hI hproj
  obtain ⟨_, htI, hnI, HnotI⟩ := terminal_fields_retained_projection hΓ hproj hiI hshapeI
    hpI hxI hfI (by simp) (by simp [huI]) hposI hr hn
  exact ⟨HI, hproj, htI, hnO, hnI, fun H => HnotI (H.projection hΓ hproj hnO)⟩

/-- Every common-typed body comparison instantiates a nested-record image,
including bodies traversing both retained projections of the boundary example. -/
theorem proofErase_computed_joint_zero_compare_inst_nestedRecord
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ m P) (hm : env.HasType univs Γ m (.const outer levels))
    (hiO : env.projections outer outerInfo) (hiI : env.projections inner innerInfo)
    (hshape : outerInfo.ctorType = wrapForalls [VExpr.mkApps (.const inner ls) args] result)
    (hparams : outerInfo.nparams = 0) (hf : outerInfo.numFields = 1)
    (HF : StructureReplay.ProjectionClosedFields env innerInfo)
    (ha : env.HasType univs (P :: Γ) a A) (hb : env.HasType univs (P :: Γ) b A)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (P :: Γ)) mode
      (proofErase (P :: Γ) a) (proofErase (P :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst m)) (proofErase Γ (b.inst m)) :=
  proofErase_computed_joint_zero_compare_inst_projectionFields hs hΓ hp (args := []) hm hiO
    (StructureReplay.ProjectionClosedFields.nested hshape hparams hf hiI HF) ha hb H

end Lean4Lean.VEnv.Strengthening
