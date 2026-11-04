import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeInputInstantiation

/-! # Callable fields in polymorphic boxes

The box parameter may now be a type-input function. Its projection remains
callable and its application returns a certified value. This crosses the old
non-function image boundary using actual projection and application typings.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- A polymorphic box inherits a callable tree from its actual parameter. -/
theorem TypeInputTree.parameterBox
    (hi : env.projections family info)
    (hshape : info.ctorType = wrapForalls [.sort (.succ (.succ .zero)), .bvar 0] result)
    (hp : info.nparams = 1) (hx : info.nindices = 0) (hf : info.numFields = 1)
    (hl : ls.length = info.uvars) (hpos : (info.resultLevel.inst ls).IsNeverZero)
    (HA : TypeInputTree env A) :
    TypeInputTree env (VExpr.mkApps (.const family ls) [A]) := by
  obtain ⟨_, hc⟩ := henv.ordered.constWF (henv.ordered.projectionConstructor hi)
  have hclosed := hc.closedN henv.ordered
    (show OnCtx ([] : List VExpr) (env.IsType info.uvars) from trivial)
  refine .record (fields := fun _ => A.lift) hi hclosed (by simp [hp]) hx hpos ?_ ?_
  · intro i hj
    have : i = 0 := by omega
    subst i
    have H := info.fieldType_eq_instOuter (typeName := family) (major := .bvar 0) hshape hl
      (params := [A.lift]) (by simp [hp]) (index := 0) (by simp [hp])
    simpa [hp, VExpr.instL, VExpr.instOuter, VExpr.instOuterAt, VExpr.inst, instVar] using H
  · intro _ _
    exact HA.lift

/-- A field that accepts and returns types. -/
def typeFunctionField : VExpr := .forallE (.sort (.succ .zero)) (.sort (.succ .zero))

/-- A positive box with a callable field has an actual retained function
projection and a typed application to Prop. It cannot belong to the earlier
InstanceProjectionImage class, whose retained results cannot be functions. -/
theorem type_input_callable_box_boundary
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (VExpr.mkApps (.const family ls) [typeFunctionField]))
    (hi : env.projections family info)
    (hshape : info.ctorType = wrapForalls [.sort (.succ (.succ .zero)), .bvar 0] result)
    (hp : info.nparams = 1) (hx : info.nindices = 0) (hf : info.numFields = 1)
    (hl : ls.length = info.uvars) (hpos : (info.resultLevel.inst ls).IsNeverZero) :
    TypeInputImage Γ m ∧
    env.HasType univs Γ (.proj family 0 m) typeFunctionField ∧
    TypeInputImage Γ (.proj family 0 m) ∧
    env.HasType univs Γ (.app (.proj family 0 m) (.sort .zero)) (.sort (.succ .zero)) ∧
    TypeInputImage Γ (.app (.proj family 0 m) (.sort .zero)) ∧
    ¬ InstanceProjectionImage Γ m := by
  have HA : TypeInputTree env typeFunctionField :=
    .function (.projection (.closed (.terminal .sort)))
  have HI : TypeInputImage Γ m := .typed hm (HA.parameterBox hi hshape hp hx hf hl hpos)
  have hfield : info.fieldType family ls [typeFunctionField] 0 m = some typeFunctionField := by
    have H := info.fieldType_eq_instOuter (typeName := family) (major := m) hshape hl
      (params := [typeFunctionField]) (by simp [hp]) (index := 0) (by simp [hp])
    simpa [hp, VExpr.instL, VExpr.instOuter, VExpr.instOuterAt, VExpr.inst, instVar] using H
  have hproj := StructureReplay.positive_projection_native hΓ hi (by simp [hp]) hx hm hpos
    (i := 0) (by omega) hfield
  have hn := not_isProof_function_to_sort hΓ hproj
  have HP := HI.projection_image hΓ hproj hn
  have happ : env.HasType univs Γ (.app (.proj family 0 m) (.sort .zero)) (.sort (.succ .zero)) :=
    HasType.app hproj (HasType.sort (by trivial))
  exact ⟨HI, hproj, HP, happ, HP.application hΓ happ,
    fun H => (H.projection hΓ hproj hn).not_function hΓ hproj⟩

/-- Complete recursive comparison instantiates a positive box at any callable
parameter tree, including bodies using its extracted function. -/
theorem proofErase_computed_joint_zero_compare_inst_callableBox
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ m P)
    (hm : env.HasType univs Γ m (VExpr.mkApps (.const family ls) [A]))
    (hi : env.projections family info)
    (hshape : info.ctorType = wrapForalls [.sort (.succ (.succ .zero)), .bvar 0] result)
    (hparams : info.nparams = 1) (hx : info.nindices = 0) (hf : info.numFields = 1)
    (hl : ls.length = info.uvars) (hpos : (info.resultLevel.inst ls).IsNeverZero)
    (HA : TypeInputTree env A)
    (ha : env.HasType univs (P :: Γ) a T) (hb : env.HasType univs (P :: Γ) b T)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (P :: Γ)) mode
      (proofErase (P :: Γ) a) (proofErase (P :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst m)) (proofErase Γ (b.inst m)) :=
  proofErase_computed_joint_zero_compare_inst_typeInput hs hΓ hp
    (.typed hm (HA.parameterBox hi hshape hparams hx hf hl hpos)) ha hb H

end Lean4Lean.VEnv.Strengthening
