import Lean4Lean.Theory.Typing.Strengthening.ProofErasureInstanceProjectionInstantiation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureProjectionClosedParameterBoundary

/-! # Instantiated field trees repair the parameter-box boundary

A positive polymorphic box inherits the tree of its actual type parameter.
This rule iterates to arbitrary finite nesting and feeds the complete recursive
checking and first-layer computation instantiation theorems.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- A box's field certificate is its actual parameter tree lifted under the
fresh major, rather than the uninstantiated parameter variable. -/
theorem InstanceProjectionType.parameterBox
    (hi : env.projections family info)
    (hshape : info.ctorType = wrapForalls [.sort (.succ (.succ .zero)), .bvar 0] result)
    (hp : info.nparams = 1) (hx : info.nindices = 0) (hf : info.numFields = 1)
    (hl : ls.length = info.uvars) (hpos : (info.resultLevel.inst ls).IsNeverZero)
    (HA : InstanceProjectionType env A) :
    InstanceProjectionType env (VExpr.mkApps (.const family ls) [A]) := by
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

/-- The very same typed Box Type occurrence excluded by declaration-only
coverage has an instantiated-tree certificate and an actual retained projection. -/
theorem instance_projection_parameter_box_repair
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (VExpr.mkApps (.const family []) [.sort (.succ .zero)]))
    (hi : env.projections family info)
    (hshape : info.ctorType = wrapForalls [.sort (.succ (.succ .zero)), .bvar 0] result)
    (hp : info.nparams = 1) (hx : info.nindices = 0) (hf : info.numFields = 1)
    (hu : info.uvars = 0) (hpos : (info.resultLevel.inst []).IsNeverZero) :
    InstanceProjectionImage Γ m ∧ ¬ ProjectionClosedImage Γ m ∧
    env.HasType univs Γ (.proj family 0 m) (.sort (.succ .zero)) ∧
    ¬ IsProof Γ (.proj family 0 m) := by
  obtain ⟨ht, hn, Hno⟩ := projection_closed_parameter_record_boundary hΓ hm hi hshape hp hx hf hu hpos
  have HA := InstanceProjectionType.parameterBox hi hshape hp hx hf
    (ls := []) (by simp [hu]) hpos (A := .sort (.succ .zero)) (.closed (.terminal .sort))
  exact ⟨.typed hm HA, Hno, ht, hn⟩

/-- Finite nesting of one polymorphic wrapper. -/
def iteratedParameterBox (family : Name) (ls : List VLevel) (A : VExpr) : Nat → VExpr
  | 0 => A
  | n + 1 => VExpr.mkApps (.const family ls) [iteratedParameterBox family ls A n]

/-- Every finite number of wrappers inherits the starting parameter's tree.
Actual use still requires the image's ordinary typing at that nested type. -/
theorem InstanceProjectionType.iteratedParameterBox
    (hi : env.projections family info)
    (hshape : info.ctorType = wrapForalls [.sort (.succ (.succ .zero)), .bvar 0] result)
    (hp : info.nparams = 1) (hx : info.nindices = 0) (hf : info.numFields = 1)
    (hl : ls.length = info.uvars) (hpos : (info.resultLevel.inst ls).IsNeverZero)
    (HA : InstanceProjectionType env A) (n : Nat) :
    InstanceProjectionType env (Strengthening.iteratedParameterBox family ls A n) := by
  induction n with
  | zero => exact HA
  | succ n ih => exact InstanceProjectionType.parameterBox hi hshape hp hx hf hl hpos ih

/-- The entire recursive comparison instantiates at any typed finite nesting
of polymorphic boxes, including comparisons traversing their projections. -/
theorem proofErase_computed_joint_zero_compare_inst_iteratedBox
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ m P)
    (hm : env.HasType univs Γ m (iteratedParameterBox family ls A n))
    (hi : env.projections family info)
    (hshape : info.ctorType = wrapForalls [.sort (.succ (.succ .zero)), .bvar 0] result)
    (hparams : info.nparams = 1) (hx : info.nindices = 0) (hf : info.numFields = 1)
    (hl : ls.length = info.uvars) (hpos : (info.resultLevel.inst ls).IsNeverZero)
    (HA : InstanceProjectionType env A)
    (ha : env.HasType univs (P :: Γ) a T) (hb : env.HasType univs (P :: Γ) b T)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (P :: Γ)) mode
      (proofErase (P :: Γ) a) (proofErase (P :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst m)) (proofErase Γ (b.inst m)) :=
  proofErase_computed_joint_zero_compare_inst_instanceProjection hs hΓ hp
    (.typed hm (HA.iteratedParameterBox hi hshape hparams hx hf hl hpos n)) ha hb H

/-- Arbitrarily nested boxes also preserve every first-layer computation and
its exact substituted output. -/
theorem proofErase_computed_joint_one_compute_inst_iteratedBox
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ m P)
    (hm : env.HasType univs Γ m (iteratedParameterBox family ls A n))
    (hi : env.projections family info)
    (hshape : info.ctorType = wrapForalls [.sort (.succ (.succ .zero)), .bvar 0] result)
    (hparams : info.nparams = 1) (hx : info.nindices = 0) (hf : info.numFields = 1)
    (hl : ls.length = info.uvars) (hpos : (info.resultLevel.inst ls).IsNeverZero)
    (HA : InstanceProjectionType env A)
    (ht : env.HasType univs (P :: Γ) e T)
    (R : ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx (P :: Γ))
      (proofErase (P :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (e.inst m)) (out.inst (proofErase Γ m)) :=
  proofErase_computed_joint_one_compute_inst_instanceProjection heq hs hΓ hp
    (.typed hm (HA.iteratedParameterBox hi hshape hparams hx hf hl hpos n)) ht R

end Lean4Lean.VEnv.Strengthening
