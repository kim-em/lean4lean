import Lean4Lean.Theory.Typing.Strengthening.ProofErasureInstanceProjectionImage

/-! # Finite trees of type-input calls and record projections

Function nodes accept types and return another finite tree. Positive record
nodes classify instantiated field types and can return callable values. The
certificate contains no raw checking or guard-conversion assumption.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
variable {env : VEnv}

/-- A finite tree of callable and projectable types. The record premise contains
only exact field-type computation and child trees, never a checking law. -/
inductive TypeInputTree (env : VEnv) : VExpr → Prop
  | projection : InstanceProjectionType env A → TypeInputTree env A
  /-- A callable value accepts a type and returns another certified value. -/
  | function : TypeInputTree env C → TypeInputTree env (.forallE (.sort u) C)
  | record {fields : Nat → VExpr} : env.projections c info → info.ctorType.Closed →
      ps.length = info.nparams → info.nindices = 0 →
      (info.resultLevel.inst ls).IsNeverZero →
      (∀ i, i < info.numFields →
        info.fieldType c ls (ps.map (·.lift)) i (.bvar 0) = some (fields i)) →
      (∀ i, i < info.numFields → TypeInputTree env (fields i)) →
      TypeInputTree env (mkApps (.const c ls) ps)

/-- Substituting the occurrence parameters transports every child tree under
its fresh major binder. The declaration and positive projection guard remain
unchanged. -/
theorem TypeInputTree.subst (H : TypeInputTree env A) :
    TypeInputTree env (A.subst σ) := by
  induction H generalizing σ with
  | projection H => exact .projection H.subst
  | function H ih =>
    simp only [VExpr.subst]
    exact .function ih
  | @record c info ls ps fields hi hc hp hx hpos HF HT ih =>
    simp only [VExpr.subst_mkApps, VExpr.subst]
    refine .record (fields := fun i => (fields i).subst σ.lift) hi hc
      (by simpa only [List.length_map] using hp) hx hpos ?_ ?_
    · intro i hj
      have hF' := info.fieldType_subst_some hc (HF i hj) (substitution := σ.lift)
      simpa only [List.map_map, Function.comp_def, VExpr.lift_subst_lift,
        VExpr.Subst.lift, VExpr.subst] using hF'
    · intro i hj
      exact ih i hj

/-- Inserting a fresh major binder lifts all ambient parameter references. -/
theorem TypeInputTree.lift (H : TypeInputTree env A) :
    TypeInputTree env A.lift := by
  rw [VExpr.lift, VExpr.liftN_eq_subst]
  exact H.subst

end Lean4Lean.VEnv.Strengthening
