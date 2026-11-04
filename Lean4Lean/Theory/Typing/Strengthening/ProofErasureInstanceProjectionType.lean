import Lean4Lean.Theory.Typing.Strengthening.ProofErasureProjectionClosedImage

/-! # Finite projection trees after parameter instantiation

Each record node certifies the native field types at a fresh major variable,
with the occurrence parameters already substituted. Children are certificates
of the same inductive type, so polymorphic wrappers may be nested finitely.
Positive result universes and zero indices enable actual field reconstruction.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
variable {env : VEnv}

/-- A finite tree of instantiated field types. The record premise contains
only exact field-type computation and child trees, never a checking law. -/
inductive InstanceProjectionType (env : VEnv) : VExpr → Prop
  | closed : ProjectionClosedType env A → InstanceProjectionType env A
  | record {fields : Nat → VExpr} : env.projections c info → info.ctorType.Closed →
      ps.length = info.nparams → info.nindices = 0 →
      (info.resultLevel.inst ls).IsNeverZero →
      (∀ i, i < info.numFields →
        info.fieldType c ls (ps.map (·.lift)) i (.bvar 0) = some (fields i)) →
      (∀ i, i < info.numFields → InstanceProjectionType env (fields i)) →
      InstanceProjectionType env (mkApps (.const c ls) ps)

/-- Substituting the occurrence parameters transports every child tree under
its fresh major binder. The declaration and positive projection guard remain
unchanged. -/
theorem InstanceProjectionType.subst (H : InstanceProjectionType env A) :
    InstanceProjectionType env (A.subst σ) := by
  induction H generalizing σ with
  | closed H => exact .closed H.subst
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
theorem InstanceProjectionType.lift (H : InstanceProjectionType env A) :
    InstanceProjectionType env A.lift := by
  rw [VExpr.lift, VExpr.liftN_eq_subst]
  exact H.subst

end Lean4Lean.VEnv.Strengthening
