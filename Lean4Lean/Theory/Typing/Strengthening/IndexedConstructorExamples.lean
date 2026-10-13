import Lean4Lean.Theory.Typing.Strengthening.SingletonHeadComputation

/-! # The indexed-constructor boundary for raw structure eta

Indexed constructors carry a tuple observation with no argument demands. A free
variable at the empty valuation cannot carry it. Consequently the expanded model
cannot also admit arbitrary indexed structure expansions. This checks why the
zero-index guard must accompany the newly admitted indexed iota rules.
-/
namespace Lean4Lean.VEnv.Strengthening.ConstructorObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)
variable [Params] {D : Definitions}

/-- A testable constructor can be observed without inspecting any argument. -/
theorem Obs.empty_ctor_tuple {ctor : Name} (hn : NotEtaCtor ctor) (args : List VExpr) :
    Obs D S (mkApps (.const ctor levels) args) (.ctor ctor levels (args.map fun _ => [])) := by
  apply Obs.ctor_tuple hn.atLevels
  induction args with
  | nil => exact .nil
  | cons a args ih => exact .cons (by simp) ih

/-- An indexed structure expansion would introduce a constructor observation at
a free variable. It is therefore excluded from the refined mixed relation, even
though the earlier over-approximation allowed it without the actual eta guard. -/
theorem indexed_eta_excluded (hi : env.projections family info) (hn : info.nindices ≠ 0)
    (hD : ConstructorRigid D) :
    ¬ EtaCompute D (.bvar i) (structExpand family info levels ps (.bvar i)) := by
  intro R
  have H := Obs.empty_ctor_tuple (D := D) (S := fun _ _ => False) (levels := levels)
    (NotEtaCtor.of_indexed hi hn)
    (ps ++ (List.range info.numFields).map (fun j => .proj family j (.bvar i)))
  obtain ⟨_, hfalse, _⟩ := (R.obs_back hD H).var_inv
  exact hfalse

/-- Indexed constructors satisfy the broadened test criterion but fail the old
blanket exclusion of projection constructors. -/
theorem indexed_test_available (hi : env.projections family info) (hn : info.nindices ≠ 0) :
    NotEtaCtor info.ctorName ∧ ¬ NotProjectionCtor info.ctorName :=
  ⟨NotEtaCtor.of_indexed hi hn, fun H => H family info hi rfl⟩

/-- An inadmissible universe instance also has a tuple test without inspecting
its arguments, even when the registered family has zero indices. -/
theorem Obs.empty_inadmissible_tuple (hi : env.projections family info)
    (hn : ¬ EtaAdmissible info levels) (args : List VExpr) :
    Obs D S (mkApps (.const info.ctorName levels) args)
      (.ctor info.ctorName levels (args.map fun _ => [])) := by
  apply Obs.ctor_tuple (NotEtaInstance.of_inadmissible hi hn)
  induction args with
  | nil => exact .nil
  | cons a args ih => exact .cons (by simp) ih

/-- Removing the admissibility guard would let a raw eta step introduce a tuple
observation at a free variable. Thus this guard is necessary for the expanded model. -/
theorem inadmissible_eta_excluded (hi : env.projections family info)
    (hn : ¬ EtaAdmissible info levels) (hD : ConstructorRigid D) :
    ¬ EtaCompute D (.bvar i) (structExpand family info levels ps (.bvar i)) := by
  intro R
  have H := Obs.empty_inadmissible_tuple (D := D) (S := fun _ _ => False) hi hn
    (ps ++ (List.range info.numFields).map (fun j => .proj family j (.bvar i)))
  obtain ⟨_, hfalse, _⟩ := (R.obs_back hD H).var_inv
  exact hfalse

end Lean4Lean.VEnv.Strengthening.ConstructorObservation
