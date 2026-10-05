import Lean4Lean.Theory.Typing.AnchoredProjectionRows
import Lean4Lean.Theory.Typing.AnchoredFamilyArgumentGrades

/-! An isolated interface for declaration-indexed projection observations.
The plan has no assigned source field type or semantic callback. Every
selector uses its own literal declaration row, while earlier selectors reuse
the same rich record demand and the same finite target seed ledger. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem FamilyKey.uniform_take
    (N : Nat) (keys : List FamilyKey) (bounded : ∀ key ∈ keys, key.rank ≤ N) (count : Nat) :
    FamilyKey.uniform N (keys.take count)
      (fun key member => bounded key (List.mem_of_mem_take member)) =
      (FamilyKey.uniform N keys bounded).take count := by
  induction keys generalizing count with
  | nil => simp only [List.take_nil, FamilyKey.uniform]
  | cons key keys ih =>
    cases count with
    | zero => rfl
    | succ count =>
      simp only [List.take_succ_cons, FamilyKey.uniform]
      exact congrArg (List.cons _) (ih (fun key member => bounded key (List.mem_cons_of_mem _ member)) count)

structure ProjectionPlan (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (demand : RecordData (Profile N)) (selector : Nat) where
  info : VProjectionInfo
  registered : registry.projections demand.family.name = some info
  domains : List VExpr
  result : VExpr
  declaration : info.ctorType = wrapForalls domains result
  closed : info.ctorType.Closed
  levelsWF : ∀ level ∈ demand.family.levels, level.WF U
  levelCount : demand.family.levels.length = info.uvars
  fieldCount : Nat
  selected : selector < fieldCount
  arityBound : info.nparams + fieldCount ≤ domains.length
  fieldBound : fieldCount ≤ info.numFields
  parameterBound : info.nparams ≤ demand.family.arguments.length
  fields : demand.fields.map Prod.fst = List.range fieldCount
  keys : List FamilyKey
  bounded : ∀ key ∈ keys, key.rank ≤ N
  rows : ProjectionRows env U registry target [] [] (nativeCaptureSubst []) (fun _ => [])
    (info.ctorType.instL demand.family.levels)
    ((domains.map (·.instL demand.family.levels)).take (info.nparams + fieldCount)) keys
  requests : FamilyKey.uniform N keys bounded =
    demand.family.arguments.take info.nparams ++ demand.fields.map Prod.snd

namespace ProjectionPlan

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  {target : List VExpr} {N : Nat} {demand : RecordData (Profile N)} {selector : Nat}

/-- The observer of the major and its whole exact record descriptor remain
unchanged. Only the selector decreases; all source reification can therefore
reuse the original major child rather than asking for a new observation. -/
def earlier (plan : ProjectionPlan env U registry target demand selector)
    (index : Nat) (before : index < selector) :
    ProjectionPlan env U registry target demand index :=
  { plan with selected := Nat.lt_trans before plan.selected }

theorem earlier_keys (plan : ProjectionPlan env U registry target demand selector)
    (index : Nat) (before : index < selector) : (plan.earlier index before).keys = plan.keys := rfl

theorem keyCount (plan : ProjectionPlan env U registry target demand selector) :
    plan.keys.length = plan.info.nparams + plan.fieldCount := by
  have length := plan.rows.length
  simp only [List.length_take, List.length_map, Nat.min_eq_left plan.arityBound] at length
  exact length

theorem prefixRequests (plan : ProjectionPlan env U registry target demand selector)
    (index : Nat) :
    FamilyKey.uniform N (plan.keys.take (plan.info.nparams + index))
      (fun key member => plan.bounded key (List.mem_of_mem_take member)) =
      demand.family.arguments.take plan.info.nparams ++ (demand.fields.take index).map Prod.snd := by
  rw [FamilyKey.uniform_take, plan.requests]
  have paramsLength : (demand.family.arguments.take plan.info.nparams).length = plan.info.nparams := by
    simp only [List.length_take, Nat.min_eq_left plan.parameterBound]
  have taken := List.take_length_add_append (l₁ := demand.family.arguments.take plan.info.nparams)
    (l₂ := demand.fields.map Prod.snd) index
  simpa only [paramsLength, List.map_take] using taken

/-- This is the exact domain template and natural support for the selected
field. The template certificate is realized at the frozen prefix anchors;
declaration replay transports it to the original source parameters and
preceding projections before source substitution/reification. -/
theorem domainSlice (plan : ProjectionPlan env U registry target demand selector) :
    Nonempty (ProjectionRowSlice env U registry target [] (nativeCaptureSubst []) (fun _ => [])
      (plan.info.ctorType.instL demand.family.levels)
      ((plan.domains.map (·.instL demand.family.levels)).take (plan.info.nparams + plan.fieldCount))
      plan.keys (plan.info.nparams + selector)) := by
  apply plan.rows.restrictDomain
  simp only [List.length_take, List.length_map, Nat.min_eq_left plan.arityBound]
  have selected := plan.selected
  omega

end ProjectionPlan
end Lean4Lean.AnchoredSource.Adapted
