import Lean4Lean.Theory.Typing.EquationWorldClosureOrder

/-! A selected frame may retain additional covered captures without changing
its maximum numerical cost. Its old children remain smaller than the merged
parent; the old parent itself need not be strictly smaller than the new one. -/
namespace Lean4Lean.VEnv.EquationWorldClosureOrder
set_option Elab.async false

theorem Below.retargetCaptures
    {r : α → α → Prop}
    (rt : ∀ {a b c}, r a b → r b c → r a c)
    {key : α} {previous next : List (Closure α)}
    (covered : Covered r previous next)
    {value : Closure α} (smaller : Below r value (.node key previous)) :
    Below r value (.node key next) := by
  have captured : ∀ child ∈ previous, Below r child (.node key next) :=
    covered.below rt (fun _ member => .child member)
  induction value using (measure (fun x : Closure α => sizeOf x)).wf.induction with
  | h value ih =>
    cases value with
    | node valueKey children =>
      cases smaller with
      | child member => exact captured _ member
      | under member smaller => exact trans (r := r) rt smaller (captured _ member)
      | root lower childBounds =>
        exact .root lower (fun child member => ih child (by
          change sizeOf child < sizeOf (Closure.node valueKey children)
          have bound := List.sizeOf_lt_of_mem member
          simp only [Closure.node.sizeOf_spec]
          omega) (childBounds child member))

theorem Below.retarget
    {r : α → α → Prop}
    (rt : ∀ {a b c}, r a b → r b c → r a c)
    {previousKey nextKey : α} {previous next : List (Closure α)}
    (keys : previousKey = nextKey ∨ r previousKey nextKey)
    (covered : Covered r previous next)
    {value : Closure α} (smaller : Below r value (.node previousKey previous)) :
    Below r value (.node nextKey next) := by
  rcases keys with rfl | strict
  · exact Below.retargetCaptures (r := r) rt covered smaller
  · exact trans (r := r) rt smaller (smaller_root (r := r) rt strict covered)

end Lean4Lean.VEnv.EquationWorldClosureOrder
