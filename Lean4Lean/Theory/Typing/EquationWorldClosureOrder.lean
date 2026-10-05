import Lean4Lean.Theory.Typing.EquationControlOrder
import Lean4Lean.Theory.Typing.EquationWorldPolynomial
import Lean4Lean.Theory.Typing.EquationStratifiedFuel

/-! A closure order retains the worlds of captured originals. A recursive
call can descend either to a captured original, irrespective of its world,
or to a smaller control key whose captures are already below the caller.
The latter allows a canonical body to use proper caller children without
multiplying their world ranks by the size of the canonical proof.

These are measure theorems, not an interpretation theorem. Actual query
and frame producers must still supply the hereditary coverage invariant. -/
namespace Lean4Lean.VEnv.EquationWorldClosureOrder
set_option Elab.async false

inductive Closure (α : Type) where
  | node (key : α) (captures : List (Closure α))

inductive Below (r : α → α → Prop) : Closure α → Closure α → Prop where
  | child (member : child ∈ captures) : Below r child (.node key captures)
  | under (member : child ∈ captures) (smaller : Below r value child) :
      Below r value (.node key captures)
  | root (smaller : r next key)
      (capturesBelow : ∀ child ∈ nextCaptures, Below r child (.node key captures)) :
      Below r (.node next nextCaptures) (.node key captures)

private theorem accessible_node {r : α → α → Prop} {key : α}
    (accessible : Acc r key) :
    ∀ captures, (∀ child ∈ captures, Acc (Below r) child) →
      Acc (Below r) (.node key captures) := by
  induction accessible with
  | intro key _ lower =>
    intro captures captured
    apply Acc.intro
    intro value smaller
    induction value using (measure (fun x : Closure α => sizeOf x)).wf.induction with
    | h value ih =>
      cases value with
      | node next nextCaptures =>
        cases smaller with
        | child member => exact captured _ member
        | under member smaller => exact (captured _ member).inv smaller
        | root smaller capturesBelow =>
          exact lower next smaller nextCaptures (fun child member =>
            ih child (by
              change sizeOf child < sizeOf (Closure.node next nextCaptures)
              have := List.sizeOf_lt_of_mem member
              simp only [Closure.node.sizeOf_spec]
              omega) (capturesBelow child member))

theorem wellFounded {r : α → α → Prop} (wf : WellFounded r) :
    WellFounded (Below r) := by
  constructor
  intro value
  induction value using (measure (fun x : Closure α => sizeOf x)).wf.induction with
  | h value ih =>
    cases value with
    | node key captures =>
      exact accessible_node (wf.apply key) captures
        (fun child member => ih child (by
          change sizeOf child < sizeOf (Closure.node key captures)
          have := List.sizeOf_lt_of_mem member
          simp only [Closure.node.sizeOf_spec]
          omega))

theorem trans {r : α → α → Prop}
    (rt : ∀ {a b c}, r a b → r b c → r a c)
    {a b c : Closure α} (ab : Below r a b) (bc : Below r b c) : Below r a c := by
  cases bc with
  | child member => exact .under member ab
  | under member smaller => exact .under member (trans (r := r) rt ab smaller)
  | root smaller capturesBelow =>
    cases ab with
    | child member => exact capturesBelow _ member
    | under member earlier => exact trans (r := r) rt earlier (capturesBelow _ member)
    | root earlier children =>
      exact .root (rt earlier smaller) (fun child member =>
        trans (r := r) rt (children child member) (.root smaller capturesBelow))
termination_by sizeOf a + sizeOf b + sizeOf c
decreasing_by
  all_goals
    simp_wf
    have h := List.sizeOf_lt_of_mem member
    simp_all
    omega

/-- A returned frame may duplicate or omit shared captures. Each retained
closure still has to be covered by an actual old closure. -/
def Covered (r : α → α → Prop) (next old : List (Closure α)) : Prop :=
  ∀ value ∈ next, ∃ original ∈ old, value = original ∨ Below r value original

theorem Covered.refl (captures : List (Closure α)) : Covered r captures captures :=
  fun value member => ⟨value, member, .inl rfl⟩

theorem Covered.merge (left : Covered r xs bound) (right : Covered r ys bound) :
    Covered r (xs ++ ys) bound := by
  intro value member
  rcases List.mem_append.mp member with member | member
  · exact left value member
  · exact right value member

theorem Covered.duplicate (captures : List (Closure α)) :
    Covered r (captures ++ captures) captures :=
  (Covered.refl captures).merge (Covered.refl captures)

theorem Covered.below {r : α → α → Prop}
    (rt : ∀ {a b c}, r a b → r b c → r a c)
    (covered : Covered r next old)
    (bounded : ∀ original ∈ old, Below r original parent) :
    ∀ value ∈ next, Below r value parent := by
  intro value member
  obtain ⟨original, originalMember, equal | smaller⟩ := covered value member
  · subst value; exact bounded original originalMember
  · exact trans (r := r) rt smaller (bounded original originalMember)

theorem Covered.trans {r : α → α → Prop}
    (rt : ∀ {a b c}, r a b → r b c → r a c)
    (first : Covered r xs ys) (second : Covered r ys zs) : Covered r xs zs := by
  intro value member
  obtain ⟨middle, middleMember, first⟩ := first value member
  obtain ⟨last, lastMember, second⟩ := second middle middleMember
  refine ⟨last, lastMember, ?_⟩
  rcases first with rfl | first
  · exact second
  rcases second with rfl | second
  · exact .inr first
  · exact .inr (EquationWorldClosureOrder.trans (r := r) rt first second)

/-- A strict original-key decrease tolerates any finite number of already
covered captures. In particular repeated history merges require no credit. -/
theorem smaller_root {r : α → α → Prop}
    (rt : ∀ {a b c}, r a b → r b c → r a c)
    (smaller : r next key) (covered : Covered r nextCaptures captures) :
    Below r (.node next nextCaptures) (.node key captures) :=
  .root smaller (covered.below rt (fun _ member => .child member))

abbrev World (count : Nat) := Closure (EquationControlMeasure.Key count)
abbrev WorldBelow (count : Nat) := Below (@EquationControlMeasure.Less count)

theorem world_wellFounded (count : Nat) : WellFounded (WorldBelow count) :=
  wellFounded (EquationControlMeasure.wellFounded count)

/-- A comparison may replace one original call by several genuinely lower
calls, each retaining its own original world and captures. -/
abbrev CallBelow (count : Nat) := EquationWorldPolynomial.Less (WorldBelow count)

theorem call_wellFounded (count : Nat) : WellFounded (CallBelow count) :=
  EquationWorldPolynomial.wellFounded (world_wellFounded count)

theorem split_call {parent : World count} {calls : List (World count)}
    (smaller : ∀ child ∈ calls, WorldBelow count child parent) :
    CallBelow count calls [parent] := EquationWorldPolynomial.lower_mass smaller

/-- Ordinary closure descent keeps the world controls fixed. Captured
worlds may have larger cutoffs than this original's source. -/
theorem original_child (smaller : nextSchedule < schedule)
    (count cutoff : Nat) (fuel : Nat → Nat) (constants : Nat)
    (captures : List (World count)) :
    WorldBelow count
      (.node (EquationControlMeasure.key count cutoff fuel constants nextSchedule) captures)
      (.node (EquationControlMeasure.key count cutoff fuel constants schedule) captures) :=
  smaller_root (r := @EquationControlMeasure.Less count) EquationControlMeasure.less_trans
    (EquationControlMeasure.scheduleDecrease smaller count cutoff fuel constants)
    (Covered.refl captures)

/-- A canonical opening may borrow any finite set of proper caller
children. The canonical proof's schedule is arbitrary, including the cost
of evaluating it under those captures. No canonical/caller cutoff is joined.
This supplies the measure edge; constructing the corresponding query and
its hereditary frame evidence remains the compiler's obligation. -/
theorem opening_with_caller_captures
    {head count cutoff : Nat} {fuel children : Nat → Nat}
    (headPositive : 0 < head) (headBound : head ≤ count) (cutoffBound : cutoff ≤ count)
    (incoming : EquationStratifiedFuel.WithinAbove cutoff fuel
      (EquationStratifiedFuel.headDepth head children))
    (constants schedule canonicalConstants canonicalSchedule : Nat)
    (callerSchedules : List Nat) (proper : ∀ cost ∈ callerSchedules, cost < schedule)
    (captures : List (World count)) :
    WorldBelow count
      (.node (EquationControlMeasure.key count (head - 1) children canonicalConstants canonicalSchedule)
        (callerSchedules.map (fun cost =>
          .node (EquationControlMeasure.key count cutoff fuel constants cost) captures) ++ captures))
      (.node (EquationControlMeasure.key count cutoff fuel constants schedule) captures) := by
  apply Below.root
    (EquationStratifiedFuel.openingDecrease headPositive headBound cutoffBound incoming
      constants schedule canonicalConstants canonicalSchedule)
  intro child member
  rcases List.mem_append.mp member with member | member
  · obtain ⟨cost, costMember, rfl⟩ := List.mem_map.mp member
    exact original_child (proper cost costMember) count cutoff fuel constants captures
  · exact .child member

/-- Uses refer to existing sponsors; they do not insert copies of those
sponsors into the measured call frontier. This distinguishes query-owned
children from newly captured destination-frame owners. -/
def Sponsored (frontier uses : List (World count)) : Prop :=
  ∀ child ∈ uses, ∃ sponsor ∈ frontier, WorldBelow count child sponsor

theorem Sponsored.merge (left : Sponsored frontier xs) (right : Sponsored frontier ys) :
    Sponsored frontier (xs ++ ys) := by
  intro child member
  rcases List.mem_append.mp member with member | member
  · exact left child member
  · exact right child member

theorem Sponsored.duplicate (bounded : Sponsored frontier uses) :
    Sponsored frontier (uses ++ uses) := bounded.merge bounded

/-- Following R by destination F may retain query children funded only by
the source original. Keep that source sponsor separate, lower the actual
destination schedule, and retain the destination's original captures.
The foreign children are never reparented below the destination world. -/
theorem sponsored_continuation
    (source : World count) (cutoff : Nat) (fuel : Nat → Nat) (constants : Nat)
    {schedule nextSchedule : Nat} (smaller : nextSchedule < schedule)
    (captures nextCaptures foreignUses : List (World count))
    (covered : Covered (@EquationControlMeasure.Less count) nextCaptures captures)
    (foreignBound : ∀ child ∈ foreignUses, WorldBelow count child source) :
    let destination := Closure.node
      (EquationControlMeasure.key count cutoff fuel constants schedule) captures
    let next := Closure.node
      (EquationControlMeasure.key count cutoff fuel constants nextSchedule) nextCaptures
    CallBelow count [source, next] [source, destination] ∧
      Sponsored [source, next] (foreignUses ++ nextCaptures) := by
  dsimp only
  constructor
  · apply EquationWorldPolynomial.Less.cons
    exact EquationWorldPolynomial.lower_mass (by
      intro child member
      have equal := List.mem_singleton.mp member
      subst child
      exact smaller_root (r := @EquationControlMeasure.Less count) EquationControlMeasure.less_trans
        (EquationControlMeasure.scheduleDecrease smaller count cutoff fuel constants) covered)
  · apply Sponsored.merge
    · intro child member
      exact ⟨source, List.mem_cons_self, foreignBound child member⟩
    · intro child member
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, .child member⟩

end Lean4Lean.VEnv.EquationWorldClosureOrder
