import Lean4Lean.Theory.Typing.AnchoredOriginalWorldProvenance
import Lean4Lean.Theory.Typing.EquationWorldClosureMonotonicity

/-! Static retained call budgets quantify over the actual selected frame.
Equal-cost capture reorganization is not a strict world decrease. Instead the
recursive motive ranges over every actual node bounded by one fixed retained
world. Strict children transfer to that fixed world, so the induction itself
still uses the checked well-founded closure order. -/
namespace Lean4Lean.VEnv.EquationWorldClosureOrder
set_option Elab.async false

/-- This is an input admissibility relation, not the recursive strict order.
In particular it allows duplicating a covered capture at an unchanged key. -/
def BoundedNode (r : α → α → Prop) : Closure α → Closure α → Prop
  | .node actual captures, .node baseline reserved =>
    (actual = baseline ∨ r actual baseline) ∧ Covered r captures reserved

theorem BoundedNode.refl (value : Closure α) : BoundedNode r value value := by
  cases value with
  | node key captures => exact ⟨.inl rfl, Covered.refl captures⟩

/-- A genuinely smaller actual child is below the original retained budget.
No strict same-key edge between the two parents is asserted. -/
theorem BoundedNode.child
    {r : α → α → Prop} (rt : ∀ {a b c}, r a b → r b c → r a c)
    {actual baseline child : Closure α} (bound : BoundedNode r actual baseline)
    (smaller : Below r child actual) : Below r child baseline := by
  cases actual with
  | node key captures =>
    cases baseline with
    | node other reserved => exact Below.retarget (r := r) rt bound.1 bound.2 smaller

theorem BoundedNode.captures
    {r : α → α → Prop} (rt : ∀ {a b c}, r a b → r b c → r a c)
    {key : α} {captures : List (Closure α)} {baseline : Closure α}
    (bound : BoundedNode r (.node key captures) baseline) :
    ∀ child ∈ captures, Below r child baseline :=
  fun _ member => BoundedNode.child (r := r) rt bound (.child member)

/-- Well-founded induction with a fixed retained budget and an actual input.
The step must prove the result for every admissible actual input; this is the
stronger contract needed by selected-frame replay, not a coercion from an old
bank quantified only at an exact frame. -/
theorem boundedNodeInduction
    {r : α → α → Prop} (wf : WellFounded r)
    {motive : Closure α → Prop}
    (step : ∀ baseline : Closure α,
      (∀ smaller, Below r smaller baseline →
        ∀ actual, BoundedNode r actual smaller → motive actual) →
      ∀ actual, BoundedNode r actual baseline → motive actual) :
    ∀ baseline actual, BoundedNode r actual baseline → motive actual := by
  intro baseline
  induction baseline using (wellFounded wf).induction with
  | h baseline ih => exact step baseline ih

/-- Existing sponsors also fund strict uses made by a bounded actual input.
The reserved baseline itself is never inserted into a new frontier. -/
theorem BoundedNode.sponsored
    {actual baseline : World count} (bound : BoundedNode (@EquationControlMeasure.Less count) actual baseline)
    {frontier uses : List (World count)}
    (reserved : Sponsored frontier [baseline])
    (usesBelow : ∀ child ∈ uses, WorldBelow count child actual) : Sponsored frontier uses := by
  obtain ⟨sponsor, member, lower⟩ := reserved baseline (List.mem_singleton_self _)
  intro child belongs
  exact ⟨sponsor, member, trans (r := @EquationControlMeasure.Less count)
    EquationControlMeasure.less_trans (BoundedNode.child (r := @EquationControlMeasure.Less count) EquationControlMeasure.less_trans bound (usesBelow child belongs)) lower⟩

/-- The missing edge is real even for duplicate captures with identical keys.
This is why `BoundedNode` is a motive precondition rather than a claimed
`Covered` or strict-decrease theorem about the reorganized parent. -/
theorem duplicateCapture_not_covered
    {r : α → α → Prop} (key : α) (irreflexive : ¬ r key key) :
    let leaf : Closure α := .node key []
    let baseline : Closure α := .node key [leaf]
    let actual : Closure α := .node key [leaf, leaf]
    BoundedNode r actual baseline ∧ ¬ Covered r [actual] [baseline] := by
  dsimp only
  constructor
  · refine ⟨.inl rfl, ?_⟩
    intro child member
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
    subst child
    exact ⟨_, List.mem_singleton_self _, .inl rfl⟩
  · intro covered
    obtain ⟨old, member, same | smaller⟩ := covered _ (List.mem_singleton_self _)
    · have oldEq := List.mem_singleton.mp member
      have equality := same.trans oldEq
      have lengths := congrArg List.length (Closure.node.inj equality).2
      simp at lengths
    · have oldEq := List.mem_singleton.mp member
      subst old
      cases smaller with
      | child member =>
        have equality := List.mem_singleton.mp member
        have lengths := congrArg List.length (Closure.node.inj equality).2
        simp at lengths
      | under member lower =>
        have equality := List.mem_singleton.mp member
        subst equality
        cases lower with
        | child member => cases member
        | under member _ => cases member
        | root smaller _ => exact irreflexive smaller
      | root smaller _ => exact irreflexive smaller

end Lean4Lean.VEnv.EquationWorldClosureOrder

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv OriginalClosureMeasure EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- Concrete selected-frame admission at the SAME original endpoint, phase,
cutoff and fuel. Both ledgers are actual typed provenance; a mere numerical
capacity bound is deliberately insufficient. -/
theorem originalCallWorld_boundedNode
    (controls : OriginalWorldControls strata sourceEnv) (phase : RichPhase)
    (node : EndpointState sourceEnv U source expression assigned)
    (actual : WorldEnvironmentProvenance strata U actualEnvironment)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost actualEnvironment ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) actual.worlds baseline.worlds) :
    BoundedNode (@EquationControlMeasure.Less strata.rules.length)
      (originalCallWorld controls phase node actual) (originalCallWorld controls phase node baseline) := by
  have cost : (Closure.close (node.dependencyOrigin controls.ordered) actualEnvironment).cost ≤
      (Closure.close (node.dependencyOrigin controls.ordered) baselineEnvironment).cost :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_left capacity 1)
  have schedule : richSchedule phase (Closure.close (node.dependencyOrigin controls.ordered) actualEnvironment).cost ≤
      richSchedule phase (Closure.close (node.dependencyOrigin controls.ordered) baselineEnvironment).cost := by
    simp only [richSchedule]
    omega
  refine ⟨?_, covered⟩
  rcases Nat.eq_or_lt_of_le schedule with equal | smaller
  · exact .inl (congrArg (EquationControlMeasure.key strata.rules.length controls.cutoff controls.fuel
      controls.ordered.constantCount) equal)
  · exact .inr (EquationControlMeasure.scheduleDecrease smaller _ _ _ _)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
