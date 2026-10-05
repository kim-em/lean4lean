import Lean4Lean.Theory.Typing.AnchoredOriginalSortableFamilyDeclaredReplay

/-! Literal finite source cut observations are collected into rich family
spine seeds. The ledger contains source syntax, not a semantic supplier. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure SortableSeedCover (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (argument : VExpr) (needs : List Need) (minimum : Nat) where
  seed : SortableArgumentSeed env U registry target locals σ available argument
  bound : minimum ≤ seed.rank
  covered : ∀ need ∈ needs, need.rank ≤ seed.rank ∧
    ∀ atom ∈ (need.atGrade seed.rank).atoms, atom ∈ seed.demand.atoms

/-- Finite collection chooses its grade only after every actual observation
has been obtained. All returned leaves remain in the original valuation. -/
theorem SortableArgumentSeed.collect
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {argument : VExpr} (needs : List Need) (minimum : Nat)
    (observations : ∀ need ∈ needs, ∃ footprint,
      Nonempty (SortableObs env U registry target locals σ argument need.profile footprint) ∧
      footprint.Available available) :
    Nonempty (SortableSeedCover env U registry target locals σ available argument needs minimum) := by
  induction needs with
  | nil =>
    exact ⟨⟨⟨minimum, .empty, [], .legacy .empty, (fun _ _ h => nomatch h)⟩,
      Nat.le_refl _, (fun _ h => nomatch h)⟩⟩
  | cons need needs ih =>
    obtain ⟨tail⟩ := ih (fun need member => observations need (List.mem_cons_of_mem _ member))
    obtain ⟨footprint, ⟨observation⟩, resources⟩ := observations need List.mem_cons_self
    let N := max need.rank tail.seed.rank
    have hn : need.rank ≤ N := Nat.le_max_left _ _
    have ht : tail.seed.rank ≤ N := Nat.le_max_right _ _
    refine ⟨{
      seed := {
        rank := N
        demand := (raiseProfile N hn need.profile).union (raiseProfile N ht tail.seed.demand)
        footprint := footprint ++ tail.seed.footprint
        observation := .union (observation.raise hn) (tail.seed.observation.raise ht)
        resources := fun i n member => (List.mem_append.mp member).elim
          (resources i n) (tail.seed.resources i n) }
      bound := Nat.le_trans tail.bound ht
      covered := ?_ }⟩
    intro requested member
    rcases List.mem_cons.mp member with rfl | member
    · refine ⟨hn, ?_⟩
      simpa only [Need.atGrade, dif_pos hn, Profile.union, Profile.atoms, Profile.mk] using
        (fun atom (ha : atom ∈ (raiseProfile N hn requested.profile).atoms) =>
          List.mem_append_left (raiseProfile N ht tail.seed.demand) ha)
    · obtain ⟨low, included⟩ := tail.covered requested member
      refine ⟨Nat.le_trans low ht, ?_⟩
      rw [Need.atGrade_raise requested ht low]
      intro atom ha
      exact List.mem_append_right _ (raiseProfile_subset ht included atom ha)

inductive SortableArgumentLedger (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (arguments : List VExpr) : Footprint → Type where
  | nil : SortableArgumentLedger env U registry target locals σ available arguments []
  | cons {index : Nat} {need : Need} {footprint required : Footprint}
      (bound : index < arguments.length)
      (observation : SortableObs env U registry target locals σ
        arguments[arguments.length - 1 - index] need.profile footprint)
      (resources : footprint.Available available)
      (tail : SortableArgumentLedger env U registry target locals σ available arguments required) :
      SortableArgumentLedger env U registry target locals σ available arguments ((index, need) :: required)

def SortableArgumentLedger.append
    (left : SortableArgumentLedger env U registry target locals σ available arguments first)
    (right : SortableArgumentLedger env U registry target locals σ available arguments second) :
    SortableArgumentLedger env U registry target locals σ available arguments (first ++ second) :=
  match left with
  | .nil => right
  | .cons bound observation resources tail => .cons bound observation resources (tail.append right)

theorem SortableArgumentLedger.observation
    (ledger : SortableArgumentLedger env U registry target locals σ available arguments required)
    (member : (index, need) ∈ required) :
    ∃ bound : index < arguments.length, ∃ footprint,
      Nonempty (SortableObs env U registry target locals σ
        arguments[arguments.length - 1 - index] need.profile footprint) ∧
        footprint.Available available := by
  induction ledger with
  | nil => cases member
  | cons bound observation resources tail ih =>
    rcases List.mem_cons.mp member with same | member
    · cases same; exact ⟨bound, _, ⟨observation⟩, resources⟩
    · exact ih member

theorem SortableArgumentLedger.scoped
    (ledger : SortableArgumentLedger env U registry target locals σ available arguments required) :
    Footprint.Scoped arguments.length required := by
  intro index need member
  exact (ledger.observation member).choose

/-- Shift a prefix ledger into the full native tuple without changing a
single original source observation. -/
noncomputable def SortableArgumentLedger.intoPrefix
    {arguments prefixArguments : List VExpr}
    (prefix_eq : prefixArguments = arguments.take count) (count_le : count ≤ arguments.length)
    (ledger : SortableArgumentLedger env U registry target locals σ available prefixArguments required) :
    SortableArgumentLedger env U registry target locals σ available arguments
      (Footprint.sourceLift (.skipN .refl (arguments.length - count)) required) := by
  subst prefixArguments
  induction ledger with
  | nil => exact .nil
  | @cons index need footprint required bound observation resources tail ih =>
    have small : index < count := by simpa only [List.length_take, Nat.min_eq_left count_le] using bound
    have hi : index + (arguments.length - count) < arguments.length := by omega
    have position : arguments.length - 1 - (index + (arguments.length - count)) = count - 1 - index := by omega
    have observed : SortableObs env U registry target locals σ
        arguments[arguments.length - 1 - (index + (arguments.length - count))] need.profile footprint := by
      simpa only [List.length_take, Nat.min_eq_left count_le, List.getElem_take, position] using observation
    simpa only [Footprint.sourceLift, List.map_cons, Lift.liftVar_skipN, Lift.liftVar,
      Nat.zero_add, Nat.add_comm] using SortableArgumentLedger.cons hi observed resources ih

noncomputable def SortableArgumentLedger.withoutLast
    (ledger : SortableArgumentLedger env U registry target locals σ available (arguments ++ [last]) required) :
    SortableArgumentLedger env U registry target locals σ available arguments (externalArguments required) := by
  induction ledger with
  | nil => exact .nil
  | @cons index need footprint required bound observation resources tail ih =>
    cases index with
    | zero => exact ih
    | succ index =>
      have hi : index < arguments.length := by simpa only [List.length_append, List.length_singleton,
        Nat.add_lt_add_iff_right] using bound
      have position : (arguments ++ [last]).length - 1 - (index + 1) = arguments.length - 1 - index := by
        simp only [List.length_append, List.length_singleton]; omega
      have observed : SortableObs env U registry target locals σ arguments[arguments.length - 1 - index]
          need.profile footprint := by
        have beforeBound : (arguments ++ [last]).length - 1 - (index + 1) < arguments.length := by
          simp only [List.length_append, List.length_singleton]; omega
        have same : (arguments ++ [last])[(arguments ++ [last]).length - 1 - (index + 1)] =
            arguments[arguments.length - 1 - index] := by
          simp only [position]
          exact List.getElem_append_left (by omega)
        exact same ▸ observation
      exact .cons hi observed resources ih

theorem SortableArgumentLedger.lastSeed
    (ledger : SortableArgumentLedger env U registry target locals σ available (arguments ++ [last]) required)
    (minimum : Nat) :
    Nonempty (SortableSeedCover env U registry target locals σ available last
      (argumentNeeds required 0) minimum) := by
  apply SortableArgumentSeed.collect
  intro need member
  obtain ⟨bound, footprint, ⟨observation⟩, resources⟩ := ledger.observation (mem_argumentNeeds.mp member)
  exact ⟨footprint, ⟨by simpa using observation⟩, resources⟩

theorem SortableArgumentLedger.spineSeeds
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {expression : VExpr} {name : Name} {levels : List VLevel}
    (head : expression.getAppFnArgs.1 = .const name levels)
    {required : Footprint}
    (ledger : SortableArgumentLedger env U registry target locals σ available expression.getAppFnArgs.2 required)
    (minimum : Nat) :
    ∃ seeds : SortableSpineSeeds env U registry target locals σ available expression,
      SortableSpineSeedCoverage seeds required := by
  induction expression generalizing required with
  | const actual actualLevels =>
    simp only [getAppFnArgs_const] at head
    cases head
    have empty : required = [] := by
      cases required with
      | nil => rfl
      | cons entry tail =>
        obtain ⟨index, need⟩ := entry
        have bad := ledger.scoped index need List.mem_cons_self
        simp only [getAppFnArgs_const, List.length_nil] at bad
        omega
    subst required
    exact ⟨.constant, .constant⟩
  | app f a ihF ihA =>
    simp only [getAppFnArgs_app] at head ledger
    obtain ⟨cover⟩ := ledger.lastSeed minimum
    obtain ⟨function, covered⟩ := ihF head ledger.withoutLast
    exact ⟨.app function cover.seed, .app covered
      (fun need member => (cover.covered need (mem_argumentNeeds.mpr member)).1)
      (fun need member => (cover.covered need (mem_argumentNeeds.mpr member)).2)⟩
  | bvar | sort | lam | forallE | proj | elim =>
    simp only [getAppFnArgs] at head
    contradiction


end Lean4Lean.AnchoredSource.Adapted
