import Lean4Lean.Theory.Typing.AnchoredNativeSeededSpine

/-! Initial capture routing collects actual original source observations.
The resulting finite seed covers every requested grade literally; no target
typing theorem is used to manufacture an observation of a computed index. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

def argumentNeeds (footprint : Footprint) (index : Nat) : List Need :=
  (footprint.filter (fun entry => entry.1 == index)).map Prod.snd

theorem mem_argumentNeeds : need ∈ argumentNeeds footprint index ↔ (index, need) ∈ footprint := by
  simp only [argumentNeeds, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨⟨i, n⟩, ⟨member, rfl⟩, rfl⟩; exact member
  · intro member; exact ⟨(index, need), ⟨member, rfl⟩, rfl⟩

structure NativeSeedCover (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (argument : VExpr) (needs : List Need) (minimum : Nat) where
  seed : NativeArgumentSeed env U registry target locals σ available argument
  bound : minimum ≤ seed.rank
  covered : ∀ need ∈ needs, need.rank ≤ seed.rank ∧
    ∀ atom ∈ (need.atGrade seed.rank).atoms, atom ∈ seed.demand.atoms

/-- Finite collection chooses its grade only after every actual observation
has been obtained. All returned leaves remain in the original valuation. -/
theorem NativeArgumentSeed.collect
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {argument : VExpr} (needs : List Need) (minimum : Nat)
    (observations : ∀ need ∈ needs, ∃ footprint,
      Nonempty (Obs env U registry target locals σ argument need.profile footprint) ∧
      footprint.Available available) :
    Nonempty (NativeSeedCover env U registry target locals σ available argument needs minimum) := by
  induction needs with
  | nil =>
    exact ⟨⟨⟨minimum, .empty, [], .empty, (fun _ _ h => nomatch h)⟩,
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

/-- Collect precisely the demands on one original field variable. This
constructs actual variable observations, rather than assuming a seed packet. -/
theorem NativeArgumentSeed.variable
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (required : Footprint) (resources : required.Available available)
    (index minimum : Nat) :
    Nonempty (NativeSeedCover env U registry target locals σ available (.bvar index)
      (argumentNeeds required index) minimum) := by
  apply NativeArgumentSeed.collect
  intro need member
  exact ⟨[(index, need)], ⟨.var locals σ index need.profile⟩, by
    intro i n hm
    cases List.mem_singleton.mp hm
    exact resources index need (mem_argumentNeeds.mp member)⟩

/-- Every demanded native prefix argument, including a computed expression,
comes from an actual cut in the retained original template certificate. -/
theorem ParamsFootprint.argumentSeed
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {arguments : List VExpr} {before after : Footprint}
    (cuts : ParamsFootprint env U registry target locals σ arguments before after)
    (resources : before.Available available)
    {index : Nat} (bound : index < arguments.length) (minimum : Nat) :
    Nonempty (NativeSeedCover env U registry target locals σ available
      arguments[arguments.length - 1 - index] (argumentNeeds after index) minimum) := by
  apply NativeArgumentSeed.collect
  intro need member
  obtain ⟨footprint, observation, included⟩ := cuts.argument bound (mem_argumentNeeds.mp member)
  exact ⟨footprint, observation, fun i n hm => resources i n (included i n hm)⟩

noncomputable def NativeArgumentSeed.union
    (left right : NativeArgumentSeed env U registry target locals σ available argument) :
    NativeArgumentSeed env U registry target locals σ available argument where
  rank := max left.rank right.rank
  demand := (raiseProfile _ (Nat.le_max_left _ _) left.demand).union
    (raiseProfile _ (Nat.le_max_right _ _) right.demand)
  footprint := left.footprint ++ right.footprint
  observation := .union (left.observation.raise (Nat.le_max_left _ _))
    (right.observation.raise (Nat.le_max_right _ _))
  resources := fun i need member => (List.mem_append.mp member).elim
    (left.resources i need) (right.resources i need)

/-- Capture-domain cuts and computational body demands combine as actual
observations at one grade, retaining both sets of literal coverage proofs. -/
noncomputable def NativeSeedCover.union
    (left : NativeSeedCover env U registry target locals σ available argument first minimum)
    (right : NativeSeedCover env U registry target locals σ available argument second minimum) :
    NativeSeedCover env U registry target locals σ available argument (first ++ second) minimum where
  seed := left.seed.union right.seed
  bound := Nat.le_trans left.bound (Nat.le_max_left _ _)
  covered := by
    intro need member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨bound, included⟩ := left.covered need member
      refine ⟨Nat.le_trans bound (Nat.le_max_left _ _), ?_⟩
      change ∀ atom ∈ (need.atGrade (max left.seed.rank right.seed.rank)).atoms, _
      rw [Need.atGrade_raise need (Nat.le_max_left _ _) bound]
      intro atom ha
      exact List.mem_append_left _ (raiseProfile_subset (Nat.le_max_left _ _) included atom ha)
    · obtain ⟨bound, included⟩ := right.covered need member
      refine ⟨Nat.le_trans bound (Nat.le_max_right _ _), ?_⟩
      change ∀ atom ∈ (need.atGrade (max left.seed.rank right.seed.rank)).atoms, _
      rw [Need.atGrade_raise need (Nat.le_max_right _ _) bound]
      intro atom ha
      exact List.mem_append_right _ (raiseProfile_subset (Nat.le_max_right _ _) included atom ha)

noncomputable def NativeSpineSeeds.union
    (left right : NativeSpineSeeds env U registry target locals σ available expression) :
    NativeSpineSeeds env U registry target locals σ available expression := by
  match left, right with
  | .constant, .constant => exact .constant
  | .app leftFn leftArg, .app rightFn rightArg =>
    exact .app (leftFn.union rightFn) (leftArg.union rightArg)
termination_by sizeOf expression

end Lean4Lean.AnchoredSource.Adapted
