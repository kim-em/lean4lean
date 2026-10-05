import Lean4Lean.Theory.Typing.AnchoredNativeTemplateFactor
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceFactorArguments

/-! Every factored native-argument demand retains an actual original source
observation. Its leaves are drawn from the original certificate footprint;
the remaining native-prefix requirements are kept distinct from those leaves. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private theorem InstFootprint.above
    (factor : InstFootprint env U registry Γ locals σ argument depth before after)
    (member : (index + depth + 1, need) ∈ after) : (index + depth, need) ∈ before := by
  induction factor with
  | nil => cases member
  | keep i n tail ih =>
    rcases List.mem_cons.mp member with eq | member
    · have pair := Prod.mk.inj eq
      have position := pair.1
      unfold insertIndex at position
      split at position <;> rename_i bound
      · omega
      · have same : i = index + depth := by omega
        subst i
        exact List.mem_cons.mpr (.inl (congrArg (Prod.mk _) pair.2))
    · exact List.mem_cons_of_mem _ (ih member)
  | cut observation tail ih =>
    rcases List.mem_cons.mp member with eq | member
    · have := (Prod.mk.inj eq).1
      omega
    · exact List.mem_append_right _ (ih member)

private theorem InstFootprint.belowCut
    (factor : InstFootprint env U registry Γ locals σ argument depth before after)
    (bound : index < depth) (member : (index, need) ∈ after) : (index, need) ∈ before := by
  induction factor with
  | nil => cases member
  | keep i n tail ih =>
    rcases List.mem_cons.mp member with eq | member
    · have pair := Prod.mk.inj eq
      have position := pair.1
      unfold insertIndex at position
      split at position <;> rename_i hi
      · exact List.mem_cons.mpr (.inl (Prod.ext position pair.2))
      · omega
    · exact List.mem_cons_of_mem _ (ih member)
  | cut observation tail ih =>
    rcases List.mem_cons.mp member with eq | member
    · have := (Prod.mk.inj eq).1
      omega
    · exact List.mem_append_right _ (ih member)

private theorem InstFootprint.atCut
    (factor : InstFootprint env U registry Γ locals σ argument depth before after)
    (member : (depth, need) ∈ after) :
    ∃ footprint, Nonempty (Obs env U registry Γ locals σ argument need.profile footprint) ∧
      ∀ i n, (i,n) ∈ footprint → (i + depth,n) ∈ before := by
  induction factor with
  | nil => cases member
  | keep i n tail ih =>
    rcases List.mem_cons.mp member with eq | member
    · have position := (Prod.mk.inj eq).1
      unfold insertIndex at position
      split at position <;> omega
    · obtain ⟨footprint, observation, included⟩ := ih member
      exact ⟨footprint, observation, fun i n hm => List.mem_cons_of_mem _ (included i n hm)⟩
  | @cut rank before after demand footprint observation tail ih =>
    rcases List.mem_cons.mp member with eq | member
    · have same := (Prod.mk.inj eq).2
      subst need
      exact ⟨footprint, ⟨observation⟩, fun i n hm => List.mem_append_left _
        (List.mem_map.mpr ⟨(i,n), hm, rfl⟩)⟩
    · obtain ⟨footprint, observation, included⟩ := ih member
      exact ⟨footprint, observation, fun i n hm => List.mem_append_right _ (included i n hm)⟩

/-- Original free-variable requirements remain outside the entire factored
argument prefix and return to their original source indices. -/
theorem ParamsFootprint.external
    (factor : ParamsFootprint env U registry Γ locals σ arguments before after)
    (member : (index + arguments.length, need) ∈ after) : (index, need) ∈ before := by
  induction factor with
  | nil => simpa only [List.length_nil, Nat.add_zero] using member
  | cons tail head ih =>
    apply ih
    apply head.above
    simpa only [List.length_cons, Nat.add_assoc] using member

/-- An argument requirement recovers an actual observation of that exact
source argument. No source observation is reconstructed from target typing. -/
theorem ParamsFootprint.argument
    (factor : ParamsFootprint env U registry Γ locals σ arguments before after)
    (bound : index < arguments.length) (member : (index, need) ∈ after) :
    ∃ footprint, Nonempty (Obs env U registry Γ locals σ
      arguments[arguments.length - 1 - index] need.profile footprint) ∧
      ∀ i n, (i,n) ∈ footprint → (i,n) ∈ before := by
  induction factor with
  | nil => cases Nat.not_lt_zero index bound
  | @cons arguments before middle argument after tail head ih =>
    by_cases equal : index = arguments.length
    · subst index
      obtain ⟨footprint, observation, included⟩ := head.atCut member
      refine ⟨footprint, ?_, fun i n hm => tail.external (included i n hm)⟩
      simpa only [List.length_cons, Nat.add_sub_cancel, Nat.sub_self, List.getElem_cons_zero] using observation
    · have below : index < arguments.length := by simp only [List.length_cons] at bound; omega
      obtain ⟨footprint, observation, included⟩ := ih below (head.belowCut below member)
      refine ⟨footprint, ?_, included⟩
      have position : (argument :: arguments).length - 1 - index =
          (arguments.length - 1 - index) + 1 := by simp only [List.length_cons]; omega
      simpa only [position, List.getElem_cons_succ] using observation

/-- A finite input assembled before a key is frozen. `outside` refers to the
remaining native arguments; only `argumentFootprint` uses the original source
valuation. These two resource spaces must not be conflated. -/
structure NativeArgumentPack (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (argument : VExpr) (required : Footprint) (minimum : Nat) where
  rank : Nat
  bound : minimum ≤ rank
  input : Profile rank
  argumentFootprint : Footprint
  observation : Obs env U registry target locals σ argument input argumentFootprint
  resources : argumentFootprint.Available available
  outside : Footprint
  pack : BinderPack rank input required outside

private theorem pack_last_argument
    (factor : ParamsFootprint env U registry Γ locals σ arguments before after)
    (nonempty : 0 < arguments.length) (available : Valuation)
    (resources : before.Available available) (minimum : Nat) (part : Footprint)
    (included : ∀ entry ∈ part, entry ∈ after) :
    Nonempty (NativeArgumentPack env U registry Γ locals σ available
      arguments[arguments.length - 1] part minimum) := by
  induction part with
  | nil => exact ⟨⟨minimum, Nat.le_refl _, .empty, [], .empty,
      (fun _ _ hm => nomatch hm), [], .nil⟩⟩
  | cons entry part ih =>
    obtain ⟨tail⟩ := ih (fun entry hm => included entry (List.mem_cons_of_mem _ hm))
    obtain ⟨index, need⟩ := entry
    cases index with
    | zero =>
      obtain ⟨footprint, ⟨observation⟩, leaves⟩ := factor.argument nonempty (included _ List.mem_cons_self)
      let N := max need.rank tail.rank
      have hn : need.rank ≤ N := Nat.le_max_left _ _
      have ht : tail.rank ≤ N := Nat.le_max_right _ _
      refine ⟨{
        rank := N
        bound := Nat.le_trans tail.bound ht
        input := (raiseProfile N hn need.profile).union (raiseProfile N ht tail.input)
        argumentFootprint := footprint ++ tail.argumentFootprint
        observation := .union (observation.raise hn) (tail.observation.raise ht)
        resources := ?_
        outside := tail.outside
        pack := ?_ }⟩
      · intro i n hm
        exact (List.mem_append.mp hm).elim (fun hm => resources i n (leaves i n hm))
          (tail.resources i n)
      · simpa only [Need.atGrade, dif_pos hn] using BinderPack.local need hn (tail.pack.raise ht)
    | succ index =>
      exact ⟨{
        rank := tail.rank
        bound := tail.bound
        input := tail.input
        argumentFootprint := tail.argumentFootprint
        observation := tail.observation
        resources := tail.resources
        outside := (index, need) :: tail.outside
        pack := .external index need tail.pack }⟩

/-- Collect all last-argument cuts at one finite grade, without modifying the
original valuation. Higher-grade cuts raise the entire finite input. -/
theorem ParamsFootprint.lastArgument
    (factor : ParamsFootprint env U registry Γ locals σ arguments before after)
    (nonempty : 0 < arguments.length) (available : Valuation)
    (resources : before.Available available) (minimum : Nat) :
    Nonempty (NativeArgumentPack env U registry Γ locals σ available
      arguments[arguments.length - 1] after minimum) :=
  pack_last_argument factor nonempty available resources minimum after (fun _ hm => hm)

end Lean4Lean.AnchoredSource.Adapted
