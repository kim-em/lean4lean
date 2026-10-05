import Lean4Lean.Theory.Typing.AnchoredFlatSorts

/-! Bare universe covers at an explicitly chosen finite rank. -/
namespace Lean4Lean.AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

def Profile.sortsAt (n : Nat) (flags : List Bool) : Profile n :=
  flags.flatMap fun flag => Profile.sort flag

def Profile.flatSortsAt (m : Nat) (profile : Profile n) : Profile m :=
  Profile.sortsAt m profile.sortFlags

@[simp] theorem Profile.sortsAt_nil : Profile.sortsAt n [] = .empty := rfl

@[simp] theorem Profile.sortsAt_cons :
    Profile.sortsAt n (flag :: flags) = (Profile.sort flag).union (Profile.sortsAt n flags) := rfl

@[simp] theorem Profile.sortsAt_down :
    (Profile.sortsAt (n + 1) flags).down = Profile.sortsAt n flags := by
  induction flags with
  | nil => rfl
  | cons flag flags ih =>
    rw [sortsAt_cons, Profile.down_union, Profile.down_sort, ih, sortsAt_cons]

@[simp] theorem Profile.sortsAt_rename :
    (Profile.sortsAt n flags).rename ρ = Profile.sortsAt n flags := by
  induction flags with
  | nil => rfl
  | cons flag flags ih =>
    rw [sortsAt_cons, Profile.rename_union, Profile.rename_sort, ih]

@[simp] theorem Profile.flatSortsAt_rename (profile : Profile n) :
    (profile.rename ρ).flatSortsAt m = (profile.flatSortsAt m).rename ρ := by
  simp only [flatSortsAt, Profile.sortFlags_rename, sortsAt_rename]

theorem Profile.sortsAt_wf : (Profile.sortsAt n flags).WF := by
  cases n with
  | zero => trivial
  | succ n =>
    intro atom member
    obtain ⟨flag, _, member⟩ := List.mem_flatMap.mp member
    cases List.mem_singleton.mp member
    trivial

theorem Profile.HasType.sortsAt_iff {value : Profile n} :
    value.HasType (Profile.sortsAt n flags) ↔
      value.WF ∧ ∀ atom ∈ value.atoms,
        ∃ flag ∈ flags, (Profile.singleton atom).HasType (.sort flag) := by
  cases n with
  | zero =>
    constructor
    · intro typed
      refine ⟨typed.wf_value, ?_⟩
      intro atom member
      obtain ⟨flag, member, equal⟩ := typed atom member
      have member' : flag ∈ flags := by
        simpa [Profile.sortsAt, Profile.sort, Profile.atoms] using member
      exact ⟨flag, member', fun _ _ => ⟨flag, List.mem_singleton_self _, equal⟩⟩
    · rintro ⟨_, typed⟩ atom member
      obtain ⟨flag, member, cover⟩ := typed atom member
      obtain ⟨actual, actualMember, equal⟩ := cover atom (List.mem_singleton_self _)
      cases List.mem_singleton.mp actualMember
      exact ⟨flag, by simpa [Profile.sortsAt, Profile.sort, Profile.atoms] using member, equal⟩
  | succ n =>
    constructor
    · intro typed
      refine ⟨typed.wf_value, ?_⟩
      intro atom member
      obtain ⟨cover, coverMember, covered⟩ := typed.2.2 atom member
      obtain ⟨flag, flagMember, coverMember⟩ := List.mem_flatMap.mp coverMember
      cases List.mem_singleton.mp coverMember
      refine ⟨flag, flagMember, (typed.singleton_of_mem member).wf_value,
        Profile.WF.sort (n := n + 1) flag, ?_⟩
      intro actual h
      cases List.mem_singleton.mp h
      exact ⟨.sort flag, List.mem_singleton_self _, covered⟩
    · rintro ⟨wf, typed⟩
      refine ⟨wf, Profile.sortsAt_wf (n := n + 1) (flags := flags), ?_⟩
      intro atom member
      obtain ⟨flag, flagMember, cover⟩ := typed atom member
      obtain ⟨actual, actualMember, covered⟩ := cover.2.2 atom (List.mem_singleton_self _)
      exact ⟨actual, List.mem_flatMap.mpr ⟨flag, flagMember, actualMember⟩, covered⟩

theorem Profile.HasType.sortAt {n m : Nat}
    (typed : (Profile.sort (n := n) flag).HasType (.sort relevant)) :
    (Profile.sort (n := m) flag).HasType (.sort relevant) := by
  have equal : relevant = true := by
    cases n with
    | zero =>
      obtain ⟨_, member, equal⟩ := typed flag (List.mem_singleton_self _)
      cases List.mem_singleton.mp member
      exact equal
    | succ n =>
      obtain ⟨_, member, equal⟩ := typed.2.2 (.sort flag) (List.mem_singleton_self _)
      cases List.mem_singleton.mp member
      exact equal
  subst relevant
  exact Profile.HasType.sort flag

theorem Profile.HasType.flatSortsAt_sort {profile : Profile n}
    (typed : profile.HasType (.sort relevant)) :
    (profile.flatSortsAt m).HasType (.sort relevant) := by
  have build (flags : List Bool) (included : List.Subset flags profile.sortFlags) :
      (Profile.sortsAt m flags).HasType (.sort relevant) := by
    induction flags with
    | nil => exact Profile.HasType.empty (Profile.WF.sort relevant)
    | cons head tail ih =>
      exact ((typed.sortFlag (included List.mem_cons_self)).sortAt).union
        (ih (fun _ h => included (List.mem_cons_of_mem _ h)))
  exact build _ (fun _ h => h)

end Lean4Lean.AnchoredProfiles

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles

theorem TypeRelated.sortAt {n m : Nat}
    (henv : env.Ordered)
    (code : TypeRelated env U registry Γ left right (Profile.sort (n := n) flag)) :
    TypeRelated env U registry Γ left right (Profile.sort (n := m) flag) := by
  have base : TypeRelated env U registry Γ left right (Profile.sort (n := 0) flag) := by
    induction n with
    | zero => exact code
    | succ n ih => exact ih (by simpa only [Profile.down_sort] using code.down henv)
  induction m with
  | zero => exact base
  | succ m ih => exact ih.sortPad

theorem TypeRelated.flatSortsAt {profile : Profile n}
    (henv : env.Ordered) (code : TypeRelated env U registry Γ left right profile) :
    TypeRelated env U registry Γ left right (profile.flatSortsAt m) := by
  apply TypeRelated.of_singletons
  intro atom member
  obtain ⟨flag, flagMember, atomMember⟩ := List.mem_flatMap.mp member
  exact ((code.sortFlag henv flagMember).sortAt henv).singleton atomMember

end Lean4Lean.AnchoredSemantics
