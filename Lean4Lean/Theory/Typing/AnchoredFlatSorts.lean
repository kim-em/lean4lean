import Lean4Lean.Theory.Typing.AnchoredSortCodeGrades

/-! A computed support for code actions. Only sort covers already present in
the input survive; explicit padding is flattened using sort-grade promotion.
This operation does not manufacture a universe cover from raw typing. -/
namespace Lean4Lean.AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

def Profile.sortFlags : {n : Nat} → Profile n → List Bool
  | 0, profile => profile
  | _ + 1, profile => profile.down.sortFlags

def Profile.flatSorts (profile : Profile n) : Profile n :=
  profile.sortFlags.flatMap fun flag => Profile.sort flag

@[simp] theorem Profile.sortFlags_sort (flag : Bool) :
    (Profile.sort (n := n) flag).sortFlags = [flag] := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [sortFlags, Profile.down_sort] using ih

@[simp] theorem Profile.sortFlags_union (left right : Profile n) :
    (left.union right).sortFlags = left.sortFlags ++ right.sortFlags := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [sortFlags, Profile.down_union] using ih left.down right.down

@[simp] theorem Profile.sortFlags_empty : (Profile.empty (n := n)).sortFlags = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [sortFlags, Profile.down_empty] using ih

@[simp] theorem Profile.sortFlags_rename (profile : Profile n) (ρ : Lift) :
    (profile.rename ρ).sortFlags = profile.sortFlags := by
  induction n with
  | zero => simp [sortFlags, Profile.rename, Atom.rename, id]
  | succ n ih => simpa only [sortFlags, Profile.down_rename] using ih profile.down

@[simp] theorem Profile.flatSorts_rename (profile : Profile n) (ρ : Lift) :
    (profile.rename ρ).flatSorts = profile.flatSorts.rename ρ := by
  unfold Profile.flatSorts
  rw [Profile.sortFlags_rename]
  simp only [Profile.rename, List.map_flatMap]
  congr 1
  funext flag
  exact (Profile.rename_sort flag).symm

theorem Profile.sortFlags_mono {left right : Profile n} (included : List.Subset left right) :
    List.Subset (Profile.sortFlags (n := n) left) right.sortFlags := by
  induction n with
  | zero => exact included
  | succ n ih =>
    apply ih
    intro atom member
    obtain ⟨source, sourceMember, member⟩ := Profile.mem_down_iff.mp member
    exact Profile.mem_down_iff.mpr ⟨source, included sourceMember, member⟩

theorem Profile.flatSorts_wf (profile : Profile n) : profile.flatSorts.WF := by
  cases n with
  | zero => trivial
  | succ n =>
    intro atom member
    obtain ⟨flag, _, member⟩ := List.mem_flatMap.mp member
    cases List.mem_singleton.mp member
    trivial

theorem Profile.flatSorts_formed (profile : Profile n) :
    profile.flatSorts.HasType (.sort true) := by
  cases n with
  | zero => exact fun _ _ => ⟨true, List.mem_singleton_self _, rfl⟩
  | succ n =>
    refine ⟨profile.flatSorts_wf, Profile.WF.sort (n := n + 1) true, ?_⟩
    intro atom member
    obtain ⟨flag, _, member⟩ := List.mem_flatMap.mp member
    cases List.mem_singleton.mp member
    exact ⟨.sort true, List.mem_singleton_self _, rfl⟩

/-- A sortable value uses a sort cover, possibly underneath padding. -/
theorem Profile.HasType.sortFlagCover
    {atom : Atom n} {support : Profile n}
    (sortable : (Profile.singleton atom).HasType (.sort relevant))
    (typed : (Profile.singleton atom).HasType support) :
    ∃ flag ∈ support.sortFlags, (Profile.singleton atom).HasType (.sort flag) := by
  induction n with
  | zero =>
    obtain ⟨flag, member, equal⟩ := typed atom (List.mem_singleton_self _)
    change flag = true at equal
    subst flag
    exact ⟨true, member, Profile.HasType.sort atom⟩
  | succ n ih =>
    cases atom with
    | pad lower =>
      change (Profile.singleton lower).pad.HasType _ at sortable typed
      have small : (Profile.singleton lower).HasType (.sort relevant) := by
        simpa only [Profile.down_sort] using sortable.pad_inv
      obtain ⟨flag, member, formed⟩ := ih small typed.pad_inv
      exact ⟨flag, member, formed.pad_sort⟩
    | fn | ctor | record =>
      obtain ⟨cover, member, impossible⟩ := sortable.2.2 _ (List.mem_singleton_self _)
      cases List.mem_singleton.mp member
      contradiction
    | sort | pi | family =>
      obtain ⟨cover, member, covered⟩ := typed.2.2 _ (List.mem_singleton_self _)
      cases cover with
      | sort flag =>
        refine ⟨flag, ?_, typed.wf_value, Profile.WF.sort (n := n + 1) flag, ?_⟩
        · apply Profile.sortFlags_mono (left := Profile.sort (n := n + 1) flag)
            (fun _ h => (List.mem_singleton.mp h) ▸ member)
          simp only [Profile.sortFlags_sort, List.mem_singleton]
        · intro actual h
          cases List.mem_singleton.mp h
          exact ⟨.sort flag, List.mem_singleton_self _, covered⟩
      | fn | pi | pad | family | ctor | record => contradiction

theorem Profile.HasType.flatSorts {value support : Profile n}
    (sortable : value.HasType (.sort relevant)) (typed : value.HasType support) :
    value.HasType support.flatSorts := by
  cases n with
  | zero => simpa [Profile.flatSorts, Profile.sortFlags, Profile.sort] using typed
  | succ n =>
    refine ⟨typed.wf_value, support.flatSorts_wf, ?_⟩
    intro atom member
    obtain ⟨flag, flagMember, cover⟩ :=
      (sortable.singleton_of_mem member).sortFlagCover (typed.singleton_of_mem member)
    obtain ⟨actual, actualMember, actualTyped⟩ := cover.2.2 atom (List.mem_singleton_self _)
    cases List.mem_singleton.mp actualMember
    exact ⟨.sort flag, List.mem_flatMap.mpr ⟨flag, flagMember, List.mem_singleton_self _⟩,
      actualTyped⟩

theorem Profile.HasType.sortFlag {profile : Profile n}
    (formed : profile.HasType (.sort relevant)) (member : flag ∈ profile.sortFlags) :
    (Profile.sort (n := n) flag).HasType (.sort relevant) := by
  induction n with
  | zero => exact formed.singleton_of_mem member
  | succ n ih =>
    have lower : profile.down.HasType (.sort relevant) := by
      simpa only [Profile.down_sort] using formed.down
    exact (ih lower member).sortPad

theorem Profile.HasType.flatSorts_sort {profile : Profile n}
    (formed : profile.HasType (.sort relevant)) :
    profile.flatSorts.HasType (.sort relevant) := by
  cases n with
  | zero => simpa [Profile.flatSorts, Profile.sortFlags, Profile.sort] using formed
  | succ n =>
    refine ⟨profile.flatSorts_wf, Profile.WF.sort (n := n + 1) relevant, ?_⟩
    intro atom member
    obtain ⟨flag, flagMember, atomMember⟩ := List.mem_flatMap.mp member
    exact (formed.sortFlag flagMember).2.2 atom atomMember

theorem Profile.WF.flatSorts {profile : Profile n} (_formed : profile.WF) :
    profile.flatSorts.WF := profile.flatSorts_wf

theorem Profile.HasType.flatSorts_sortable_type {value support : Profile n}
    (sortable : value.HasType (.sort relevant)) (typed : value.HasType support) :
    value.HasType support.flatSorts := sortable.flatSorts typed

end Lean4Lean.AnchoredProfiles

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles

theorem TypeRelated.sortFlag {profile : Profile n} (henv : env.Ordered)
    (code : TypeRelated env U registry Γ left right profile)
    (member : flag ∈ profile.sortFlags) :
    TypeRelated env U registry Γ left right (Profile.sort (n := n) flag) := by
  induction n with
  | zero => exact code.singleton member
  | succ n ih => exact (ih (code.down henv) member).sortPad

theorem TypeRelated.flatSorts {profile : Profile n} (henv : env.Ordered)
    (code : TypeRelated env U registry Γ left right profile) :
    TypeRelated env U registry Γ left right profile.flatSorts := by
  apply TypeRelated.of_singletons
  intro atom member
  obtain ⟨flag, member, atomMember⟩ := List.mem_flatMap.mp member
  exact (code.sortFlag henv member).singleton atomMember

end Lean4Lean.AnchoredSemantics

