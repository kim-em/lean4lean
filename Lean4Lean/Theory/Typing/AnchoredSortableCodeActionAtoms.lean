import Lean4Lean.Theory.Typing.AnchoredSupportActionLists
import Lean4Lean.Theory.Typing.AnchoredCodeAction
import Lean4Lean.Theory.Typing.AnchoredSourcePruning

/-! Every selected result of a finite code action has one original outer
atom. This includes minimal focusing: a selected minimal cover retains a
single demanded atom and one actual covering atom of the original support. -/
namespace Lean4Lean.AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

theorem Minimal.length_eq {value support : Profile n} (minimal : Minimal value support) :
    support.length = value.length := by
  induction minimal using Minimal.rec
      (motive_2 := fun _ support _ => support.length = 1) with
  | nil => rfl
  | cons first tail ihfirst ihtail =>
    simp only [Profile.union, Profile.singleton, Profile.mk, Profile.atoms,
      List.length_append, List.length_cons, List.length_nil] at *
    omega
  | @sort n atom relevant typed => cases n <;> rfl
  | family => rfl
  | fn => rfl
  | pad lower ih => simpa only [Profile.pad, List.length_map, Profile.singleton, Profile.mk, List.length_cons, List.length_nil] using ih

theorem AtomMinimal.singleton_support {atom : Atom n} {support : Profile n}
    (minimal : AtomMinimal atom support) : ∃ selected, support = Profile.singleton selected := by
  have count := (Minimal.cons minimal Minimal.nil).length_eq
  simp only [Profile.union, Profile.empty, Profile.atoms, Profile.mk, List.append_nil,
    Profile.singleton, List.length_cons, List.length_nil] at count
  cases support with
  | nil => simp at count
  | cons head tail =>
    cases tail with
    | nil => exact ⟨head, rfl⟩
    | cons next rest => simp at count

theorem Profile.LE.singleton_cover {profile : Profile n} {atom : Atom n}
    (bound : Profile.singleton atom ≤ profile) :
    ∃ original ∈ profile.atoms, Profile.singleton atom ≤ Profile.singleton original := by
  cases n with
  | zero =>
    obtain ⟨original, member, related⟩ := bound atom (List.mem_singleton_self _)
    refine ⟨original, member, ?_⟩
    intro other h
    cases List.mem_singleton.mp h
    exact ⟨original, List.mem_singleton_self _, related⟩
  | succ n =>
    obtain ⟨original, member, related⟩ := bound atom (List.mem_singleton_self _)
    refine ⟨original, member, ?_⟩
    intro other h
    cases List.mem_singleton.mp h
    exact ⟨original, List.mem_singleton_self _, related⟩

theorem Minimal.selected_cover {value focused support : Profile n}
    {atom : Atom n}
    (minimal : Minimal value focused) (bound : focused ≤ support)
    (member : atom ∈ focused.atoms) :
    ∃ demand, ∃ original ∈ support.atoms,
      Minimal (Profile.singleton demand) (Profile.singleton atom) ∧
      Profile.singleton atom ≤ Profile.singleton original := by
  obtain ⟨demand, _, part, partMinimal, selected, included⟩ :=
    minimal.support_origin_subset member
  obtain ⟨selectedAtom, rfl⟩ := partMinimal.singleton_support
  have equal : atom = selectedAtom := List.mem_singleton.mp selected
  subst atom
  have partBound : Profile.singleton selectedAtom ≤ support := by
    cases n <;> intro other h <;> exact bound other (included other h)
  obtain ⟨original, originalMember, originalBound⟩ := partBound.singleton_cover
  refine ⟨demand, original, originalMember, ?_, originalBound⟩
  simpa only [Profile.union, Profile.empty, Profile.atoms, Profile.mk, List.append_nil] using
    Minimal.cons partMinimal Minimal.nil

end Lean4Lean.AnchoredProfiles

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- Atom selection after an action can be pushed to one exact source atom,
retaining a finite action rather than assuming a semantic restriction. -/
theorem SortableCodeAction.atom
    {n m : Nat} {profile : Profile n} {nextProfile : Profile m} {atom : Atom m}
    (action : SortableCodeAction env U registry target relevant profile next nextProfile)
    (member : atom ∈ nextProfile.atoms) :
    ∃ original ∈ profile.atoms,
      Nonempty (SortableCodeAction env U registry target relevant
        (Profile.singleton original) next (Profile.singleton atom)) := by
  induction action with
  | id => exact ⟨atom, member, ⟨.id⟩⟩
  | support action =>
    obtain ⟨original, originalMember, selected⟩ := action.apply_mem.mp member
    exact ⟨original, originalMember, ⟨.comp (.support action) (.select selected)⟩⟩
  | comp first second firstIH secondIH =>
    obtain ⟨middle, middleMember, ⟨right⟩⟩ := secondIH member
    obtain ⟨original, originalMember, ⟨left⟩⟩ := firstIH middleMember
    exact ⟨original, originalMember, ⟨.comp left right⟩⟩
  | union first second firstIH secondIH =>
    exact (List.mem_append.mp member).elim firstIH secondIH
  | retag formed => exact ⟨atom, member, ⟨.retag (formed.singleton_of_mem member)⟩⟩
  | pad =>
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact ⟨original, originalMember, ⟨.pad⟩⟩
  | down =>
    obtain ⟨original, originalMember, selected⟩ := Profile.mem_down_iff.mp member
    exact ⟨original, originalMember, ⟨.comp .down
      (.select (by simpa only [Profile.down_singleton] using selected))⟩⟩
  | unpad =>
    refine ⟨.pad atom, List.mem_map_of_mem member, ⟨?_⟩⟩
    simpa only [Profile.pad_singleton] using (SortableCodeAction.unpad (profile := Profile.singleton atom))
  | @sortPad relevant n flag =>
    cases n with
    | zero =>
      cases List.mem_singleton.mp member
      exact ⟨flag, List.mem_singleton_self _, ⟨.sortPad⟩⟩
    | succ n =>
      cases List.mem_singleton.mp member
      exact ⟨.sort flag, List.mem_singleton_self _, ⟨.sortPad⟩⟩
  | @familyPad n relevant family =>
    cases List.mem_singleton.mp member
    exact ⟨.family family, List.mem_singleton_self _, ⟨.familyPad⟩⟩
  | map view =>
    obtain ⟨original, originalMember, selected⟩ := view.mapType_mem.mp member
    exact ⟨original, originalMember, ⟨.comp (.map view) (.select selected)⟩⟩
  | select selected =>
    cases List.mem_singleton.mp member
    exact ⟨_, selected, ⟨.id⟩⟩
  | focusMinimal minimal bound =>
    obtain ⟨demand, original, originalMember, restricted, covered⟩ :=
      minimal.selected_cover bound member
    exact ⟨original, originalMember, ⟨.focusMinimal restricted covered⟩⟩

end Lean4Lean.AnchoredSource.Adapted
