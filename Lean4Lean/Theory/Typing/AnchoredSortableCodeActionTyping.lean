import Lean4Lean.Theory.Typing.AnchoredSortableCodeActionAtoms
import Lean4Lean.Theory.Typing.AnchoredFlatSortsGrades

/-! Code actions preserve the actual finite universe covers at any rank.
The proof follows each output atom to one original source atom, so mixed
relevance flags never require a single common sort for the entire query. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem SortableCodeAction.typedAtSorts
    {n m : Nat} {profile : Profile n} {nextProfile : Profile m}
    (action : SortableCodeAction env U registry target relevant profile next nextProfile)
    (typed : profile.HasType (Profile.sortsAt n flags)) :
    nextProfile.HasType (Profile.sortsAt m flags) := by
  have covers := (Profile.HasType.sortsAt_iff.mp typed).2
  have nextCovers : ∀ atom ∈ nextProfile.atoms,
      ∃ flag ∈ flags, (Profile.singleton atom).HasType (.sort flag) := by
    intro atom member
    obtain ⟨original, originalMember, ⟨selected⟩⟩ := action.atom member
    obtain ⟨flag, flagMember, formation⟩ := covers original originalMember
    exact ⟨flag, flagMember, selected.preservesSort formation⟩
  apply Profile.HasType.sortsAt_iff.mpr
  refine ⟨?_, nextCovers⟩
  cases m with
  | zero => trivial
  | succ m =>
    intro atom member
    obtain ⟨_, _, formed⟩ := nextCovers atom member
    exact formed.wf_value atom (List.mem_singleton_self _)

end Lean4Lean.AnchoredSource.Adapted
