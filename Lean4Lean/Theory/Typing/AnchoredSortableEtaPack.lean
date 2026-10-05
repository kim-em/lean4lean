import Lean4Lean.Theory.Typing.AnchoredSortableVariableTrace

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem BinderPack.local_member
    (pack : BinderPack n input required outside) (member : (0, need) ∈ required) :
    need.rank ≤ n ∧ List.Subset (need.atGrade n).atoms input.atoms := by
  induction pack with
  | nil => cases member
  | «local» head bound rest ih =>
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      exact ⟨bound, fun _ h => List.mem_append_left _ h⟩
    · obtain ⟨bound, included⟩ := ih member
      exact ⟨bound, fun _ h => List.mem_append_right _ (included h)⟩
  | external i head rest ih =>
    rcases List.mem_cons.mp member with equal | member
    · cases equal
    · exact ih member

theorem BinderPack.external_member
    (pack : BinderPack n input required outside) (member : (i + 1, need) ∈ required) :
    (i, need) ∈ outside := by
  induction pack with
  | nil => cases member
  | «local» head bound rest ih =>
    rcases List.mem_cons.mp member with equal | member
    · cases equal
    · exact ih member
  | external j head rest ih =>
    rcases List.mem_cons.mp member with equal | member
    · cases equal; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih member)

theorem BinderPack.variable_subset
    (pack : BinderPack n input required outside)
    (trace : SortableVariableTrace env U registry Γ 0 demand argument)
    (included : List.Subset argument required) :
    (∀ j need, (j, need) ∈ argument → need.rank ≤ n) ∧
      List.Subset (argument.atGrade n).atoms input.atoms := by
  constructor
  · intro j need member
    have eq := trace.indices member
    subst j
    exact (BinderPack.local_member pack (included member)).1
  · intro atom member
    obtain ⟨⟨j, need⟩, hm, ha⟩ := List.mem_flatMap.mp member
    have eq := trace.indices hm
    subst j
    exact (BinderPack.local_member pack (included hm)).2 ha

end Lean4Lean.AnchoredSource.Adapted
