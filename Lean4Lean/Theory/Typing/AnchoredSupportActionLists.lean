import Lean4Lean.Theory.Typing.AnchoredSupportAction
import Lean4Lean.Theory.Typing.AnchoredSourcePruning

/-! Support actions preserve finite atom origins. Conjunction can reorder
lists, so distribution is stated as membership equivalence, not list equality. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

theorem SupportAction.apply_empty (action : SupportAction env U registry context n) :
    action.apply [] = [] := by
  induction action with
  | id | output => rfl
  | flatSorts =>
    change (Profile.empty (n := _)).sortFlags.flatMap _ = []
    rw [Profile.sortFlags_empty]; rfl
  | view view => exact view.mapType_lists.1
  | pad child ih => change (child.apply []).pad = []; rw [ih]; rfl
  | comp first second firstIH secondIH => change second.apply (first.apply []) = []; rw [firstIH, secondIH]
  | union first second firstIH secondIH => change (first.apply []).union (second.apply []) = []; rw [firstIH, secondIH]; rfl

private theorem sortFlags_origin {profile : Profile n}
    (member : flag ∈ profile.sortFlags) :
    ∃ atom ∈ profile.atoms, flag ∈ (Profile.singleton atom).sortFlags := by
  induction profile with
  | nil =>
    change flag ∈ (Profile.empty (n := n)).sortFlags at member
    rw [Profile.sortFlags_empty] at member
    cases member
  | cons head tail ih =>
    change flag ∈ ((Profile.singleton head).union tail).sortFlags at member
    rw [Profile.sortFlags_union] at member
    rcases List.mem_append.mp member with first | rest
    · exact ⟨head, List.mem_cons_self, first⟩
    · obtain ⟨atom, present, found⟩ := ih rest
      exact ⟨atom, List.mem_cons_of_mem _ present, found⟩

theorem SupportAction.apply_mem
    (action : SupportAction env U registry context n)
    {profile : Profile n} {output : Atom n} :
    output ∈ (action.apply profile).atoms ↔
      ∃ original ∈ profile.atoms, output ∈ (action.apply (.singleton original)).atoms := by
  induction action with
  | id => simp [SupportAction.apply, Profile.singleton, Profile.mk, Profile.atoms]
  | flatSorts =>
    change output ∈ profile.sortFlags.flatMap (fun flag => Profile.sort flag) ↔ _
    simp only [List.mem_flatMap]
    constructor
    · rintro ⟨flag, member, selected⟩
      obtain ⟨original, originalMember, flagMember⟩ := sortFlags_origin member
      exact ⟨original, originalMember, List.mem_flatMap.mpr ⟨flag, flagMember, selected⟩⟩
    · rintro ⟨original, originalMember, selected⟩
      obtain ⟨flag, flagMember, selected⟩ := List.mem_flatMap.mp selected
      exact ⟨flag, Profile.sortFlags_mono (fun _ h => (List.mem_singleton.mp h) ▸ originalMember) flagMember, selected⟩
  | view view => exact view.mapType_mem
  | output key child ih =>
    simp only [SupportAction.apply, outputTypes, Profile.atoms, List.mem_map,
      Profile.singleton, Profile.mk, List.mem_cons, List.not_mem_nil, or_false]
    simp
  | pad child ih =>
    change output ∈ ((child.apply profile.down).pad).atoms ↔ _
    constructor
    · intro selected
      obtain ⟨atom, member, rfl⟩ := List.mem_map.mp selected
      obtain ⟨lower, lowerMember, selected⟩ := ih.mp member
      obtain ⟨original, originalMember, lowered⟩ := Profile.mem_down_iff.mp lowerMember
      refine ⟨original, originalMember, List.mem_map.mpr ⟨atom, ?_, rfl⟩⟩
      apply ih.mpr
      exact ⟨lower, by simpa only [Profile.down_singleton] using lowered, selected⟩
    · rintro ⟨original, originalMember, selected⟩
      obtain ⟨atom, member, rfl⟩ := List.mem_map.mp selected
      obtain ⟨lower, lowerMember, selected⟩ := ih.mp member
      refine List.mem_map.mpr ⟨atom, ih.mpr ⟨lower, ?_, selected⟩, rfl⟩
      apply Profile.mem_down_iff.mpr
      exact ⟨original, originalMember, by simpa only [Profile.down_singleton] using lowerMember⟩
  | comp first second firstIH secondIH =>
    change output ∈ (second.apply (first.apply profile)).atoms ↔ _
    constructor
    · intro member
      obtain ⟨middle, middleMember, selected⟩ := secondIH.mp member
      obtain ⟨original, originalMember, selectedMiddle⟩ := firstIH.mp middleMember
      exact ⟨original, originalMember, secondIH.mpr ⟨middle, selectedMiddle, selected⟩⟩
    · rintro ⟨original, originalMember, selected⟩
      obtain ⟨middle, middleMember, selected⟩ := secondIH.mp selected
      exact secondIH.mpr ⟨middle, firstIH.mpr ⟨original, originalMember, middleMember⟩, selected⟩
  | union first second firstIH secondIH =>
    constructor
    · intro member
      rcases List.mem_append.mp member with firstMember | secondMember
      · obtain ⟨original, present, selected⟩ := firstIH.mp firstMember
        exact ⟨original, present, List.mem_append_left _ selected⟩
      · obtain ⟨original, present, selected⟩ := secondIH.mp secondMember
        exact ⟨original, present, List.mem_append_right _ selected⟩
    · rintro ⟨original, present, selected⟩
      rcases List.mem_append.mp selected with firstMember | secondMember
      · exact List.mem_append_left _ (firstIH.mpr ⟨original, present, firstMember⟩)
      · exact List.mem_append_right _ (secondIH.mpr ⟨original, present, secondMember⟩)

end Lean4Lean.AnchoredSemantics
