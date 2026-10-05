import Batteries.Tactic.OpenPrivate
import Lean4Lean.Theory.Typing.AnchoredProfiles

namespace Lean4Lean.AnchoredProfiles
set_option backward.isDefEq.respectTransparency false
open private AtomLE AtomTyped AtomWF FamilyWF checks from Lean4Lean.Theory.Typing.AnchoredProfiles

/-- Relevant data values select one exact family support. -/
theorem Profile.HasType.family_cover_formation {atom : Atom (n + 1)}
    {family : FamilyData (Profile n)}
    (typed : (Profile.singleton atom).HasType (.singleton (.family family))) :
    (Profile.singleton (.family family) : Profile (n + 1)).HasType (.sort true) := by
  obtain ⟨other, member, cover⟩ := typed.2.2 _ (List.mem_singleton_self _)
  cases List.mem_singleton.mp member
  have relevant : family.relevant = true := by
    cases atom <;> simp only [AtomTyped] at cover
    all_goals try contradiction
    all_goals rename_i data; cases cover; exact data.relevant
  refine ⟨typed.wf_type, Profile.WF.sort (n := n + 1) true, ?_⟩
  intro a member
  cases List.mem_singleton.mp member
  exact ⟨.sort true, List.mem_singleton_self _, relevant⟩

theorem Profile.HasType.family_cover_mem {atom : Atom (n + 1)}
    {family : FamilyData (Profile n)} {bound : Profile (n + 1)}
    (typed : (Profile.singleton atom).HasType (.singleton (.family family)))
    (otherTyped : (Profile.singleton atom).HasType bound) :
    (.family family : Atom (n + 1)) ∈ bound.atoms := by
  obtain ⟨other, member, cover⟩ := typed.2.2 _ (List.mem_singleton_self _)
  cases List.mem_singleton.mp member
  obtain ⟨other, member, next⟩ := otherTyped.2.2 _ (List.mem_singleton_self _)
  cases atom <;> cases other <;> simp only [AtomTyped] at cover next
  all_goals try contradiction
  all_goals cases cover; cases next; exact member

theorem Profile.family_le_mem {family : FamilyData (Profile n)} {bound : Profile (n + 1)}
    (dominated : Profile.singleton (n := n + 1) (.family family) ≤ bound) :
    (.family family : Atom (n + 1)) ∈ bound.atoms := by
  obtain ⟨other, member, same⟩ := dominated _ (List.mem_singleton_self _)
  cases other <;> simp only [AtomLE] at same
  all_goals try contradiction
  cases same; exact member


theorem Profile.HasType.ctor_family_mem {data : ConstructorData (Profile n)}
    {bound : Profile (n + 1)}
    (typed : (Profile.singleton (.ctor data) : Profile (n + 1)).HasType bound) :
    (.family data.family : Atom (n + 1)) ∈ bound.atoms := by
  obtain ⟨other, member, cover⟩ := typed.2.2 _ (List.mem_singleton_self _)
  cases other <;> simp only [AtomTyped] at cover
  all_goals try contradiction
  cases cover; exact member

theorem Profile.HasType.record_family_mem {data : RecordData (Profile n)}
    {bound : Profile (n + 1)}
    (typed : (Profile.singleton (.record data) : Profile (n + 1)).HasType bound) :
    (.family data.family : Atom (n + 1)) ∈ bound.atoms := by
  obtain ⟨other, member, cover⟩ := typed.2.2 _ (List.mem_singleton_self _)
  cases other <;> simp only [AtomTyped] at cover
  all_goals try contradiction
  cases cover; exact member

end Lean4Lean.AnchoredProfiles
