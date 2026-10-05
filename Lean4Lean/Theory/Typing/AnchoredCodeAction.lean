import Lean4Lean.Theory.Typing.AnchoredSupportActionInterpretation
import Lean4Lean.Theory.Typing.AnchoredSortCodeGrades
import Lean4Lean.Theory.Typing.AnchoredDataPadding
import Lean4Lean.Theory.Typing.AnchoredViewInterpretation
import Lean4Lean.Theory.Typing.AnchoredMinimalSupport

/-! Finite code actions for hereditary output queries. Each constructor is
an explicit finite operation, with no semantic transformer field. This low
module does not depend on the hereditary source certificate grammar. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

inductive SortableCodeAction (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) : Bool → {n : Nat} → Profile n → Bool → {m : Nat} → Profile m → Type where
  | id : SortableCodeAction env U registry target relevant profile relevant profile
  | comp (first : SortableCodeAction env U registry target a p b q)
      (second : SortableCodeAction env U registry target b q c r) :
      SortableCodeAction env U registry target a p c r
  | union (first : SortableCodeAction env U registry target a p b q)
      (second : SortableCodeAction env U registry target a p b r) :
      SortableCodeAction env U registry target a p b (q.union r)
  | support (action : SupportAction env U registry target n) :
      SortableCodeAction env U registry target relevant (profile : Profile n) relevant (action.apply profile)
  | retag (formed : profile.HasType (.sort next)) :
      SortableCodeAction env U registry target relevant profile next profile
  | pad : SortableCodeAction env U registry target relevant profile relevant profile.pad
  | down {profile : Profile (n + 1)} :
      SortableCodeAction env U registry target relevant profile relevant profile.down
  | unpad : SortableCodeAction env U registry target relevant profile.pad relevant profile
  | sortPad : SortableCodeAction env U registry target relevant
      (Profile.sort (n := n) flag) relevant (Profile.sort (n := n + 1) flag)
  | familyPad {family : FamilyData (Profile n)} :
      SortableCodeAction env U registry target relevant
        (.singleton (n := n + 1) (.family family)) relevant
        (.singleton (n := n + 2) (.family family.pad))
  | map {a b : Atom n} (view : AtomView env U registry target a b) :
      SortableCodeAction env U registry target relevant (profile : Profile n)
        relevant (view.mapType profile)
  | select {profile : Profile n} {atom : Atom n} (member : atom ∈ profile.atoms) :
      SortableCodeAction env U registry target relevant profile relevant (.singleton atom)
  | focusMinimal {value focused support : Profile n}
      (minimal : Minimal value focused) (bound : focused ≤ support) :
      SortableCodeAction env U registry target relevant support relevant focused

/-- A code action preserves every actual sort classification, independently
of the flag used to form its source certificate. -/
theorem SortableCodeAction.preservesSort
    (action : SortableCodeAction env U registry target relevant profile next nextProfile)
    (formed : profile.HasType (.sort flag)) : nextProfile.HasType (.sort flag) := by
  induction action with
  | id | retag => exact formed
  | support action => exact action.preservesSort formed
  | comp first second firstIH secondIH => exact secondIH (firstIH formed)
  | union first second firstIH secondIH => exact (firstIH formed).union (secondIH formed)
  | pad => exact formed.pad_sort
  | down => simpa only [Profile.down_sort] using formed.down
  | unpad => simpa only [Profile.down_sort] using formed.pad_inv
  | sortPad => exact formed.sortPad
  | familyPad => exact formed.familyPad
  | map view => exact view.mapType_sort formed
  | select member => exact formed.singleton_of_mem member
  | focusMinimal minimal bound => exact formed.restrict bound minimal.formation.wf_value

theorem SortableCodeAction.codeMap
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (action : SortableCodeAction env U registry target relevant profile next nextProfile)
    (code : TypeRelated env U registry target left right profile) :
    TypeRelated env U registry target left right nextProfile := by
  induction action with
  | id | retag => exact code
  | support action => exact action.codeMap henv hscoped code
  | comp first second firstIH secondIH => exact secondIH (firstIH code)
  | union first second firstIH secondIH =>
    apply TypeRelated.of_singletons
    intro atom member
    exact (List.mem_append.mp member).elim
      (fun h => (firstIH code).singleton h) (fun h => (secondIH code).singleton h)
  | pad => exact code.pad henv
  | down => exact code.down henv
  | unpad => exact (TypeRelated.pad_iff henv).mp code
  | sortPad => exact code.sortPad
  | familyPad => exact code.familyPad henv
  | map view => exact view.codeMap henv hscoped code
  | select member => exact code.singleton member
  | focusMinimal minimal bound => exact code.focusMinimal henv minimal bound

noncomputable def SortableCodeAction.mixed
    {target future : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (insertion : MixedInsertion env U target future ρ)
    (action : SortableCodeAction env U registry target relevant profile next nextProfile) :
    SortableCodeAction env U registry future relevant (profile.rename ρ) next (nextProfile.rename ρ) := by
  induction action with
  | id => exact .id
  | support action =>
    rw [action.apply_mixed henv insertion]
    exact .support (action.mixed henv insertion)
  | comp first second firstIH secondIH => exact .comp firstIH secondIH
  | union first second firstIH secondIH =>
    simpa only [Profile.rename_union] using SortableCodeAction.union firstIH secondIH
  | retag formed =>
    exact .retag (by simpa only [Profile.rename_sort] using Profile.rename_hasType_iff.mpr formed)
  | @pad relevant n profile => simpa only [Profile.rename_pad] using (SortableCodeAction.pad (profile := profile.rename ρ))
  | @down relevant n profile =>
    simpa only [Profile.down_rename] using (SortableCodeAction.down (profile := profile.rename ρ))
  | @unpad relevant n profile =>
    simpa only [Profile.rename_pad] using (SortableCodeAction.unpad (profile := profile.rename ρ))
  | sortPad => simpa only [Profile.rename_sort] using SortableCodeAction.sortPad
  | @familyPad n relevant family =>
    simpa only [Profile.rename_singleton, Atom.rename_family, FamilyData.pad,
      FamilyData.map_map, Profile.pad_rename, Function.comp_def, id_eq] using (SortableCodeAction.familyPad (family := family.map (·.lift' ρ) (Profile.rename ρ)))
  | map view =>
    rw [view.mapType_mixed henv insertion]
    exact .map (view.mixed henv insertion)
  | select member =>
    rw [Profile.rename_singleton]
    apply SortableCodeAction.select
    exact List.mem_map_of_mem (f := Atom.rename ρ) member
  | focusMinimal minimal bound => exact .focusMinimal (minimal.rename ρ) (Profile.rename_le_iff.mpr bound)

noncomputable def SortableCodeAction.future
    {target future : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (insertion : FutureInsertion env U target future ρ)
    (action : SortableCodeAction env U registry target relevant profile next nextProfile) :
    SortableCodeAction env U registry future relevant (profile.rename ρ) next (nextProfile.rename ρ) := by
  induction action with
  | id => exact .id
  | support action =>
    rw [action.apply_future henv insertion]
    exact .support (action.future henv insertion)
  | comp first second firstIH secondIH => exact .comp firstIH secondIH
  | union first second firstIH secondIH =>
    simpa only [Profile.rename_union] using SortableCodeAction.union firstIH secondIH
  | retag formed =>
    exact .retag (by simpa only [Profile.rename_sort] using Profile.rename_hasType_iff.mpr formed)
  | @pad relevant n profile => simpa only [Profile.rename_pad] using (SortableCodeAction.pad (profile := profile.rename ρ))
  | @down relevant n profile =>
    simpa only [Profile.down_rename] using (SortableCodeAction.down (profile := profile.rename ρ))
  | @unpad relevant n profile =>
    simpa only [Profile.rename_pad] using (SortableCodeAction.unpad (profile := profile.rename ρ))
  | sortPad => simpa only [Profile.rename_sort] using SortableCodeAction.sortPad
  | @familyPad n relevant family =>
    simpa only [Profile.rename_singleton, Atom.rename_family, FamilyData.pad,
      FamilyData.map_map, Profile.pad_rename, Function.comp_def, id_eq] using (SortableCodeAction.familyPad (family := family.map (·.lift' ρ) (Profile.rename ρ)))
  | map view =>
    rw [view.mapType_future henv insertion]
    exact .map (view.future henv insertion)
  | select member =>
    rw [Profile.rename_singleton]
    apply SortableCodeAction.select
    exact List.mem_map_of_mem (f := Atom.rename ρ) member
  | focusMinimal minimal bound => exact .focusMinimal (minimal.rename ρ) (Profile.rename_le_iff.mpr bound)

end Lean4Lean.AnchoredSource.Adapted
