import Lean4Lean.Theory.Typing.AnchoredCodeAction

/-! Finite code actions preserve family provenance. Family-specific padding
can change the literal descriptor, so this invariant deliberately records
that operation instead of asserting adapter rigidity. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

def FamilyAtomProperty (property : {n : Nat} → FamilyData (Profile n) → Prop) :
    {n : Nat} → Atom n → Prop
  | _ + 1, .family family => property family
  | _ + 1, .pad atom => FamilyAtomProperty property atom
  | _, _ => True

def FamilyProfileProperty (property : {n : Nat} → FamilyData (Profile n) → Prop)
    (profile : Profile n) : Prop :=
  ∀ atom ∈ profile.atoms, FamilyAtomProperty property atom

theorem FamilyAtomProperty.mono
    {first second : {n : Nat} → FamilyData (Profile n) → Prop}
    (change : ∀ {n} {family : FamilyData (Profile n)}, first family → second family)
    {atom : Atom n} (origin : FamilyAtomProperty first atom) :
    FamilyAtomProperty second atom := by
  induction n with
  | zero => trivial
  | succ n ih =>
    cases atom with
    | family family => exact change origin
    | pad atom => exact ih origin
    | sort | fn | pi | ctor | record => trivial

namespace FamilyProfileProperty
variable {property : {n : Nat} → FamilyData (Profile n) → Prop}

theorem refine {focused profile : Profile n} (bound : focused ≤ profile)
    (origins : FamilyProfileProperty property profile) : FamilyProfileProperty property focused := by
  induction n with
  | zero => exact fun _ _ => trivial
  | succ n ih =>
    intro atom member
    obtain ⟨other, present, covered⟩ := bound atom member
    have origin := origins other present
    cases atom with
    | sort | fn | pi | ctor | record => trivial
    | family family =>
      cases other <;> try contradiction
      cases covered
      exact origin
    | pad atom =>
      cases other <;> try contradiction
      exact ih covered (fun other member => by
        cases List.mem_singleton.mp member
        exact origin) atom (List.mem_singleton_self _)

theorem pad (origins : FamilyProfileProperty property (profile : Profile n)) :
    FamilyProfileProperty property profile.pad := by
  intro atom member
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
  exact origins old ho

theorem sort (flag : Bool) : FamilyProfileProperty property (Profile.sort (n := n) flag) := by
  cases n with
  | zero => exact fun _ _ => trivial
  | succ n =>
    intro atom member
    cases List.mem_singleton.mp member
    trivial

theorem down (origins : FamilyProfileProperty property (profile : Profile (n + 1))) :
    FamilyProfileProperty property profile.down := by
  intro atom member
  obtain ⟨old, ho, member⟩ := List.mem_flatMap.mp member
  have origin := origins old ho
  cases old with
  | sort relevant => exact FamilyProfileProperty.sort relevant atom member
  | fn | pi | family | ctor | record => cases member
  | pad a => cases List.mem_singleton.mp member; exact origin

theorem rankShift (origins : FamilyProfileProperty property (profile : Profile (n + 1))) :
    FamilyProfileProperty property profile.rankShift := by
  intro atom member
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
  have origin := origins old ho
  cases old with
  | pi => trivial
  | sort | fn | pad | family | ctor | record => exact origin

theorem unshift (key : Key n)
    (origins : FamilyProfileProperty property (profile : Profile (n + 2))) :
    FamilyProfileProperty property (profile.unshift key) := by
  intro atom member
  obtain ⟨old, ho, member⟩ := List.mem_flatMap.mp member
  have origin := origins old ho
  cases old with
  | sort relevant => exact FamilyProfileProperty.sort relevant atom member
  | fn | family | ctor | record => cases member
  | pad a => cases List.mem_singleton.mp member; exact origin
  | pi => cases List.mem_singleton.mp member; trivial

theorem map {a b : Atom n} (change : AtomView env U registry target a b)
    (origins : FamilyProfileProperty property profile) :
    FamilyProfileProperty property (change.mapType profile) := by
  match n, a, b, change with
  | _, _, _, .refl _ => exact origins
  | _ + 1, _, _, .reanchor admitted =>
    intro atom member
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
    have origin := origins old ho
    cases old with
    | sort | fn | family | ctor | record | pad => exact origin
    | pi => trivial
  | _ + 1, _, _, .domainRekey path typed formed related =>
    intro atom member
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
    have origin := origins old ho
    cases old with
    | sort | fn | family | ctor | record | pad => exact origin
    | pi => simp only [domainRekeyAtom]; split <;> trivial
  | _ + 1, _, _, .input forward backward =>
    intro atom member
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
    have origin := origins old ho
    cases old with
    | sort | fn | family | ctor | record | pad => exact origin
    | pi => simp only [AtomView.mapType, inputTypes] at *; split <;> trivial
  | _ + 2, _, _, .commutePadFn _ _ => exact origins.down.rankShift
  | _ + 2, _, _, .uncommutePadFn key _ => exact (origins.unshift key).pad
  | _ + 1, _, _, .fn _ child =>
    intro atom member
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
    have origin := origins old ho
    cases old with
    | sort | fn | family | ctor | record | pad => exact origin
    | pi => trivial
  | _ + 1, _, _, .pad child => exact (FamilyProfileProperty.map child origins.down).pad
  | _, _, _, .trans first second => exact (origins.map first).map second
termination_by sizeOf change
decreasing_by all_goals simp_wf; omega

theorem support (action : SupportAction env U registry target n)
    (origins : FamilyProfileProperty property profile) :
    FamilyProfileProperty property (action.apply profile) := by
  induction action with
  | id => exact origins
  | flatSorts =>
    intro atom member
    obtain ⟨flag, _, member⟩ := List.mem_flatMap.mp member
    exact FamilyProfileProperty.sort flag atom member
  | view change => exact origins.map change
  | output key child ih =>
    intro atom member
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
    have origin := origins old ho
    cases old with
    | pi => trivial
    | sort | fn | pad | family | ctor | record => exact origin
  | pad child ih => exact (ih origins.down).pad
  | comp first second firstIH secondIH => exact secondIH (firstIH origins)
  | union first second firstIH secondIH =>
    intro atom member
    exact (List.mem_append.mp member).elim
      (fun h => firstIH origins atom h) (fun h => secondIH origins atom h)

end FamilyProfileProperty

theorem SortableCodeAction.familyProperty
    (action : SortableCodeAction env U registry target relevant profile next nextProfile)
    {property : {n : Nat} → FamilyData (Profile n) → Prop}
    (padFamily : ∀ {n} {family : FamilyData (Profile n)}, property family → property family.pad)
    (origins : FamilyProfileProperty property profile) : FamilyProfileProperty property nextProfile := by
  induction action with
  | id | retag => exact origins
  | support action => exact origins.support action
  | comp first second firstIH secondIH => exact secondIH (firstIH origins)
  | union first second firstIH secondIH =>
    intro atom member
    exact (List.mem_append.mp member).elim
      (fun h => firstIH origins atom h) (fun h => secondIH origins atom h)
  | pad => exact origins.pad
  | down => exact origins.down
  | unpad =>
    intro atom member
    exact origins (.pad atom) (List.mem_map_of_mem member)
  | sortPad => exact FamilyProfileProperty.sort _
  | familyPad =>
    intro atom member
    cases List.mem_singleton.mp member
    exact padFamily (origins _ (List.mem_singleton_self _))
  | map view => exact origins.map view
  | select member =>
    intro atom hm
    cases List.mem_singleton.mp hm
    exact origins _ member
  | focusMinimal minimal bound => exact origins.refine bound

/-- The only change to a family descriptor is a finite sequence of the
existing family padding operation. Outer profile padding is not a change
to the descriptor. -/
inductive FamilyPaddingPath : {n m : Nat} → FamilyData (Profile n) → FamilyData (Profile m) → Prop where
  | refl (family : FamilyData (Profile n)) : FamilyPaddingPath family family
  | pad (path : FamilyPaddingPath first last) : FamilyPaddingPath first last.pad

inductive FamilyOccurrence : {n m : Nat} → FamilyData (Profile n) → Atom m → Prop where
  | here (family : FamilyData (Profile n)) :
      FamilyOccurrence (m := n + 1) family (AtomData.family family)
  | pad {family : FamilyData (Profile n)} {atom : Atom m}
      (found : FamilyOccurrence family atom) :
      FamilyOccurrence (m := m + 1) family (AtomData.pad atom)

private theorem FamilyOccurrence.self (atom : Atom n) :
    FamilyAtomProperty (fun {_k} family => ∃ m, ∃ original : FamilyData (Profile m),
      FamilyOccurrence original atom ∧ FamilyPaddingPath original family) atom := by
  induction n with
  | zero => trivial
  | succ n ih =>
    cases atom with
    | family family => exact ⟨n, family, .here _, .refl _⟩
    | pad atom =>
      exact (ih atom).mono (by
        rintro k family ⟨m, original, found, path⟩
        exact ⟨m, original, .pad found, path⟩)
    | sort | fn | pi | ctor | record => trivial

def FamilyProfileOrigin (profile : Profile n) (family : FamilyData (Profile m)) : Prop :=
  ∃ k, ∃ original : FamilyData (Profile k), ∃ atom ∈ profile.atoms,
    FamilyOccurrence original atom ∧ FamilyPaddingPath original family

theorem SortableCodeAction.familyOrigins
    (action : SortableCodeAction env U registry target relevant profile next nextProfile) :
    FamilyProfileProperty (FamilyProfileOrigin profile) nextProfile := by
  apply action.familyProperty
  · rintro n family ⟨k, original, atom, member, found, path⟩
    exact ⟨k, original, atom, member, found, .pad path⟩
  · intro atom member
    exact (FamilyOccurrence.self atom).mono (by
      rintro k family ⟨m, original, found, path⟩
      exact ⟨m, original, atom, member, found, path⟩)

theorem SortableCodeAction.familyOrigin
    {profile : Profile n} {nextProfile : Profile (m + 1)} {family : FamilyData (Profile m)}
    (action : SortableCodeAction env U registry target relevant profile next nextProfile)
    (member : AtomData.family family ∈ nextProfile.atoms) : FamilyProfileOrigin profile family :=
  action.familyOrigins _ member

end Lean4Lean.AnchoredSource.Adapted
