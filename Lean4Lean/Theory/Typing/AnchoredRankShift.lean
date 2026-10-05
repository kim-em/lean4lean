import Lean4Lean.Theory.Typing.AnchoredPadding

/-! Expose one padded function demand at the next rank. Its key retains the
same raw domain and anchor. The expanded Pi cover uses the very same typed
display; only its finite domain and row demands are padded. Incoming arguments
are reflected through padding before applying the original behavior.
-/

namespace Lean4Lean.AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

def Rows.rankShift (rows : List (Key n × Profile n)) : List (Key (n + 1) × Profile (n + 1)) :=
  rows.map fun row => (row.1.pad, row.2.pad)

theorem Rows.rankShift_rename (rows : List (Key n × Profile n)) (ρ : Lift) :
    Rows.rankShift (Rows.rename ρ rows) = Rows.rename ρ (Rows.rankShift rows) := by
  simp only [Rows.rankShift, Rows.rename, List.map_map]
  apply List.map_congr_left
  intro row _
  exact Prod.ext (Key.pad_rename row.1 ρ) (Profile.pad_rename row.2 ρ)

/-- Expand every Pi cover at the next rank, retaining all other demands by
explicit padding. This fixed map is independent of future-world witnesses. -/
def Atom.rankShift : Atom (n + 1) → Atom (n + 2)
  | .pi A B domain rows => .pi A B (Profile.pad domain) (Rows.rankShift rows)
  | atom => .pad atom

def Profile.rankShift (profile : Profile (n + 1)) : Profile (n + 2) :=
  profile.map Atom.rankShift

theorem Atom.rankShift_rename (atom : Atom (n + 1)) (ρ : Lift) :
    Atom.rankShift (atom.rename ρ) = Atom.rename ρ (Atom.rankShift atom) := by
  cases atom with
  | sort | fn | pad | family | ctor | record => rfl
  | pi => simp only [Atom.rename_pi, Atom.rankShift, Profile.pad_rename, Rows.rankShift_rename]

theorem Profile.rankShift_rename (profile : Profile (n + 1)) (ρ : Lift) :
    (profile.rename ρ).rankShift = profile.rankShift.rename ρ := by
  simp only [Profile.rankShift, Profile.rename, List.map_map]
  apply List.map_congr_left
  intro atom _
  exact Atom.rankShift_rename atom ρ

theorem Profile.WF.rankShiftPi {domain : Profile n} {rows : List (Key n × Profile n)}
    (H : (Profile.pi A B domain rows).WF) :
    (Profile.pi A B (Profile.pad domain) (Rows.rankShift rows)).WF := by
  obtain ⟨hdomain, hrows⟩ := Profile.WF.pi_iff.mp H
  apply Profile.WF.pi_iff.mpr
  refine ⟨hdomain.pad_sort, ?_⟩
  intro key output hmem
  obtain ⟨⟨oldKey, oldOutput⟩, hsource, heq⟩ := List.mem_map.mp hmem
  cases heq
  exact ⟨(hrows oldKey oldOutput hsource).1.pad, (hrows oldKey oldOutput hsource).2.pad⟩

theorem Profile.WF.rankShift {profile : Profile (n + 1)} (H : profile.WF) :
    profile.rankShift.WF := by
  intro atom hmem
  obtain ⟨oldAtom, hsource, rfl⟩ := List.mem_map.mp hmem
  have hs : (Profile.singleton oldAtom).WF := by
    intro a ha
    cases List.mem_singleton.mp ha
    exact H _ hsource
  have hs' : (Profile.singleton (Atom.rankShift oldAtom)).WF := by
    cases oldAtom with
    | pi A B domain rows => exact hs.rankShiftPi
    | sort | fn | pad | family | ctor | record => exact hs.pad
  exact hs' _ (List.mem_singleton_self _)

theorem Profile.HasType.rankShift_sort {profile : Profile (n + 1)}
    (H : profile.HasType (.sort relevant)) :
    profile.rankShift.HasType (.sort relevant) := by
  refine ⟨H.wf_value.rankShift, Profile.WF.sort (n := n + 2) relevant, ?_⟩
  intro atom hmem
  obtain ⟨oldAtom, hsource, rfl⟩ := List.mem_map.mp hmem
  have hs := H.singleton_of_mem hsource
  have shifted : (Profile.singleton (Atom.rankShift oldAtom)).HasType (.sort relevant) := by
    cases oldAtom with
    | pi A B domain rows =>
      obtain ⟨hw, hr⟩ := Profile.HasType.pi_iff.mp hs
      apply Profile.HasType.pi_iff.mpr
      refine ⟨hw.rankShiftPi, ?_⟩
      intro key output hm
      obtain ⟨⟨oldKey, oldOutput⟩, hrow, heq⟩ := List.mem_map.mp hm
      cases heq
      exact (hr oldKey oldOutput hrow).pad_sort
    | sort | fn | pad | family | ctor | record => exact hs.pad_sort
  exact shifted.2.2 _ (List.mem_singleton_self _)

theorem Profile.HasType.rankShiftFn {key : Key n} {output : Atom n}
    {typeProfile : Profile (n + 1)} (H : (Profile.fn key output).HasType typeProfile) :
    (Profile.fn key.pad (AtomData.pad output)).HasType typeProfile.rankShift := by
  obtain ⟨A, B, domain, rows, result, hpi, hWF, _, _, hrow, htyped⟩ :=
    H.fn_inv (List.mem_singleton_self _)
  have hout : (Profile.singleton (n := n + 1) (AtomData.pad output)).HasType (Profile.pad result) := by
    simpa only [Profile.pad_singleton] using htyped.pad
  have ht := Profile.HasType.fn hWF.rankShiftPi
    (List.mem_map.mpr ⟨(key, result), hrow, rfl⟩) hout
  apply ht.enlarge ?_ H.wf_type.rankShift
  intro atom hmem
  cases List.mem_singleton.mp hmem
  exact Profile.le_refl typeProfile.rankShift _
    (List.mem_map.mpr ⟨.pi A B domain rows, hpi, rfl⟩)

end Lean4Lean.AnchoredProfiles

namespace Lean4Lean.AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
open VExpr VEnv AnchoredProfiles

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}

/-- The shifted Pi witness preserves all actual raw domains, bodies, paths,
and exposures. No new type conversion is inferred from a finite profile. -/
def PiWitness.rankShift
    {Γ : List VExpr} {left right A B : VExpr} {domain : Profile n}
    {rows : List (Key n × Profile n)}
    (W : PiWitness env U registry (relations env U registry n)
      Γ left right A B domain rows) (henv : env.Ordered) :
    PiWitness env U registry (relations env U registry (n + 1))
      Γ left right A B (Profile.pad domain) (Rows.rankShift rows) where
  context := W.context
  map := W.map
  leftDomain := W.leftDomain
  leftBody := W.leftBody
  rightDomain := W.rightDomain
  rightBody := W.rightBody
  leftExposure := W.leftExposure
  rightExposure := W.rightExposure
  leftDomainType := W.leftDomainType
  rightDomainType := W.rightDomainType
  leftBodyType := W.leftBodyType
  rightBodyType := W.rightBodyType
  domains := W.domains
  bodies := W.bodies
  prototypeDomainPath := W.prototypeDomainPath
  prototypeBodyPath := W.prototypeBodyPath
  domainRelated := by
    simpa only [TypeRelated, Profile.pad_rename] using TypeRelated.pad henv W.domainRelated
  rowDomains := by
    intro key output hmem
    obtain ⟨⟨oldKey, oldOutput⟩, hsource, heq⟩ := List.mem_map.mp hmem
    cases heq
    obtain ⟨support, hinput, hsort, hle, hpath, hcode⟩ :=
      W.rowDomains oldKey oldOutput hsource
    refine ⟨support.pad, ?_, hsort.pad_sort, ?_, hpath, TypeRelated.pad henv hcode⟩
    · simpa only [Key.rename, Key.pad, Profile.pad_rename] using hinput.pad
    · simpa only [Profile.pad_rename] using hle.pad
  rowBodies := by
    intro key output hmem Δ ρ future x y admitted
    obtain ⟨⟨oldKey, oldOutput⟩, hsource, heq⟩ := List.mem_map.mp hmem
    cases heq
    have ha : Admitted env U registry Δ
        (oldKey.rename (W.map.comp ρ)).pad x y := by
      simpa only [Admitted, Key.pad_rename] using admitted
    have oldAdmission := Admitted.unpad henv (future.targetWF henv) ha
    obtain ⟨hleft, hright, hpair⟩ := W.rowBodies oldKey oldOutput hsource Δ ρ future x y oldAdmission
    exact ⟨by simpa only [TypeRelated, Profile.pad_rename] using TypeRelated.pad henv hleft,
      by simpa only [TypeRelated, Profile.pad_rename] using TypeRelated.pad henv hright,
      by simpa only [TypeRelated, Profile.pad_rename] using TypeRelated.pad henv hpair⟩

/-- Closed type capability for the expanded Pi cover. Every future world
uses its original witness, so this does not transport an arbitrary private
display back to the base context. -/
theorem TypeRelated.rankShiftPi
    {Γ : List VExpr} {left right A B : VExpr} {domain : Profile n}
    {rows : List (Key n × Profile n)} (henv : env.Ordered)
    (H : TypeRelated env U registry Γ left right (.pi A B domain rows)) :
    TypeRelated env U registry Γ left right (.pi A B (Profile.pad domain) (Rows.rankShift rows)) := by
  intro Δ ρ future atom hmem
  have heq : atom = Atom.rename (n := n + 2) ρ (.pi A B (Profile.pad domain) (Rows.rankShift rows)) :=
    List.mem_singleton.mp hmem
  subst atom
  obtain ⟨W⟩ := H Δ ρ future _ (List.mem_singleton_self _)
  change PiWitness env U registry (relations env U registry n) Δ
    (left.lift' ρ) (right.lift' ρ) (A.lift' ρ) (B.lift' ρ.cons)
    (domain.rename ρ) (Rows.rename ρ rows) at W
  have W' := W.rankShift henv
  rw [Profile.pad_rename, Rows.rankShift_rename] at W'
  exact ⟨W'⟩

/-- Shift the entire fixed type cover before quantifying over future worlds.
Different future displays may select different original Pi atoms. -/
theorem TypeRelated.rankShift
    {Γ : List VExpr} {left right : VExpr} {profile : Profile (n + 1)}
    (henv : env.Ordered) (H : TypeRelated env U registry Γ left right profile) :
    TypeRelated env U registry Γ left right profile.rankShift := by
  apply TypeRelated.of_singletons
  intro atom hmem
  obtain ⟨oldAtom, hsource, rfl⟩ := List.mem_map.mp hmem
  have hs := H.singleton hsource
  cases oldAtom with
  | pi A B domain rows => exact hs.rankShiftPi henv
  | sort | fn | pad | family | ctor | record => exact TypeRelated.pad henv hs

/-- One concrete old function capability chooses one of its actual Pi covers.
Expanding that cover and padding the key/output produces function behavior at
the next rank. The theorem assumes no coverage or conversion callback. -/
theorem FunctionBehavior.rankShift
    {Γ : List VExpr} {left right type : VExpr} {key : Key n} {output : Atom n}
    {typeProfile : Profile (n + 1)} (henv : env.Ordered)
    (H : FunctionBehavior env U registry (relations env U registry n)
      Γ left right type key output typeProfile) :
    ∃ (A B : VExpr) (domain : Profile n) (rows : List (Key n × Profile n)),
      (.pi A B domain rows : Atom (n + 1)) ∈ typeProfile.atoms ∧
      FunctionBehavior env U registry (relations env U registry (n + 1))
        Γ left right type key.pad (AtomData.pad output) (.pi A B (Profile.pad domain) (Rows.rankShift rows)) := by
  obtain ⟨ha, A, B, domain, rows, result, hpi, hrow, htyped, W, behavior⟩ := H
  refine ⟨A, B, domain, rows, hpi, Admitted.pad henv ha,
    A, B, (Profile.pad domain), (Rows.rankShift rows), (Profile.pad result), List.mem_singleton_self _,
    List.mem_map.mpr ⟨(key, result), hrow, rfl⟩, ?_, W.rankShift henv, ?_⟩
  · simpa only [Profile.pad_singleton] using htyped.pad
  · intro Δ ρ future x y admitted
    have hadmitted : Admitted env U registry Δ
        (key.rename (W.map.comp ρ)).pad x y := by
      simpa only [Admitted, PiWitness.rankShift, Key.pad_rename] using admitted
    have oldAdmission := Admitted.unpad henv (future.targetWF henv) hadmitted
    obtain ⟨hleft, hright, hpair⟩ := behavior Δ ρ future x y oldAdmission
    refine ⟨?_, ?_, ?_⟩
    · simpa only [Related, PiWitness.rankShift, Profile.pad_singleton, Profile.pad_rename,
        Atom.rename_pad] using Related.pad (n := n) henv hleft
    · simpa only [Related, PiWitness.rankShift, Profile.pad_singleton, Profile.pad_rename,
        Atom.rename_pad] using Related.pad (n := n) henv hright
    · simpa only [Related, PiWitness.rankShift, Profile.pad_singleton, Profile.pad_rename,
        Atom.rename_pad] using Related.pad (n := n) henv hpair

end Lean4Lean.AnchoredSemantics
