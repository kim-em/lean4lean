import Lean4Lean.Theory.Typing.AnchoredFunctionShift

/-! Reverse the function/padding commute at one fixed key. Pi covers retain
only rows at that padded key; their actual displays and raw paths do not change.
The lower input is admitted by padding it before invoking the original row. -/

namespace Lean4Lean.AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

noncomputable def Rows.unshift (key : Key n)
    (rows : List (Key (n + 1) × Profile (n + 1))) : List (Key n × Profile n) := by
  classical
  exact rows.flatMap fun (other, output) =>
    if other = key.pad then [(key, output.down)] else []

theorem Rows.mem_unshift {key other : Key n} {output : Profile n}
    {rows : List (Key (n + 1) × Profile (n + 1))} :
    (other, output) ∈ Rows.unshift key rows ↔
      other = key ∧ ∃ oldOutput, (key.pad, oldOutput) ∈ rows ∧ output = oldOutput.down := by
  classical
  constructor
  · intro h
    obtain ⟨⟨oldKey, oldOutput⟩, hrow, hm⟩ := List.mem_flatMap.mp h
    change (other, output) ∈ (if oldKey = key.pad then [(key, oldOutput.down)] else []) at hm
    split at hm
    · rename_i he
      cases List.mem_singleton.mp hm
      exact ⟨rfl, oldOutput, he ▸ hrow, rfl⟩
    · cases hm
  · rintro ⟨heq, oldOutput, hrow, rfl⟩
    subst other
    exact List.mem_flatMap.mpr ⟨(key.pad, oldOutput), hrow, by simp⟩

theorem Rows.unshift_row {key : Key n} {output : Profile (n + 1)}
    (h : (key.pad, output) ∈ rows) : (key, output.down) ∈ Rows.unshift key rows :=
  Rows.mem_unshift.mpr ⟨rfl, output, h, rfl⟩

theorem Rows.unshift_rename (key : Key n)
    (rows : List (Key (n + 1) × Profile (n + 1))) (ρ : Lift) :
    Rows.unshift (key.rename ρ) (Rows.rename ρ rows) =
      Rows.rename ρ (Rows.unshift key rows) := by
  classical
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    obtain ⟨other, output⟩ := row
    by_cases he : other = key.pad
    · subst other
      simp only [Rows.rename, List.map_cons, Rows.unshift, List.flatMap_cons,
        Key.pad_rename, Profile.down_rename, List.map_append] at ih ⊢
      exact congrArg (List.cons _) ih
    · have he' : other.rename ρ ≠ (key.rename ρ).pad := by
        intro h
        apply he
        apply Key.rename_inj.mp
        simpa only [Key.pad_rename] using h
      simp only [Rows.rename, List.map_cons, Rows.unshift, List.flatMap_cons,
        if_neg he, if_neg he', List.nil_append] at ih ⊢
      exact ih

noncomputable def Atom.unshift (key : Key n) : Atom (n + 2) → Profile (n + 1)
  | .pi A B domain rows => .pi A B (Profile.down domain) (Rows.unshift key rows)
  | atom => atom.down

noncomputable def Profile.unshift (key : Key n) (profile : Profile (n + 2)) : Profile (n + 1) :=
  profile.flatMap (Atom.unshift key)

theorem Atom.unshift_rename (key : Key n) (atom : Atom (n + 2)) (ρ : Lift) :
    Atom.unshift (key.rename ρ) (atom.rename ρ) = (Atom.unshift key atom).rename ρ := by
  cases atom with
  | pi => simp only [Atom.rename_pi, Atom.unshift, Profile.pi, Profile.rename_singleton,
      Atom.rename_pi, Profile.down_rename, Rows.unshift_rename]
  | sort | fn | pad | family | ctor | record => rfl

theorem Profile.unshift_rename (key : Key n) (profile : Profile (n + 2)) (ρ : Lift) :
    (profile.rename ρ).unshift (key.rename ρ) = (profile.unshift key).rename ρ := by
  simp only [Profile.unshift, Profile.rename, List.flatMap_map, List.map_flatMap]
  congr 1
  funext atom
  exact Atom.unshift_rename key atom ρ

theorem Profile.WF.unshiftPi {domain : Profile (n + 1)}
    {rows : List (Key (n + 1) × Profile (n + 1))} (key : Key n)
    (H : (Profile.pi A B domain rows).WF) :
    (Profile.pi A B domain.down (Rows.unshift key rows)).WF := by
  obtain ⟨hd, hr⟩ := Profile.WF.pi_iff.mp H
  apply Profile.WF.pi_iff.mpr
  refine ⟨by simpa only [Profile.down_sort] using hd.down, ?_⟩
  intro other output hm
  obtain ⟨heq, oldOutput, hrow, rfl⟩ := Rows.mem_unshift.mp hm
  subst other
  exact ⟨(hr key.pad oldOutput hrow).1.pad_inv, (hr key.pad oldOutput hrow).2.down⟩

theorem Profile.WF.unshift {profile : Profile (n + 2)} (key : Key n) (H : profile.WF) :
    (profile.unshift key).WF := by
  intro atom hm
  obtain ⟨oldAtom, hsource, ha⟩ := List.mem_flatMap.mp hm
  have hs : (Profile.singleton oldAtom).WF := by
    intro a ha
    cases List.mem_singleton.mp ha
    exact H _ hsource
  have hw : (Atom.unshift key oldAtom).WF := by
    cases oldAtom with
    | pi => exact hs.unshiftPi key
    | sort | fn | pad | family | ctor | record => simpa only [Atom.unshift, Profile.down_singleton] using hs.down
  exact hw _ ha

theorem Profile.HasType.unshift_sort {profile : Profile (n + 2)} (key : Key n)
    (H : profile.HasType (.sort relevant)) :
    (profile.unshift key).HasType (.sort relevant) := by
  refine ⟨H.wf_value.unshift key, Profile.WF.sort (n := n + 1) relevant, ?_⟩
  intro atom hm
  obtain ⟨oldAtom, hsource, ha⟩ := List.mem_flatMap.mp hm
  have hs := H.singleton_of_mem hsource
  have ht : (Atom.unshift key oldAtom).HasType (.sort relevant) := by
    cases oldAtom with
    | pi A B domain rows =>
      obtain ⟨hw, hr⟩ := Profile.HasType.pi_iff.mp hs
      apply Profile.HasType.pi_iff.mpr
      refine ⟨hw.unshiftPi key, ?_⟩
      intro other output hrow
      obtain ⟨heq, oldOutput, hsource, rfl⟩ := Rows.mem_unshift.mp hrow
      subst other
      simpa only [Profile.down_sort] using (hr key.pad oldOutput hsource).down
    | sort | fn | pad | family | ctor | record => simpa only [Atom.unshift, Profile.down_singleton, Profile.down_sort] using hs.down
  exact ht.2.2 atom ha

theorem Profile.HasType.unshiftFn {key : Key n} {output : Atom n}
    {typeProfile : Profile (n + 2)}
    (H : (Profile.fn key.pad (.pad output)).HasType typeProfile) :
    (Profile.fn key output).HasType (typeProfile.unshift key) := by
  obtain ⟨A, B, domain, rows, result, hpi, hw, _, _, hrow, ht⟩ :=
    H.fn_inv (List.mem_singleton_self _)
  have hout : (Profile.singleton output).HasType (Profile.down result) := (show (Profile.singleton output).pad.HasType result from ht).pad_inv
  have hnew := Profile.HasType.fn (hw.unshiftPi key) (Rows.unshift_row hrow) hout
  apply hnew.enlarge ?_ (H.wf_type.unshift key)
  intro atom hm
  cases List.mem_singleton.mp hm
  exact Profile.le_refl (typeProfile.unshift key) _
    (List.mem_flatMap.mpr ⟨.pi A B domain rows, hpi, List.mem_singleton_self _⟩)

end Lean4Lean.AnchoredProfiles

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}

def PiWitness.unshift
    {Γ : List VExpr} {left right A B : VExpr} {domain : Profile (n + 1)}
    {rows : List (Key (n + 1) × Profile (n + 1))}
    (W : PiWitness env U registry (relations env U registry (n + 1))
      Γ left right A B domain rows) (henv : env.Ordered) (key : Key n) :
    PiWitness env U registry (relations env U registry n)
      Γ left right A B domain.down (Rows.unshift key rows) where
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
    simpa only [TypeRelated, Profile.down_rename] using TypeRelated.down henv W.domainRelated
  rowDomains := by
    intro other output hm
    obtain ⟨heq, oldOutput, hrow, rfl⟩ := Rows.mem_unshift.mp hm
    subst other
    obtain ⟨support, ht, hf, hle, hp, hc⟩ := W.rowDomains key.pad oldOutput hrow
    refine ⟨support.down, ?_, ?_, ?_, hp, TypeRelated.down henv hc⟩
    · have ht' : (key.rename W.map).input.pad.HasType support := by
        simpa only [Key.rename, Key.pad, Profile.rename_pad] using ht
      exact ht'.pad_inv
    · simpa only [Profile.down_sort] using hf.down
    · simpa only [Profile.down_rename] using hle.down
  rowBodies := by
    intro other output hm Δ ρ future x y admitted
    obtain ⟨heq, oldOutput, hrow, rfl⟩ := Rows.mem_unshift.mp hm
    subst other
    have ha : Admitted env U registry Δ (key.pad.rename (W.map.comp ρ)) x y := by
      simpa only [Key.pad_rename] using Admitted.pad henv admitted
    obtain ⟨hl, hr, hp⟩ := W.rowBodies key.pad oldOutput hrow Δ ρ future x y ha
    exact ⟨by simpa only [TypeRelated, Profile.down_rename] using TypeRelated.down henv hl,
      by simpa only [TypeRelated, Profile.down_rename] using TypeRelated.down henv hr,
      by simpa only [TypeRelated, Profile.down_rename] using TypeRelated.down henv hp⟩

theorem TypeRelated.unshiftPi
    {Γ : List VExpr} {left right A B : VExpr} {domain : Profile (n + 1)}
    {rows : List (Key (n + 1) × Profile (n + 1))}
    (henv : env.Ordered) (key : Key n)
    (H : TypeRelated env U registry Γ left right (.pi A B domain rows)) :
    TypeRelated env U registry Γ left right (.pi A B domain.down (Rows.unshift key rows)) := by
  intro Δ ρ future atom hm
  cases List.mem_singleton.mp hm
  obtain ⟨W⟩ := H Δ ρ future _ (List.mem_singleton_self _)
  change PiWitness env U registry (relations env U registry (n + 1)) Δ
    (left.lift' ρ) (right.lift' ρ) (A.lift' ρ) (B.lift' ρ.cons)
    (domain.rename ρ) (Rows.rename ρ rows) at W
  have W' := W.unshift henv (key.rename ρ)
  simpa only [Atom.rename_pi, CodeAtom, Profile.down_rename, Rows.unshift_rename] using Nonempty.intro W'

theorem TypeRelated.unshift {Γ : List VExpr} {left right : VExpr}
    {profile : Profile (n + 2)} (henv : env.Ordered) (key : Key n)
    (H : TypeRelated env U registry Γ left right profile) :
    TypeRelated env U registry Γ left right (profile.unshift key) := by
  apply TypeRelated.of_singletons
  intro atom hm
  obtain ⟨oldAtom, hsource, ha⟩ := List.mem_flatMap.mp hm
  have hs := H.singleton hsource
  have hshift : TypeRelated env U registry Γ left right (Atom.unshift key oldAtom) := by
    cases oldAtom with
    | pi => exact hs.unshiftPi henv key
    | sort | fn | pad | family | ctor | record => simpa only [Atom.unshift, Profile.down_singleton] using hs.down henv
  exact hshift.singleton ha

theorem FunctionBehavior.unshift
    {Γ : List VExpr} {left right type : VExpr} {key : Key n} {output : Atom n}
    {typeProfile : Profile (n + 2)} (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U))
    (H : FunctionBehavior env U registry (relations env U registry (n + 1))
      Γ left right type key.pad (.pad output) typeProfile) :
    FunctionBehavior env U registry (relations env U registry n)
      Γ left right type key output (typeProfile.unshift key) := by
  obtain ⟨ha, A, B, domain, rows, result, hpi, hrow, ht, W, behavior⟩ := H
  refine ⟨Admitted.unpad henv hΓ ha, A, B, domain.down, Rows.unshift key rows, result.down,
    List.mem_flatMap.mpr ⟨.pi A B domain rows, hpi, List.mem_singleton_self _⟩,
    Rows.unshift_row hrow,
    (show (Profile.singleton output).pad.HasType result from ht).pad_inv, W.unshift henv key, ?_⟩
  intro Δ ρ future x y admitted
  simp only [PiWitness.unshift] at future admitted ⊢
  have ha : Admitted env U registry Δ (key.pad.rename (W.map.comp ρ)) x y := by
    simpa only [Key.pad_rename] using Admitted.pad henv admitted
  obtain ⟨hl, hr, hp⟩ := behavior Δ ρ future x y ha
  have hl' : Related env U registry Δ
      (.app (left.lift' (W.map.comp ρ)) x) (.app (left.lift' (W.map.comp ρ)) y)
      ((W.leftBody.lift' ρ.cons).inst x)
      (Profile.singleton (output.rename (W.map.comp ρ))).pad (result.rename (W.map.comp ρ)) := by
    simpa only [Related, Profile.pad_singleton, Atom.rename_pad] using hl
  have hr' : Related env U registry Δ
      (.app (right.lift' (W.map.comp ρ)) x) (.app (right.lift' (W.map.comp ρ)) y)
      ((W.leftBody.lift' ρ.cons).inst x)
      (Profile.singleton (output.rename (W.map.comp ρ))).pad (result.rename (W.map.comp ρ)) := by
    simpa only [Related, Profile.pad_singleton, Atom.rename_pad] using hr
  have hp' : Related env U registry Δ
      (.app (left.lift' (W.map.comp ρ)) x) (.app (right.lift' (W.map.comp ρ)) x)
      ((W.leftBody.lift' ρ.cons).inst x)
      (Profile.singleton (output.rename (W.map.comp ρ))).pad (result.rename (W.map.comp ρ)) := by
    simpa only [Related, Profile.pad_singleton, Atom.rename_pad] using hp
  exact ⟨by simpa only [Related, Profile.down_rename] using
      Related.unpad henv (future.targetWF henv) hl',
    by simpa only [Related, Profile.down_rename] using
      Related.unpad henv (future.targetWF henv) hr',
    by simpa only [Related, Profile.down_rename] using
      Related.unpad henv (future.targetWF henv) hp'⟩

theorem Related.unshift_fn
    {Γ : List VExpr} {left right type : VExpr} {key : Key n} {output : Atom n}
    {typeProfile : Profile (n + 2)} (henv : env.Ordered)
    (H : Related env U registry Γ left right type (.fn key.pad (.pad output)) typeProfile) :
    Related env U registry Γ left right type (.fn key output) (typeProfile.unshift key) := by
  intro atom ha Δ ρ future
  cases List.mem_singleton.mp ha
  have old := H _ (List.mem_singleton_self _) Δ ρ future
  rcases old with hempty | ⟨Ω, τ, insertion, ht, hc, hv⟩
  · cases hempty
  · have behavior := hv _ (List.mem_singleton_self _)
    change (Profile.fn ((key.pad.rename ρ).rename τ)
      (.pad ((output.rename ρ).rename τ))).HasType ((typeProfile.rename ρ).rename τ) at ht
    simp only [← Key.pad_rename] at ht
    simp only [Atom.rename_fn, Atom.rename_pad, ← Key.pad_rename] at behavior
    change FunctionBehavior env U registry (relations env U registry (n + 1)) Ω
      ((left.lift' ρ).lift' τ) ((right.lift' ρ).lift' τ) ((type.lift' ρ).lift' τ)
      ((key.rename ρ).rename τ).pad (.pad ((output.rename ρ).rename τ))
      ((typeProfile.rename ρ).rename τ) at behavior
    have newTyped := ht.unshiftFn
    have newCode := TypeRelated.unshift henv ((key.rename ρ).rename τ) hc
    have newBehavior := FunctionBehavior.unshift henv (insertion.targetWF henv) behavior
    right
    refine ⟨Ω, τ, insertion, ?_, ?_, ?_⟩
    · simpa only [Profile.fn, Profile.rename_singleton, Atom.rename_fn,
        Profile.unshift_rename] using newTyped
    · change TypeRelated env U registry Ω ((type.lift' ρ).lift' τ)
        ((type.lift' ρ).lift' τ) (((typeProfile.unshift key).rename ρ).rename τ)
      simpa only [Profile.unshift_rename] using newCode
    · intro requested hr
      cases List.mem_singleton.mp hr
      simpa only [Profile.unshift_rename, Atom.rename_fn, TermAtom] using newBehavior

theorem Related.uncommute_pad_fn
    {Γ : List VExpr} {left right type : VExpr} {key : Key n} {output : Atom n}
    {typeProfile : Profile (n + 2)} (henv : env.Ordered)
    (H : Related env U registry Γ left right type (.fn key.pad (.pad output)) typeProfile) :
    Related env U registry Γ left right type (Profile.fn key output).pad
      (typeProfile.unshift key).pad :=
  Related.pad henv (H.unshift_fn henv)

end Lean4Lean.AnchoredSemantics
