import Lean4Lean.Theory.Typing.AnchoredProfiles

/-! Computed finite support maps and their literal renaming laws. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

def reanchorKey (key : Key n) (anchor : VExpr) : Key n := { key with anchor }

/-- Copy matching rows with a changed key. Existing rows remain available. -/
noncomputable def reanchorRows (oldKey newKey : Key n)
    (rows : List (Key n × Profile n)) : List (Key n × Profile n) := by
  classical
  exact rows ++ rows.flatMap fun (key, output) =>
    if key = oldKey then [(newKey, output)] else []

/-- Copy matching rows with a computed new output support. -/
noncomputable def outputRows (key : Key n) (map : Profile n → Profile n)
    (rows : List (Key n × Profile n)) : List (Key n × Profile n) := by
  classical
  exact rows ++ rows.flatMap fun (other, output) =>
    if other = key then [(key, map output)] else []

noncomputable def reanchorTypes (oldKey newKey : Key n) (profile : Profile (n + 1)) :
    Profile (n + 1) := profile.map fun
  | .pi A B domain rows => .pi A B domain (reanchorRows oldKey newKey rows)
  | atom => atom

noncomputable def outputTypes (key : Key n) (map : Profile n → Profile n)
    (profile : Profile (n + 1)) : Profile (n + 1) := profile.map fun
  | .pi A B domain rows => .pi A B domain (outputRows key map rows)
  | atom => atom

theorem mem_outputRows {key other : Key n} {map : Profile n → Profile n}
    {rows : List (Key n × Profile n)} {output : Profile n} :
    (other, output) ∈ outputRows key map rows ↔
      (other, output) ∈ rows ∨
        other = key ∧ ∃ oldOutput, (key, oldOutput) ∈ rows ∧ output = map oldOutput := by
  classical
  simp only [outputRows, List.mem_append, List.mem_flatMap]
  constructor
  · rintro (h | ⟨⟨k, b⟩, hm, h⟩)
    · exact .inl h
    · split at h
      next he =>
        change k = key at he
        subst k
        cases List.mem_singleton.mp h
        exact .inr ⟨rfl, b, hm, rfl⟩
      next => cases h
  · rintro (h | ⟨rfl, b, hm, rfl⟩)
    · exact .inl h
    · exact .inr ⟨(other, b), hm, by simp⟩

theorem outputRows.original {key : Key n} {map : Profile n → Profile n}
    {rows : List (Key n × Profile n)} (h : row ∈ rows) :
    row ∈ outputRows key map rows := List.mem_append.mpr (.inl h)

theorem outputRows.changed {key : Key n} {map : Profile n → Profile n}
    {rows : List (Key n × Profile n)} {output : Profile n} (h : (key, output) ∈ rows) :
    (key, map output) ∈ outputRows key map rows :=
  mem_outputRows.mpr (.inr ⟨rfl, output, h, rfl⟩)

theorem mem_reanchorRows {oldKey newKey other : Key n}
    {rows : List (Key n × Profile n)} {output : Profile n} :
    (other, output) ∈ reanchorRows oldKey newKey rows ↔
      (other, output) ∈ rows ∨ other = newKey ∧ (oldKey, output) ∈ rows := by
  classical
  simp only [reanchorRows, List.mem_append, List.mem_flatMap]
  constructor
  · rintro (h | ⟨⟨key, b⟩, hm, h⟩)
    · exact .inl h
    · split at h
      next he =>
        change key = oldKey at he
        subst key
        cases List.mem_singleton.mp h
        exact .inr ⟨rfl, hm⟩
      next => cases h
  · rintro (h | ⟨rfl, hm⟩)
    · exact .inl h
    · exact .inr ⟨(oldKey, output), hm, by simp⟩

theorem reanchorRows.original {oldKey newKey : Key n}
    {rows : List (Key n × Profile n)} (h : row ∈ rows) :
    row ∈ reanchorRows oldKey newKey rows := List.mem_append.mpr (.inl h)

theorem reanchorRows.changed {oldKey newKey : Key n}
    {rows : List (Key n × Profile n)} {output : Profile n} (h : (oldKey, output) ∈ rows) :
    (newKey, output) ∈ reanchorRows oldKey newKey rows :=
  mem_reanchorRows.mpr (.inr ⟨rfl, h⟩)

theorem reanchorRows_rename (oldKey newKey : Key n)
    (rows : List (Key n × Profile n)) (ρ : Lift) :
    Rows.rename ρ (reanchorRows oldKey newKey rows) =
      reanchorRows (oldKey.rename ρ) (newKey.rename ρ) (Rows.rename ρ rows) := by
  classical
  simp only [reanchorRows, Rows.rename, List.map_append, List.map_flatMap,
    List.flatMap_map]
  congr 1
  apply congrArg (fun f => rows.flatMap f)
  funext row
  rcases row with ⟨key, output⟩
  by_cases h : key = oldKey
  · simp [h]
  · simp [h]

theorem outputRows_rename (key : Key n) (map map' : Profile n → Profile n)
    (hmap : ∀ p, (map p).rename ρ = map' (p.rename ρ))
    (rows : List (Key n × Profile n)) :
    Rows.rename ρ (outputRows key map rows) =
      outputRows (key.rename ρ) map' (Rows.rename ρ rows) := by
  classical
  simp only [outputRows, Rows.rename, List.map_append, List.map_flatMap,
    List.flatMap_map]
  congr 1
  apply congrArg (fun f => rows.flatMap f)
  funext row
  rcases row with ⟨other, output⟩
  by_cases h : other = key
  · simp [h, hmap]
  · simp [h]

theorem reanchorTypes_rename (oldKey newKey : Key n)
    (profile : Profile (n + 1)) (ρ : Lift) :
    (reanchorTypes oldKey newKey profile).rename ρ =
      reanchorTypes (oldKey.rename ρ) (newKey.rename ρ) (profile.rename ρ) := by
  simp only [reanchorTypes, Profile.rename, List.map_map]
  apply List.map_congr_left
  intro atom _
  cases atom <;> simp only [Function.comp_apply, Atom.rename_pi, Atom.rename_sort,
    Atom.rename_fn, Atom.rename_pad, Atom.rename_family, Atom.rename_ctor, Atom.rename_record, reanchorRows_rename]

theorem outputTypes_rename (key : Key n) (map map' : Profile n → Profile n)
    (hmap : ∀ p, (map p).rename ρ = map' (p.rename ρ))
    (profile : Profile (n + 1)) :
    (outputTypes key map profile).rename ρ =
      outputTypes (key.rename ρ) map' (profile.rename ρ) := by
  simp only [outputTypes, Profile.rename, List.map_map]
  apply List.map_congr_left
  intro atom _
  cases atom <;> simp only [Function.comp_apply, Atom.rename_pi, Atom.rename_sort,
    Atom.rename_fn, Atom.rename_pad, Atom.rename_family, Atom.rename_ctor, Atom.rename_record, outputRows_rename _ _ _ hmap]

def domainKey (key : Key n) (domain : VExpr) : Key n := { key with domain }

noncomputable def domainRekeyAtom (key : Key n) (newDomain : VExpr) :
    Atom (n + 1) → Atom (n + 1) := by
  classical
  exact fun
    | .pi A B domain rows => .pi A B domain
        (if key.input.HasType domain then reanchorRows key (domainKey key newDomain) rows else rows)
    | atom => atom

noncomputable def domainRekeyTypes (key : Key n) (newDomain : VExpr)
    (profile : Profile (n + 1)) : Profile (n + 1) := profile.map (domainRekeyAtom key newDomain)

theorem domainRekeyTypes_rename (key : Key n) (newDomain : VExpr)
    (profile : Profile (n + 1)) (ρ : Lift) :
    (domainRekeyTypes key newDomain profile).rename ρ =
      domainRekeyTypes (key.rename ρ) (newDomain.lift' ρ) (profile.rename ρ) := by
  classical
  simp only [domainRekeyTypes, Profile.rename, List.map_map]
  apply List.map_congr_left
  intro atom _
  cases atom with
  | sort | fn | pad | family | ctor | record => rfl
  | pi A B domain rows =>
    change Profile n at domain
    by_cases ht : key.input.HasType domain
    · simp only [Function.comp_apply, domainRekeyAtom, ht, if_pos, Atom.rename_pi,
        Key.rename, Profile.rename_hasType_iff, reanchorRows_rename, domainKey]
    · simp only [Function.comp_apply, domainRekeyAtom, ht, ite_false, Atom.rename_pi,
        Key.rename, Profile.rename_hasType_iff, domainKey]

end Lean4Lean.AnchoredSemantics
