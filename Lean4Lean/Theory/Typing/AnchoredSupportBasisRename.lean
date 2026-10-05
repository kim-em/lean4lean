import Lean4Lean.Theory.Typing.AnchoredSupportBasis

/-! Naturality of the actual finite support enumeration. -/

namespace Lean4Lean.AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

private theorem choices_succ_rename (ρ : Lift)
    (lower : ∀ (value bound : Profile n),
      (Basis value bound).map (Profile.rename ρ) = Basis (value.rename ρ) (bound.rename ρ))
    (atom type : Atom (n + 1)) :
    (Basis.choices (n + 1) atom type).map (Profile.rename ρ) =
      Basis.choices (n + 1) (atom.rename ρ) (type.rename ρ) := by
  classical
  cases type with
  | sort relevant =>
    have ht : (Profile.singleton (atom.rename ρ)).HasType (.sort relevant) ↔
        (Profile.singleton atom).HasType (.sort relevant) := by
      simpa only [Profile.rename_singleton, Profile.rename_sort] using
        (Profile.rename_hasType_iff (ρ := ρ) (value := Profile.singleton atom)
          (type := Profile.sort relevant))
    cases atom <;>
      simp only [Basis.choices_succ, Atom.rename_sort, Atom.rename_fn, Atom.rename_pi,
        Atom.rename_pad] at ht ⊢
    all_goals try rw [ht]
    all_goals split <;> simp only [List.map_cons, List.map_nil, Profile.rename_sort]
  | fn | ctor | record => cases atom <;> rfl
  | family data =>
    have ht : (Profile.singleton (atom.rename ρ)).HasType
        (.singleton (n := n + 1) (.family (data.map (·.lift' ρ) (Profile.rename ρ)))) ↔
        (Profile.singleton atom).HasType (.singleton (n := n + 1) (.family data)) := by
      simpa only [Profile.rename_singleton, Atom.rename_family] using
        (Profile.rename_hasType_iff (ρ := ρ) (value := Profile.singleton atom)
          (type := Profile.singleton (n := n + 1) (.family data)))
    cases atom <;>
      simp only [Basis.choices_succ, Atom.rename_family, Atom.rename_ctor,
        Atom.rename_record, Atom.rename_sort, Atom.rename_fn, Atom.rename_pi,
        Atom.rename_pad] at ht ⊢
    all_goals rw [ht]
    all_goals split <;> simp only [List.map_cons, List.map_nil,
      Profile.rename_singleton, Atom.rename_family]
  | pad other =>
    cases atom <;> try rfl
    rename_i atom
    simp only [Basis.choices_succ, Atom.rename_pad, List.map_map]
    rw [← Profile.rename_singleton, ← Profile.rename_singleton, ← lower]
    simp only [List.map_map, Function.comp_def, Profile.pad_rename]
  | pi A B domain rows =>
    cases atom <;> try rfl
    rename_i key output
    have hw : (Profile.pi (A.lift' ρ) (B.lift' ρ.cons) (Profile.rename ρ domain)
        (Rows.rename ρ rows)).WF ↔ (Profile.pi A B domain rows).WF :=
      Profile.rename_wf_iff (ρ := ρ) (profile := Profile.pi A B domain rows)
    simp only [Basis.choices_succ, Atom.rename_fn, Atom.rename_pi]
    rw [hw]
    split
    · simp only [List.map_flatMap, Rows.rename, List.flatMap_map]
      apply congrArg (fun f => rows.flatMap f)
      funext row
      rcases row with ⟨other, result⟩
      change Key n at other key
      change Profile n at domain result
      simp only [Key.rename_inj (n := n)]
      by_cases he : other = key
      · subst other
        simp only [ite_true, List.map_flatMap, Key.rename]
        rw [← lower key.input domain, ← Profile.rename_singleton, ← lower]
        simp only [List.flatMap_map, List.map_map, Function.comp_def]
        rfl
      · simp only [if_neg he, List.map_nil]
    · rfl

/-- The concrete finite list is unchanged by renaming apart from renaming
every selected support; order and duplicate choices are preserved. -/
theorem Basis.rename (value bound : Profile n) (ρ : Lift) :
    (Basis value bound).map (Profile.rename ρ) = Basis (value.rename ρ) (bound.rename ρ) := by
  induction n with
  | zero =>
    have h : Profile.rename (n := 0) ρ = id := by
      funext p
      simp [Profile.rename, Atom.rename]
    simp [h]
  | succ n lower =>
    induction value with
    | nil =>
      change (Basis Profile.empty bound).map _ = Basis Profile.empty (bound.rename ρ)
      rw [Basis.nil, Basis.nil]
      rfl
    | cons atom rest ih =>
      rw [Basis.cons]
      change _ = Basis (atom.rename ρ :: Profile.rename ρ rest) (bound.rename ρ)
      rw [Basis.cons]
      simp only [List.map_flatMap, Profile.rename, List.flatMap_map]
      apply congrArg (fun f => bound.flatMap f)
      funext type
      have hc := choices_succ_rename ρ lower atom type
      rw [← hc]
      simp only [List.flatMap_map]
      apply congrArg (fun f => (Basis.choices (n + 1) atom type).flatMap f)
      funext first
      change (List.map (first.union ·) (Basis rest bound)).map (Profile.rename ρ) =
        (Basis (Profile.rename ρ rest) (bound.rename ρ)).map ((first.rename ρ).union ·)
      rw [← ih]
      simp only [List.map_map, Function.comp_def, Profile.rename_union]

end Lean4Lean.AnchoredProfiles
