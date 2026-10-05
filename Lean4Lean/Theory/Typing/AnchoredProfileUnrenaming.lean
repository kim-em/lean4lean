import Lean4Lean.Theory.Typing.AnchoredProfiles
import Batteries.Tactic.OpenPrivate

/-! A subprofile of a renamed demand uses only names from that demand's
source world. In particular, existential row supports bounded by a fixed
renamed domain cannot introduce a dependency on an inserted proof slot. -/
namespace Lean4Lean.AnchoredProfiles
open VExpr
open private checks AtomLE RowsLE Covers from Lean4Lean.Theory.Typing.AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

private theorem list_preimage {α β : Type} {f : α → β} (xs : List β)
    (images : ∀ x ∈ xs, ∃ y, f y = x) : ∃ ys : List α, ys.map f = xs := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    obtain ⟨y, hy⟩ := images x (List.mem_cons_self ..)
    obtain ⟨ys, hys⟩ := ih (fun z hz => images z (List.mem_cons_of_mem _ hz))
    exact ⟨y :: ys, by simp only [List.map_cons, hy, hys]⟩

private theorem atom_preimage_of_singleton {ρ : Lift} {atom : Atom n}
    (h : ∃ p : Profile n, p.rename ρ = .singleton atom) :
    ∃ a : Atom n, a.rename ρ = atom := by
  obtain ⟨p, hp⟩ := h
  cases p with
  | nil => cases hp
  | cons a p => exact ⟨a, (List.cons.inj hp).1⟩

/-- The conclusion is literal equality of the entire profile, including
its raw prototypes, keys and nested row outputs. -/
theorem Profile.exists_unrename_of_le {ρ : Lift} {left right : Profile n}
    (hle : left ≤ right.rename ρ) : ∃ source : Profile n, source.rename ρ = left := by
  induction n with
  | zero => exact ⟨left, by exact List.map_id left⟩
  | succ n ih =>
    have atomPreimage : ∀ {a : Atom (n + 1)} {b : Atom (n + 1)},
        AtomLE (checks n) a (b.rename ρ) → ∃ c : Atom (n + 1), c.rename ρ = a := by
      intro a b h
      cases b with
      | sort relevant =>
        cases a <;> simp only [Atom.rename_sort, AtomLE] at h
        exact ⟨.sort relevant, by cases h; rfl⟩
      | fn key output =>
        cases a <;> simp only [Atom.rename_fn, AtomLE] at h
        rename_i key' output'
        obtain ⟨a, ha⟩ := atom_preimage_of_singleton
          (ih (show Profile.singleton output' ≤ (Profile.singleton output).rename ρ from h.2))
        exact ⟨.fn key a, by simp only [Atom.rename_fn, ha, h.1]⟩
      | pad output =>
        cases a <;> simp only [Atom.rename_pad, AtomLE] at h
        rename_i output'
        obtain ⟨a, ha⟩ := atom_preimage_of_singleton
          (ih (show Profile.singleton output' ≤ (Profile.singleton output).rename ρ from h))
        exact ⟨.pad a, by simp only [Atom.rename_pad, ha]⟩
      | pi A B domain rows =>
        cases a <;> simp only [Atom.rename_pi, AtomLE] at h
        rename_i A' B' domain' rows'
        obtain ⟨d, hd⟩ := ih h.2.2.1
        have rowImages : ∀ row ∈ rows', ∃ original : Key n × Profile n,
            (original.1.rename ρ, original.2.rename ρ) = row := by
          intro ⟨key, output⟩ member
          obtain ⟨bound, hb, ho⟩ := h.2.2.2 key output member
          obtain ⟨⟨baseKey, baseOutput⟩, _, eq⟩ := List.mem_map.mp hb
          have hk := (Prod.mk.inj eq).1
          have hout := (Prod.mk.inj eq).2
          obtain ⟨p, hp⟩ := ih (show Profile.LE output (baseOutput.rename ρ) from hout ▸ ho)
          exact ⟨(baseKey, p), Prod.ext hk hp⟩
        obtain ⟨rs, hrs⟩ := list_preimage rows' rowImages
        exact ⟨.pi A B d rs, by
          simp only [Atom.rename_pi, hd, h.1, h.2.1]
          exact congrArg (AtomData.pi (A.lift' ρ) (B.lift' ρ.cons) domain') hrs⟩
      | family data =>
        cases a <;> simp only [Atom.rename_family, AtomLE] at h
        exact ⟨.family data, by rw [Atom.rename_family]; exact congrArg AtomData.family h.symm⟩
      | ctor data =>
        cases a <;> simp only [Atom.rename_ctor, AtomLE] at h
        exact ⟨.ctor data, by rw [Atom.rename_ctor]; exact congrArg AtomData.ctor h.symm⟩
      | record data =>
        cases a <;> simp only [Atom.rename_record, AtomLE] at h
        exact ⟨.record data, by rw [Atom.rename_record]; exact congrArg AtomData.record h.symm⟩
    apply list_preimage left
    intro atom member
    obtain ⟨other, ho, related⟩ := hle atom member
    obtain ⟨base, _, eq⟩ := List.mem_map.mp ho
    subst other
    exact atomPreimage related

/-- Retraction also preserves the bound, since literal renaming reflects
profile ordering. -/
theorem Profile.unrename_le {ρ : Lift} {left right : Profile n}
    (hle : left ≤ right.rename ρ) :
    ∃ source : Profile n, source.rename ρ = left ∧ source ≤ right := by
  obtain ⟨source, equal⟩ := Profile.exists_unrename_of_le hle
  exact ⟨source, equal, Profile.rename_le_iff.mp (equal ▸ hle)⟩

end Lean4Lean.AnchoredProfiles
