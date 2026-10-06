import Lean4Lean.Verify.Inductive.Recursor.TelescopeUniqueness
import Lean4Lean.Verify.Inductive.Recursor.SecondPass
import Lean4Lean.Verify.Inductive.Recursor.FieldTypeScope

namespace Lean4Lean
open Lean hiding Environment Exception
open TypeChecker
open scoped _root_.List

/-! Restriction of a generated recursive call's context to the shape row of
its recursive field: the call-local arguments, the fields before the
recursive field, and the parameters. -/

/-- A sublist of a duplicate-free list is the filter of that list by its
membership predicate. -/
theorem List.Sublist.eq_filter_of_nodup {α : Type} {p : α → Bool} :
    ∀ {l' l : List α}, l' <+ l → l.Nodup → (∀ x, x ∈ l' ↔ x ∈ l ∧ p x) → l' = l.filter p
  | _, _, .slnil, _, _ => rfl
  | l', a :: l, .cons _ h, hnd, hmem => by
    have hpa : ¬ p a := by
      intro hp
      have : a ∈ l' := (hmem a).2 ⟨List.mem_cons_self, hp⟩
      exact (List.nodup_cons.1 hnd).1 (h.subset this)
    rw [List.filter_cons_of_neg hpa]
    refine eq_filter_of_nodup h (List.nodup_cons.1 hnd).2 fun x => ?_
    constructor
    · intro hx
      have := (hmem x).1 hx
      rcases List.mem_cons.1 this.1 with rfl | hx'
      · exact absurd this.2 hpa
      · exact ⟨hx', this.2⟩
    · rintro ⟨hx, hp⟩
      exact (hmem x).2 ⟨List.mem_cons_of_mem _ hx, hp⟩
  | _, a :: l, .cons_cons _ h, hnd, hmem => by
    have hpa : p a := ((hmem a).1 List.mem_cons_self).2
    rw [List.filter_cons_of_pos hpa]
    congr 1
    refine eq_filter_of_nodup h (List.nodup_cons.1 hnd).2 fun x => ?_
    constructor
    · intro hx
      have hxa : x ≠ a := fun heq => (List.nodup_cons.1 hnd).1 (heq ▸ h.subset hx)
      have := (hmem x).1 (List.mem_cons_of_mem _ hx)
      rcases List.mem_cons.1 this.1 with rfl | hx'
      · exact absurd rfl hxa
      · exact ⟨hx', this.2⟩
    · rintro ⟨hx, hp⟩
      have hxa : x ≠ a := fun heq => (List.nodup_cons.1 hnd).1 (heq ▸ hx)
      rcases List.mem_cons.1 ((hmem x).2 ⟨List.mem_cons_of_mem _ hx, hp⟩) with heq | hx'
      · exact absurd heq hxa
      · exact hx'


/-- Two sublists of a duplicate-free list with the same members coincide. -/
theorem List.Sublist.eq_of_nodup_of_mem_iff {α : Type} {l₁ l₂ l : List α}
    (h₁ : l₁ <+ l) (h₂ : l₂ <+ l) (hnd : l.Nodup) (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂) :
    l₁ = l₂ := by
  classical
  have e₁ := List.Sublist.eq_filter_of_nodup h₁ (p := fun x => decide (x ∈ l₂)) hnd fun x => by
    rw [hmem x, decide_eq_true_iff]
    exact ⟨fun h => ⟨h₂.subset h, h⟩, fun h => h.2⟩
  have e₂ := List.Sublist.eq_filter_of_nodup h₂ (p := fun x => decide (x ∈ l₂)) hnd fun x => by
    rw [decide_eq_true_iff]
    exact ⟨fun h => ⟨h₂.subset h, h⟩, fun h => h.2⟩
  rw [e₁, ← e₂]

namespace VerifyInductive


end VerifyInductive

end Lean4Lean
