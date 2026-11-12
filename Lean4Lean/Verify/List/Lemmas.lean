import Lean4Lean.Verify.LocalContext

/-! # List lemmas

General lemmas about lists (`List.Forall₂`, `filterMap`, `flatMap`, `takeWhile`) used by the
verification of inductive declarations.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open scoped _root_.List
open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- `List.Forall₂` from equal lengths and the relation at every index. Recursor and rule
loops use it to turn indexed facts into a pointwise relation. -/
theorem List.forall₂_of_getElem
    {α β : Type} {R : α → β → Prop} {as : List α} {bs : List β}
    (hlen : as.length = bs.length)
    (H : ∀ i (ha : i < as.length) (hb : i < bs.length),
      R as[i] bs[i]) :
    List.Forall₂ R as bs := by
  induction as generalizing bs with
  | nil =>
    have : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
    subst bs
    exact .nil
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have htail : as.length = bs.length := by simpa using hlen
      apply List.Forall₂.cons (H 0 (by simp) (by simp))
      apply ih htail
      intro i ha hb
      have h := H (i + 1) (by simpa) (by simpa)
      change R as[i] bs[i] at h
      exact h

/-- Two pointwise translations of a source spine have the same target spine. -/
theorem List.Forall₂.targets_eq_of_unique
    (H₁ : List.Forall₂ (TrExprS env Us Δ) source target₁)
    (H₂ : List.Forall₂ (TrExprS env Us Δ) source target₂) : target₁ = target₂ := by
  induction H₁ generalizing target₂ with
  | nil => cases H₂; rfl
  | cons Hhead _ ih =>
    let .cons Hhead' Htail' := H₂
    rw [Hhead.unique_of_syn Hhead', ih Htail']

/-- The element of a flattening at offset (length of the first `owner` rows) `+ i` is element
`i` of row `owner`. This is the list arithmetic shared by the executable and abstract
owned-constructor enumerations. -/
theorem List.flatMap_getElem_prefix
    (rows : List α) (entries : α → List β)
    (owner i : Nat) (howner : owner < rows.length)
    (hi : i < (entries rows[owner]).length)
    (hindex : ((rows.take owner).flatMap entries).length + i <
      (rows.flatMap entries).length) :
    (rows.flatMap entries)[((rows.take owner).flatMap entries).length + i]'hindex =
      (entries rows[owner])[i]'hi := by
  have hsplit : rows = rows.take owner ++ rows[owner] ::
      rows.drop (owner + 1) := by
    calc
      rows = rows.take (owner + 1) ++ rows.drop (owner + 1) :=
        (List.take_append_drop (owner + 1) rows).symm
      _ = (rows.take owner ++ [rows[owner]]) ++
          rows.drop (owner + 1) := by
        rw [List.take_append_getElem howner]
      _ = rows.take owner ++ rows[owner] :: rows.drop (owner + 1) := by
        simp
  have hrow : entries rows[owner] =
      (entries rows[owner]).take i ++
        (entries rows[owner])[i] ::
          (entries rows[owner]).drop (i + 1) := by
    calc
      entries rows[owner] =
          (entries rows[owner]).take (i + 1) ++
            (entries rows[owner]).drop (i + 1) :=
        (List.take_append_drop (i + 1) (entries rows[owner])).symm
      _ = ((entries rows[owner]).take i ++
            [(entries rows[owner])[i]]) ++
          (entries rows[owner]).drop (i + 1) := by
        rw [List.take_append_getElem hi]
      _ = (entries rows[owner]).take i ++
          (entries rows[owner])[i] ::
            (entries rows[owner]).drop (i + 1) := by
        simp
  have houter : rows.flatMap entries =
      (rows.take owner).flatMap entries ++ entries rows[owner] ++
        (rows.drop (owner + 1)).flatMap entries := by
    simpa only [List.flatMap_append, List.flatMap_cons,
      List.append_assoc] using congrArg (List.flatMap entries) hsplit
  have hflat : rows.flatMap entries =
      ((rows.take owner).flatMap entries ++
        (entries rows[owner]).take i) ++
      (entries rows[owner])[i] ::
        ((entries rows[owner]).drop (i + 1) ++
          (rows.drop (owner + 1)).flatMap entries) := by
    calc
      rows.flatMap entries =
          (rows.take owner).flatMap entries ++ entries rows[owner] ++
            (rows.drop (owner + 1)).flatMap entries := houter
      _ = (rows.take owner).flatMap entries ++
          ((entries rows[owner]).take i ++
            (entries rows[owner])[i] ::
              (entries rows[owner]).drop (i + 1)) ++
          (rows.drop (owner + 1)).flatMap entries :=
        congrArg
          (fun xs => (rows.take owner).flatMap entries ++ xs ++
            (rows.drop (owner + 1)).flatMap entries) hrow
      _ = ((rows.take owner).flatMap entries ++
            (entries rows[owner]).take i) ++
          (entries rows[owner])[i] ::
            ((entries rows[owner]).drop (i + 1) ++
              (rows.drop (owner + 1)).flatMap entries) := by
        simp only [List.append_assoc, List.cons_append]
  exact List.getElem_of_append hflat (by
    simp [Nat.min_eq_left (Nat.le_of_lt hi)])

theorem List.takeWhile_fvarId_prefix (fv : FVarId) :
    ∀ (l : List Expr), (∃ x ∈ l, x.fvarId! = fv) →
      (l.takeWhile (·.fvarId! != fv)).map (·.fvarId!) =
        (l.map (·.fvarId!)).take (l.takeWhile (·.fvarId! != fv)).length ∧
      (l.map (·.fvarId!))[(l.takeWhile (·.fvarId! != fv)).length]? = some fv
  | [], ⟨_, h, _⟩ => by simp at h
  | x :: xs, hmem => by
    by_cases hx : x.fvarId! = fv
    · simp [hx]
    · obtain ⟨y, hy, hyfv⟩ := hmem
      have hy' : ∃ y ∈ xs, y.fvarId! = fv := by
        rcases List.mem_cons.mp hy with rfl | hy
        · exact absurd hyfv hx
        · exact ⟨y, hy, hyfv⟩
      obtain ⟨h1, h2⟩ := List.takeWhile_fvarId_prefix fv xs hy'
      have hp : (x.fvarId! != fv) = true := by simpa using hx
      simp only [List.takeWhile_cons, hp, ↓reduceIte, List.map_cons,
        List.length_cons, List.take_succ_cons, List.getElem?_cons_succ]
      exact ⟨congrArg _ h1, h2⟩

theorem _root_.List.Forall₂.drop_both {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ n : Nat,
      List.Forall₂ R (l.drop n) (l'.drop n)
  | _, _, .nil, _ => by simp
  | _, _, .cons h t, 0 => .cons h t
  | _, _, .cons _ t, n + 1 => t.drop_both n

theorem List.filterMap_congr_of_mem {α β : Type _} {f g : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.filterMap_cons, h a (by simp)]
    rw [List.filterMap_congr_of_mem (fun x hx => h x (by simp [hx]))]

theorem List.filterMap_find?_zipIdx {β γ : Type _} :
    ∀ (types : List β) (k : Nat) (shapes : List (Nat × γ)),
      (shapes.map Prod.fst).Pairwise (· < ·) →
      (∀ p ∈ shapes, k ≤ p.1 ∧ p.1 < k + types.length) →
      (types.zipIdx k).filterMap
          (fun x => (shapes.find? (fun p => p.1 == x.2)).map (fun p => (x.2, p.2))) = shapes
  | [], k, shapes, _, hbound => by
    cases shapes with
    | nil => rfl
    | cons p ps => have := hbound p (by simp); simp at this; omega
  | t :: ts, k, [], _, _ => by
    simp only [List.find?_nil, Option.map_none]
    simp
  | t :: ts, k, p :: ps, hsorted, hbound => by
    have hsorted' : (ps.map Prod.fst).Pairwise (· < ·) := (List.pairwise_cons.mp hsorted).2
    have hgt : ∀ q ∈ ps, p.1 < q.1 := by
      intro q hq
      exact (List.pairwise_cons.mp hsorted).1 q.1 (List.mem_map_of_mem hq)
    have hp := hbound p (by simp)
    rw [List.zipIdx_cons, List.filterMap_cons]
    by_cases hpk : p.1 = k
    · have hfind : (p :: ps).find? (fun q => q.1 == k) = some p := by
        simp [hpk]
      rw [hfind]
      simp only [Option.map_some]
      have hrest : (ts.zipIdx (k + 1)).filterMap
          (fun x => ((p :: ps).find? (fun q => q.1 == x.2)).map (fun q => (x.2, q.2))) =
          (ts.zipIdx (k + 1)).filterMap
          (fun x => (ps.find? (fun q => q.1 == x.2)).map (fun q => (x.2, q.2))) := by
        apply List.filterMap_congr_of_mem
        intro x hx
        have hx' := List.mem_zipIdx (x := x.1) (i := x.2) (by simpa using hx)
        have hne : (p.1 == x.2) = false := by simp; omega
        simp [hne]
      rw [hrest, List.filterMap_find?_zipIdx ts (k + 1) ps hsorted' (by
        intro q hq
        have := hgt q hq
        have := hbound q (by simp [hq])
        simp at this ⊢
        omega)]
      rw [← hpk]
    · have hfind : (p :: ps).find? (fun q => q.1 == k) = none := by
        rw [List.find?_eq_none]
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · simpa using hpk
        · have := hgt q hq
          simp
          omega
      rw [hfind, Option.map_none]
      exact List.filterMap_find?_zipIdx ts (k + 1) (p :: ps) hsorted (by
        intro q hq
        have hq' := hbound q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · simp at hq' ⊢; omega
        · have := hgt q hq
          simp at hq' ⊢
          omega)

theorem List.Forall₂.leftPair
    (H : List.Forall₂ R [a₁, a₂] bs) :
    ∃ b₁ b₂, bs = [b₁, b₂] ∧ R a₁ b₁ ∧ R a₂ b₂ := by
  cases H with
  | cons ha₁ Htail =>
    cases Htail with
    | cons ha₂ Hnil =>
      cases Hnil
      exact ⟨_, _, rfl, ha₁, ha₂⟩

end VerifyInductive

end Lean4Lean
