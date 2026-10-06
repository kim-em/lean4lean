import Lean4Lean.Theory.VLevel

/-!
# The shape domain of the shape model

This is a port of the shape domain of Mario Carneiro's prototype
(`Lean4Lean/Experimental/ShapeLogRel.lean`, everything before `Shape.hasType`), adapted to the
real calculus as described in `docs/inductives/PHASE1_NOTES.md`, section 2. Declaration names
and proof structure follow the prototype wherever possible. The changes are:

* Levels. `SLvl := List Nat → Nat` is the evaluation of a universe level, and sorts carry an
  `SLvl` (`Shape.sort l`). The order, compatibility and join compare sort levels by equality
  (classically decidable, so the order and join are noncomputable). Shape typing
  (`ShapeTyping.lean`) only looks at whether a level is identically zero (`SLvl.IsZero`).
  `Shape.type := .sort (fun _ => 1)`, `Shape.prop := .sort (fun _ => 0)`.
* `indTy` is replaced by `rigid c ls args cts`: a rigid type former with its evaluated levels,
  argument shapes, and constructor table `cts : List (Name × Shape)` (one telescope per
  constructor, over the constructor's fields). Order, compatibility and join are componentwise:
  same name, same levels, pointwise arguments, and constructor tables with the same names in
  the same order (`CtsRel`) and pointwise shapes. `lift`, `plift`, `olift`, `trim` and `WF`
  are componentwise. Constructor tables are handled by `ctsMap`, `ctsMapM`, `ctsZip`.
* `ctor c fields` stores the constructor's fields only; `ctor'` collapses a structure
  constructor (`IsStruct c`) with all-bottom fields to `bot`.
* The prototype's `[Params]` is replaced by `class ShapeParams` (`isStruct`, `famProp`).
* `TShape` separation lemmas for `indTy` are replaced by the `rigid` ones
  (`TShape.rigid_not_le_*`, `TShape.*_not_le_rigid`, `TShape.LE.rigid_inv`).

The commented-out `Shape.WF.plift` draft of the prototype is not ported.
-/

/-
`Shape.plift` and friends below are written in `Option`-monad `do`/`return` notation, and
the proofs about them `simp` through the exact term that notation elaborates to.
Pin the legacy elaborator here (digama0/lean4lean#31).
-/
set_option backward.do.legacy true

namespace Lean4Lean.ShapeModel
open Lean4Lean

noncomputable section

/-- The evaluation of a universe level, as a function of the values of the level parameters. -/
abbrev SLvl := List Nat → Nat

/-- A level is identically zero. Shape typing only looks at levels through this predicate. -/
def SLvl.IsZero (l : SLvl) : Prop := ∀ v, l v = 0

instance SLvl.decEq : DecidableEq SLvl := fun _ _ => Classical.propDecidable _
instance SLvl.decIsZero (l : SLvl) : Decidable l.IsZero := Classical.propDecidable _

theorem SLvl.not_isZero_one : ¬SLvl.IsZero (fun _ => 1) := fun h => nomatch h []
theorem SLvl.isZero_zero : SLvl.IsZero (fun _ => 0) := fun _ => rfl

/-- The parameters of the shape domain and of shape typing. -/
class ShapeParams where
  /-- `c` is the constructor of a structure with eta: a constructor shape with all fields
  bottom collapses to bottom. -/
  isStruct : Name → Bool
  /-- The rigid type former `c` is a proposition at these evaluated levels. -/
  famProp : Name → List SLvl → Bool

inductive Shape0 : Type where
  | bot : Shape0
  | sort (l : SLvl) : Shape0

inductive ShapeS (Shape : Type) : Type where
  | bot : ShapeS Shape
  | sort (l : SLvl) : ShapeS Shape
  | forallE : Shape → List (Shape × Shape) → ShapeS Shape
  | lam : List (Shape × Shape) → ShapeS Shape
  | ctor : Name → List Shape → ShapeS Shape
  | rigid : Name → List SLvl → List Shape → List (Name × Shape) → ShapeS Shape

@[implicit_reducible] def Shape : Nat → Type
  | 0 => Shape0
  | n + 1 => ShapeS (Shape n)

abbrev ShapeFun (n) := List (Shape n × Shape n)

@[match_pattern] def Shape.bot : ∀ {n}, Shape n
  | 0 => Shape0.bot
  | _+1 => ShapeS.bot

@[match_pattern] def Shape.sort (l : SLvl) : ∀ {n}, Shape n
  | 0 => Shape0.sort l
  | _+1 => ShapeS.sort l

abbrev Shape.prop : ∀ {n}, Shape n := .sort (fun _ => 0)
abbrev Shape.type : ∀ {n}, Shape n := .sort (fun _ => 1)

def ShapeFun.bot : ShapeFun n := [(.bot, .bot)]

/-- The pointwise lifting of a relation on shapes to constructor tables
(same names in the same order). -/
abbrev CtsRel (R : α → β → Prop) (t : List (Name × α)) (t' : List (Name × β)) : Prop :=
  List.Forall₂ (fun p q => p.1 = q.1 ∧ R p.2 q.2) t t'

theorem CtsRel.iff {R : α → β → Prop} {t : List (Name × α)} {t' : List (Name × β)} :
    CtsRel R t t' ↔ t.map (·.1) = t'.map (·.1) ∧ List.Forall₂ R (t.map (·.2)) (t'.map (·.2)) := by
  induction t generalizing t' with
  | nil => cases t' <;> simp
  | cons p t ih => cases t' <;> simp [ih, and_assoc, and_left_comm]

theorem CtsRel.imp {R S : α → β → Prop} (H : ∀ a b, R a b → S a b)
    {t : List (Name × α)} {t' : List (Name × β)} (h : CtsRel R t t') : CtsRel S t t' :=
  List.Forall₂.imp (fun _ _ h => ⟨h.1, H _ _ h.2⟩) h

theorem CtsRel.flip {R : α → β → Prop}
    {t : List (Name × α)} {t' : List (Name × β)} (h : CtsRel R t t') :
    CtsRel (fun b a => R a b) t' t :=
  List.Forall₂.flip (List.Forall₂.imp (fun _ _ h => ⟨h.1.symm, h.2⟩) h)

theorem CtsRel.rfl {R : α → α → Prop} {t : List (Name × α)}
    (H : ∀ a ∈ t, R a.2 a.2) : CtsRel R t t := List.Forall₂.rfl fun a h => ⟨_root_.rfl, H a h⟩

theorem CtsRel.trans {R : α → β → Prop} {S : β → γ → Prop} {T : α → γ → Prop}
    (H : ∀ a b c, R a b → S b c → T a c) {t₁ t₂ t₃}
    (h₁ : CtsRel R t₁ t₂) (h₂ : CtsRel S t₂ t₃) : CtsRel T t₁ t₃ :=
  List.Forall₂.trans (fun _ _ _ h1 h2 => ⟨h1.1.trans h2.1, H _ _ _ h1.2 h2.2⟩) h₁ h₂

theorem CtsRel.and_mem {R : α → β → Prop} {t t'} (h : CtsRel R t t') :
    CtsRel (fun a b => R a b ∧ (∃ c, (c, a) ∈ t) ∧ ∃ c, (c, b) ∈ t') t t' :=
  List.Forall₂.imp (fun _ _ ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨h1, h2, ⟨_, h3⟩, ⟨_, h4⟩⟩)
    (List.Forall₂.and_mem h)

theorem CtsRel.forall_exists_l {R : α → β → Prop} {t t'} (h : CtsRel R t t') :
    ∀ a ∈ t, ∃ b ∈ t', a.1 = b.1 ∧ R a.2 b.2 := List.Forall₂.forall_exists_l h

theorem CtsRel.forall_exists_r {R : α → β → Prop} {t t'} (h : CtsRel R t t') :
    ∀ b ∈ t', ∃ a ∈ t, a.1 = b.1 ∧ R a.2 b.2 := List.Forall₂.forall_exists_r h

def ShapeFun.Compat (R : α → β → Bool) (f : List (α × α)) (f' : List (β × β)) : Bool :=
  f.all fun (x, y) => f'.all fun (x', y') => R x x' → R y y'

theorem ShapeFun.Compat.def : Compat R f f' ↔ ∀ x ∈ f, ∀ y ∈ f', R x.1 y.1 → R x.2 y.2 := by
  simp [ShapeFun.Compat, -decide_implies]

def Shape.Compat : ∀ {n}, Shape n → Shape n → Bool
  | 0, .bot, _ | 0, _, .bot | _+1, .bot, _ | _+1, _, .bot => true
  | 0, .sort r, .sort r' | _+1, .sort r, .sort r' => r = r'
  | _+1, .forallE s f, .forallE s' f' => s.Compat s' && ShapeFun.Compat Compat f f'
  | _+1, .lam f, .lam f' => ShapeFun.Compat Compat f f'
  | _+1, .ctor c l, .ctor c' l' => c = c' && List.Forall₂ (Compat · ·) l l'
  | _+1, .rigid c ls l t, .rigid c' ls' l' t' =>
    c = c' && ls = ls' && List.Forall₂ (Compat · ·) l l' && CtsRel (Compat · ·) t t'
  | _, _, _ => false

theorem Shape.Compat.comm {n} {s t : Shape n} : s.Compat t = t.Compat s := by
  induction n with | zero => cases s <;> cases t <;> simp [Compat, eq_comm] | succ n ih
  let rec go {f f' : ShapeFun n} : ShapeFun.Compat Compat f f' = ShapeFun.Compat Compat f' f := by
    rw [Bool.eq_iff_iff]; simp [ShapeFun.Compat.def]
    constructor <;> intro H _ _ h1 _ _ h2 h3 <;> exact ih ▸ H _ _ h2 _ _ h1 (ih ▸ h3)
  have hl {l l' : List (Shape n)} :
      List.Forall₂ (Compat · ·) l l' ↔ List.Forall₂ (Compat · ·) l' l :=
    ⟨fun h => h.flip.imp fun _ _ h => ih ▸ h, fun h => h.flip.imp fun _ _ h => ih ▸ h⟩
  have ht {l l' : List (Name × Shape n)} :
      CtsRel (Compat · ·) l l' ↔ CtsRel (Compat · ·) l' l :=
    ⟨fun h => h.flip.imp fun _ _ h => ih ▸ h, fun h => h.flip.imp fun _ _ h => ih ▸ h⟩
  cases s <;> cases t <;> rw [Bool.eq_iff_iff] <;>
    simp only [Compat, Bool.and_eq_true, decide_eq_true_eq] <;>
    simp only [ih, go, @hl, @ht, @eq_comm Name, @eq_comm (List SLvl), @eq_comm SLvl]

theorem ShapeFun.Compat.comm {n} {f f' : ShapeFun n} :
    Compat Shape.Compat f f' = Compat Shape.Compat f' f := Shape.Compat.comm.go _ Shape.Compat.comm

theorem Shape.Compat.symm {n} {s t : Shape n} : s.Compat t → t.Compat s := (comm ▸ ·)

theorem ShapeFun.Compat.symm {n} {f f' : ShapeFun n} :
    Compat Shape.Compat f f' → Compat Shape.Compat f' f := (comm ▸ ·)

theorem Shape.Compat.bot_l {n} {s : Shape n} : bot.Compat s := by cases n <;> rfl
theorem Shape.Compat.bot_r {n} {s : Shape n} : s.Compat bot := symm bot_l

theorem Shape.Compat.sort_sort : Compat (sort r : Shape n) (sort r') ↔ r = r' := by
  cases n <;> simp [Compat]
theorem Shape.Compat.forallE_forallE {a a' : Shape n} {f f' : ShapeFun n} :
    Compat (n := n+1) (.forallE a f) (.forallE a' f') ↔
    a.Compat a' ∧ ShapeFun.Compat Compat f f' := by simp only [Compat, Bool.and_eq_true]
theorem Shape.Compat.lam_lam {f f' : ShapeFun n} :
    Compat (n := n+1) (.lam f) (.lam f') ↔ ShapeFun.Compat Compat f f' := by simp only [Compat]
theorem Shape.Compat.ctor_ctor {l l' : List (Shape n)} :
    Compat (n := n+1) (.ctor c l) (.ctor c' l') ↔ c = c' ∧ l.Forall₂ (Compat · ·) l' := by
  simp [Compat]
theorem Shape.Compat.rigid_rigid {l l' : List (Shape n)} {t t' : List (Name × Shape n)} :
    Compat (n := n+1) (.rigid c ls l t) (.rigid c' ls' l' t') ↔
    c = c' ∧ ls = ls' ∧ l.Forall₂ (Compat · ·) l' ∧ CtsRel (Compat · ·) t t' := by
  simp [Compat, and_assoc]

def ShapeFun.ble (R : α → α → Bool) (f f' : List (α × α)) : Bool :=
  f.all fun (x, y) => f'.any fun (x', y') => R x' x && R y y'

def Shape.ble : ∀ {n}, Shape n → Shape n → Bool
  | 0, .bot, _ | _+1, .bot, _ => true
  | 0, .sort r, .sort r' | _+1, .sort r, .sort r' => r = r'
  | _+1, .forallE s f, .forallE s' f' => s.ble s' && ShapeFun.ble ble f f'
  | _+1, .lam f, .lam f' => ShapeFun.ble ble f f'
  | _+1, .ctor c l, .ctor c' l' => c = c' && l.Forall₂ (Shape.ble · ·) l'
  | _+1, .rigid c ls l t, .rigid c' ls' l' t' =>
    c = c' && ls = ls' && l.Forall₂ (Shape.ble · ·) l' && CtsRel (Shape.ble · ·) t t'
  | _, _, _ => false

def ShapeFun.LE (s s' : ShapeFun n) : Prop := ShapeFun.ble Shape.ble s s'
def Shape.LE (s s' : Shape n) : Prop := s.ble s'
instance : LE (Shape n) := ⟨Shape.LE⟩
instance : DecidableRel (α := Shape n) (· ≤ ·) := fun x y => inferInstanceAs (Decidable (x.ble y))
instance : DecidableRel (ShapeFun.LE (n := n)) :=
  fun x y => inferInstanceAs (Decidable (ShapeFun.ble _ x y))

@[simp] theorem Shape.bot_le : Shape.bot ≤ (s : Shape n) := by cases n <;> rfl

theorem ShapeFun.LE.def' {f f' : ShapeFun n} : ShapeFun.LE f f' ↔
    ∀ x ∈ f, ∃ x' ∈ f', x'.1 ≤ x.1 ∧ x.2 ≤ x'.2 := by
  simp [LE, ble]; rfl

theorem ShapeFun.LE.def {f f' : ShapeFun n} : ShapeFun.LE f f' ↔
    ∀ x y : Shape n, (x, y) ∈ f → ∃ x' y' : Shape n, (x', y') ∈ f' ∧ x' ≤ x ∧ y ≤ y' := by
  simp [LE, ble]; rfl

theorem Shape.LE.def {s s' : Shape (n + 1)} : s ≤ s' ↔
    match s, s' with
    | .bot, _ => True
    | .sort r, .sort r' => r = r'
    | .forallE s f, .forallE s' f' => s ≤ s' ∧ ShapeFun.LE f f'
    | .lam f, .lam f' => ShapeFun.LE f f'
    | .ctor c f, .ctor c' f' => c = c' ∧ f.Forall₂ Shape.LE f'
    | .rigid c ls l t, .rigid c' ls' l' t' =>
      c = c' ∧ ls = ls' ∧ l.Forall₂ Shape.LE l' ∧ CtsRel Shape.LE t t'
    | _, _ => False := by
  dsimp only [(· ≤ ·), LE, ShapeFun.LE]
  rw [Shape.ble.eq_def]; cases s <;> cases s' <;> simp [and_assoc]
  all_goals intros; exact .rfl

theorem Shape.LE.rfl {s : Shape n} : s ≤ s := by
  dsimp [(· ≤ ·), Shape.LE]
  induction n with
  | zero => cases s <;> simp [ble]
  | succ n ih =>
    have ihf {s : List (Shape n × Shape n)} : ShapeFun.ble ble s s := by
      simp only [ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
      exact fun _ h => ⟨_, h, ih, ih⟩
    cases s <;> simp [ble, ih, ihf]
    · exact .rfl fun _ _ => ih
    · exact ⟨.rfl fun _ _ => ih, CtsRel.rfl fun _ _ => ih⟩

theorem Shape.LE.of_eq {s : Shape n} : s = t → s ≤ t := by rintro ⟨⟩; exact .rfl

theorem ShapeFun.LE.rfl {s : ShapeFun n} : s.LE s := by
  simp only [ShapeFun.LE, ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
  exact fun _ h => ⟨_, h, Shape.LE.rfl, Shape.LE.rfl⟩

theorem Shape.le_bot {s : Shape n} : s ≤ .bot ↔ s = .bot :=
  ⟨(by cases n <;> cases s <;> first | rfl | cases ·), (· ▸ LE.rfl)⟩

theorem Shape.le_sort {s : Shape n} : s ≤ .sort r ↔ s = .bot ∨ s = .sort r := by
  cases n <;> simp [sort, bot, (· ≤ ·), Shape.LE] <;> cases s <;>
    simp [ble] <;> exact ⟨fun h => h ▸ rfl, fun h => by injection h⟩

theorem Shape.sort_le {s : Shape n} : .sort r ≤ s ↔ .sort r = s := by
  cases n <;> simp [sort, (· ≤ ·), Shape.LE] <;> cases s <;> simp [ble, Shape]

theorem Shape.le_rigid {s : Shape (n+1)} :
    s ≤ .rigid c ls l t ↔ s = .bot ∨
      ∃ l' t', s = .rigid c ls l' t' ∧ l'.Forall₂ (· ≤ ·) l ∧ CtsRel (· ≤ ·) t' t := by
  rw [Shape.LE.def]; cases s with
  | bot => exact iff_of_true trivial (.inl rfl)
  | rigid c' ls' l' t' =>
    constructor
    · rintro ⟨rfl, rfl, h1, h2⟩; exact .inr ⟨_, _, rfl, h1, h2⟩
    · rintro (h | ⟨_, _, h, h1, h2⟩) <;> cases h; exact ⟨rfl, rfl, h1, h2⟩
  | _ => simp only [false_iff, not_or, not_exists, not_and]; exact ⟨nofun, fun _ _ h => nomatch h⟩

theorem Shape.rigid_le {s : Shape (n+1)} :
    .rigid c ls l t ≤ s ↔
      ∃ l' t', s = .rigid c ls l' t' ∧ l.Forall₂ (· ≤ ·) l' ∧ CtsRel (· ≤ ·) t t' := by
  rw [Shape.LE.def]; cases s with
  | rigid c' ls' l' t' =>
    constructor
    · rintro ⟨rfl, rfl, h1, h2⟩; exact ⟨_, _, rfl, h1, h2⟩
    · rintro ⟨_, _, h, h1, h2⟩; cases h; exact ⟨rfl, rfl, h1, h2⟩
  | _ => simp only [false_iff, not_exists, not_and]; exact fun _ _ h => nomatch h

@[simp] theorem Shape.rigid_le_rigid {l l' : List (Shape n)} :
    (by exact .rigid c ls l t : Shape (n+1)) ≤ .rigid c' ls' l' t' ↔
      c = c' ∧ ls = ls' ∧ l.Forall₂ (· ≤ ·) l' ∧ CtsRel (· ≤ ·) t t' := by
  rw [Shape.LE.def]; exact .rfl

theorem Shape.forallE_le {s : Shape (n+1)} :
    .forallE a b ≤ s ↔ ∃ a' b', a ≤ a' ∧ ShapeFun.LE b b' ∧ .forallE a' b' = s := by
  rw [Shape.LE.def]; cases s <;> simp [Shape]

@[simp] theorem Shape.forallE_le_forallE :
    (by exact .forallE a b : Shape (n+1)) ≤ .forallE a' b' ↔ a ≤ a' ∧ ShapeFun.LE b b' := by
  refine Shape.forallE_le.trans ⟨?_, fun ⟨h1, h2⟩ => ⟨_, _, h1, h2, rfl⟩⟩
  rintro ⟨_, _, h1, h2, ⟨⟩⟩; exact ⟨h1, h2⟩

theorem Shape.lam_le {s : Shape (n+1)} :
    .lam f ≤ s ↔ ∃ f', ShapeFun.LE f f' ∧ .lam f' = s := by
  rw [Shape.LE.def]; cases s <;> simp [Shape]

@[simp] theorem Shape.lam_le_lam :
    (by exact .lam f : Shape (n+1)) ≤ .lam f' ↔ ShapeFun.LE f f' :=
  Shape.lam_le.trans ⟨by rintro ⟨_, h, ⟨⟩⟩; exact h, fun h => ⟨_, h, rfl⟩⟩

theorem Shape.LE.trans {s t u : Shape n} : s ≤ t → t ≤ u → s ≤ u := by
  dsimp [(· ≤ ·), Shape.LE]
  induction n with
  | zero => cases s <;> cases t <;> simp [ble] <;> cases u <;> simp [ble, *] <;>
      (intro h1 h2; exact h1.trans h2)
  | succ n ih =>
    have ihf {s t u : List (Shape n × Shape n)} :
        ShapeFun.ble ble s t → ShapeFun.ble ble t u → ShapeFun.ble ble s u := by
      simp only [ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
      rintro h1 h2 x hx; let ⟨_, hy, x1, x2⟩ := h1 _ hx; let ⟨_, hz, y1, y2⟩ := h2 _ hy
      exact ⟨_, hz, ih y1 x1, ih x2 y2⟩
    cases s <;> cases t <;> simp [ble] <;> cases u <;> simp [ble, *] <;>
      first
      | grind [List.Forall₂.trans]
      | (rintro rfl rfl h1 h2 rfl rfl h3 h4
         exact ⟨rfl, rfl, h1.trans (fun _ _ _ => ih) h3, CtsRel.trans (fun _ _ _ => ih) h2 h4⟩)

theorem ShapeFun.LE.trans {s t u : ShapeFun n} : s.LE t → t.LE u → s.LE u := by
  simp only [ShapeFun.LE, ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
  rintro h1 h2 x hx; let ⟨_, hy, x1, x2⟩ := h1 _ hx; let ⟨_, hz, y1, y2⟩ := h2 _ hy
  exact ⟨_, hz, Shape.LE.trans y1 x1, Shape.LE.trans x2 y2⟩

theorem Shape.Compat.mono_r {n} {s t t' : Shape n}
    (le : t ≤ t') (H : s.Compat t') : s.Compat t := by
  induction n with
  | zero =>
    cases s <;> [simp [Compat]; skip]
    cases t <;> cases t' <;> simp [Compat, (·≤·), Shape.LE, Shape.ble] at H le ⊢
    exact H.trans le.symm
  | succ n ih
  let rec go {s t t' : ShapeFun n}
      (le : t.LE t') (H : ShapeFun.Compat Compat s t') : ShapeFun.Compat Compat s t := by
    simp [ShapeFun.Compat.def, ShapeFun.LE.def] at H le ⊢
    intro _ _ h1 _ _ h2 h3; have ⟨_, _, a1, a2, a3⟩ := le _ _ h2
    exact ih a3 <| H _ _ h1 _ _ a1 <| ih a2 h3
  (cases s with | bot => rfl | _) <;>
    (cases t' with | bot => cases le_bot.1 le; rfl | _) <;>
    simp [Compat] at H <;> (cases t with | bot => rfl | _) <;>
    simp [Shape.LE.def, Compat] at le ⊢
  · exact H.trans le.symm
  · exact ⟨ih le.1 H.1, go le.2 H.2⟩
  · exact go le H
  · exact ⟨H.1.trans le.1.symm, H.2.trans (fun _ _ _ h1 h2 => by exact ih h2 h1) le.2.flip⟩
  · obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := H; obtain ⟨l1, l2, l3, l4⟩ := le
    exact ⟨⟨⟨h1.trans l1.symm, h2.trans l2.symm⟩,
      h3.trans (fun _ _ _ h1 h2 => by exact ih h2 h1) l3.flip⟩,
      CtsRel.trans (fun _ _ _ h1 h2 => by exact ih h2 h1) h4 (CtsRel.flip l4)⟩

theorem ShapeFun.Compat.mono_r {n} {s t t' : ShapeFun n} :
    t.LE t' → Compat Shape.Compat s t' → Compat Shape.Compat s t :=
  Shape.Compat.mono_r.go _ Shape.Compat.mono_r

theorem Shape.Compat.mono {n} {s s' t t' : Shape n}
    (le₁ : s ≤ s') (le₂ : t ≤ t') (H : s'.Compat t') : s.Compat t :=
  mono_r le₂ <| symm <| mono_r le₁ <| symm H

/-! Operations on constructor tables. -/

def ctsMap (f : α → β) (t : List (Name × α)) : List (Name × β) := t.map fun p => (p.1, f p.2)

def ctsMapM (f : α → Option β) (t : List (Name × α)) : Option (List (Name × β)) :=
  t.mapM fun p => (f p.2).map (p.1, ·)

def ctsZip (f : α → β → γ) (t : List (Name × α)) (t' : List (Name × β)) : List (Name × γ) :=
  t.zipWith (fun p q => (p.1, f p.2 q.2)) t'

@[simp] theorem ctsMap_nil {f : α → β} : ctsMap f [] = [] := rfl
@[simp] theorem ctsMap_cons : ctsMap f (p :: t) = (p.1, f p.2) :: ctsMap f t := rfl

theorem mem_ctsMap {f : α → β} {t : List (Name × α)} :
    p ∈ ctsMap f t ↔ ∃ q ∈ t, p = (q.1, f q.2) := by
  simp [ctsMap, eq_comm]

theorem ctsMap_ctsMap {f : α → β} {g : β → γ} {t : List (Name × α)} :
    ctsMap g (ctsMap f t) = ctsMap (fun a => g (f a)) t := by
  simp [ctsMap]

theorem ctsMap_congr {f g : α → β} {t : List (Name × α)} (H : ∀ p ∈ t, f p.2 = g p.2) :
    ctsMap f t = ctsMap g t := by
  induction t with
  | nil => rfl
  | cons p t ih => rw [List.forall_mem_cons] at H; simp [H.1, ih H.2]

theorem ctsMap_id' {f : α → α} {t : List (Name × α)} (H : ∀ p ∈ t, f p.2 = p.2) :
    ctsMap f t = t := by
  induction t with
  | nil => rfl
  | cons p t ih => rw [List.forall_mem_cons] at H; simp [H.1, ih H.2]

theorem ctsRel_map_left {f : γ → α} {R : α → β → Prop} {t t'} :
    CtsRel R (ctsMap f t) t' ↔ CtsRel (fun a b => R (f a) b) t t' := by
  simp [ctsMap, CtsRel]

theorem ctsRel_map_right {f : γ → β} {R : α → β → Prop} {t t'} :
    CtsRel R t (ctsMap f t') ↔ CtsRel (fun a b => R a (f b)) t t' := by
  simp [ctsMap, CtsRel]

theorem ctsMapM_eq_some {f : α → Option β} {t : List (Name × α)} {t'} :
    ctsMapM f t = some t' ↔ CtsRel (f · = some ·) t t' := by
  simp only [ctsMapM, List.mapM_eq_some]
  apply iff_of_eq; congr; ext ⟨a, b⟩ ⟨c, d⟩
  simp [Option.map_eq_some_iff]; exact and_comm

theorem ctsMapM_some {f : α → β} {t : List (Name × α)} :
    ctsMapM (fun a => some (f a)) t = some (ctsMap f t) := by
  rw [ctsMapM_eq_some, ctsRel_map_right]; exact CtsRel.rfl fun _ _ => rfl

theorem ctsZip_ctsMap {f : α → β → γ} {g : α → α'} {g' : β → β'} {h : γ → γ'}
    {f' : α' → β' → γ'} (H : ∀ a b, h (f a b) = f' (g a) (g' b)) {t t'} :
    ctsMap h (ctsZip f t t') = ctsZip f' (ctsMap g t) (ctsMap g' t') := by
  induction t generalizing t' with
  | nil => rfl
  | cons p t ih =>
    cases t' with
    | nil => rfl
    | cons q t' => exact congr (congrArg List.cons (by simp [H])) ih

theorem CtsRel.zip_l {R : α → β → Prop} {S : α → γ → Prop} {f : α → β → γ}
    (H : ∀ a b, R a b → S a (f a b)) {t t'} (h : CtsRel R t t') :
    CtsRel S t (ctsZip f t t') := by
  induction h with
  | nil => exact .nil
  | cons hh _ ih => exact .cons ⟨_root_.rfl, H _ _ hh.2⟩ ih

theorem CtsRel.zip_r {R : α → β → Prop} {S : β → γ → Prop} {f : α → β → γ}
    (H : ∀ a b, R a b → S b (f a b)) {t t'} (h : CtsRel R t t') :
    CtsRel S t' (ctsZip f t t') := by
  induction h with
  | nil => exact .nil
  | cons hh _ ih => exact .cons ⟨hh.1.symm, H _ _ hh.2⟩ ih

def ShapeFun.lift (lift : α → β) (x : List (α × α)) : List (β × β) :=
  x.map fun (a, b) => (lift a, lift b)

def Shape.lift : ∀ {n} m, Shape n → Shape m
  | 0, _, .sort r | _+1, _, .sort r => .sort r
  | 0, _, .bot | _+1, _, .bot | _, 0, _ => .bot
  | _+1, _+1, .forallE s f => .forallE (lift _ s) <| ShapeFun.lift (lift _) f
  | _+1, _+1, .lam f => .lam <| ShapeFun.lift (lift _) f
  | _+1, _+1, .ctor c l => .ctor c <| l.map (lift _)
  | _+1, _+1, .rigid c ls l t => .rigid c ls (l.map (lift _)) (ctsMap (lift _) t)

@[simp] theorem Shape.lift_bot : (.bot : Shape n).lift m = .bot := by
  cases n <;> [rfl; cases m <;> rfl]

@[simp] theorem ShapeFun.lift_bot :
    ShapeFun.lift (Shape.lift m) (.bot : ShapeFun n) = ShapeFun.bot := by simp [ShapeFun.lift, bot]

@[simp] theorem Shape.lift_sort : (.sort r : Shape n).lift m = .sort r := by
  cases n <;> [rfl; cases m <;> rfl]

theorem Shape.lift_prop : (.prop : Shape n).lift m = .prop := lift_sort
theorem Shape.lift_type : (.type : Shape n).lift m = .type := lift_sort

theorem Shape.lift_self {s : Shape n} : s.lift n = s := by
  have {α} {lift : α → α} (IH : ∀ {s}, lift s = s) {s} : ShapeFun.lift lift s = s := by
    simp [ShapeFun.lift]; apply List.map_id''; simp [IH]
  unfold lift <;> split <;> (try rfl)
  · cases s <;> [rfl; grind]
  · rw [Shape.lift_self, this Shape.lift_self]
  · rw [this Shape.lift_self]
  · rw [List.map_id'' fun _ => Shape.lift_self]
  · rw [List.map_id'' fun _ => Shape.lift_self, ctsMap_id' fun _ _ => Shape.lift_self]

theorem ShapeFun.lift_self {s : ShapeFun n} : lift (Shape.lift n) s = s := by
  simp [ShapeFun.lift]; apply List.map_id''; simp [Shape.lift_self]

theorem Shape.lift_lift {s : Shape n₁} (le : n₁ ≤ n₂ ∨ n₃ ≤ n₂) :
    (s.lift n₂).lift n₃ = s.lift _ := by
  induction n₁ generalizing n₂ n₃ with
  | zero => cases s <;> simp [lift]
  | succ n₁ ih =>
    cases n₃ with
    | zero =>
      cases n₂ with | zero => rw [lift_self] | succ n₃
      cases s <;> simp [lift]
    | succ n₃ =>
      let n₂ + 1 := n₂; simp at le; replace ih {s} := ih (s := s) le
      have ihf {s : ShapeFun n₁} :
          ShapeFun.lift (lift n₃) (ShapeFun.lift (lift n₂) s) = ShapeFun.lift (lift _) s := by
        simp [ShapeFun.lift, ih]
      cases s <;> simp [lift, ih, ihf, ctsMap_ctsMap]
      · congr 2; ext; exact ih
      · congr 2; ext; exact ih

theorem ShapeFun.lift_lift {s : ShapeFun n₁} (le : n₁ ≤ n₂ ∨ n₃ ≤ n₂) :
    lift (Shape.lift n₃) (lift (Shape.lift n₂) s) = lift (Shape.lift _) s := by
  simp [ShapeFun.lift, Shape.lift_lift le]

theorem Shape.lift_le_lift {s t : Shape n} (le : n ≤ m) : s.lift m ≤ t.lift m ↔ s ≤ t := by
  dsimp [(· ≤ ·), Shape.LE]; rw [← Bool.eq_iff_iff]
  induction n generalizing m with
  | zero =>
    cases m with | zero => simp [lift_self] | succ m
    cases s <;> cases t <;> simp [lift, ble]
  | succ n ih =>
    let m + 1 := m; replace le := Nat.le_of_succ_le_succ le; replace ih {t' s} := @ih m t' s le
    let rec go {s t : ShapeFun n} :
        ShapeFun.ble ble (ShapeFun.lift (lift m) s) (ShapeFun.lift (lift m) t) =
        ShapeFun.ble ble s t := by
      simp only [ShapeFun.ble, ShapeFun.lift, List.all_map, List.any_map, Function.comp_def, ih]
    cases s <;> cases t <;> simp [ble, lift, go, ctsRel_map_left, ctsRel_map_right, *]

theorem ShapeFun.lift_le_lift {s t : ShapeFun n} (le : n ≤ m) :
    ShapeFun.LE (lift (Shape.lift m) s) (lift (Shape.lift m) t) ↔ ShapeFun.LE s t := by
  dsimp [ShapeFun.LE]; rw [← Bool.eq_iff_iff,
    Shape.lift_le_lift.go _ _ (Bool.eq_iff_iff.2 (Shape.lift_le_lift le))]

theorem Shape.lift_le_bot {s : Shape n} (h : n ≤ m) : s.lift m ≤ .bot ↔ s = .bot := by
  rw [← le_bot, ← lift_bot, Shape.lift_le_lift h]

theorem Shape.lift_eq_bot {s : Shape n} (h : n ≤ m) : s.lift m = .bot ↔ s = .bot := by
  rw [← le_bot, Shape.lift_le_bot h]

theorem Shape.lift_mono {s t : Shape n} : s ≤ t → s.lift m ≤ t.lift m := by
  dsimp [(· ≤ ·), Shape.LE]
  cases n with
  | zero =>
    cases s <;> cases t <;> simp [lift, ble] <;>
      first | exact Shape.bot_le | (intro h; subst h; exact Shape.LE.rfl)
  | succ n =>
    cases m with
    | zero => cases s <;> cases t <;> simp [lift, ble]
    | succ m =>
      let rec go {n m} (ih : ∀ {s t : Shape n}, s ≤ t → s.lift m ≤ t.lift m)
          {s t} : ShapeFun.ble ble s t → ShapeFun.ble ble
            (ShapeFun.lift (lift m) s) (ShapeFun.lift (lift m) t) := by
        simp only [ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true,
          ShapeFun.lift, List.any_map, List.all_map, Function.comp_apply]
        exact fun H _ h1 => let ⟨_, h2, h3, h4⟩ := H _ h1; ⟨_, h2, ih h3, ih h4⟩
      have := @Shape.lift_mono n m; dsimp [(· ≤ ·), Shape.LE] at this
      have := @go n m Shape.lift_mono
      cases s <;> cases t <;> simp [ble, lift, ctsRel_map_left, ctsRel_map_right, *] <;>
        first
        | grind [List.Forall₂.imp]
        | (rintro rfl rfl h1 h2
           exact ⟨h1.imp fun _ _ => Shape.lift_mono, h2.imp fun _ _ => Shape.lift_mono⟩)

theorem ShapeFun.lift_mono {s t : ShapeFun n} : s.LE t →
    LE (lift (Shape.lift m) s) (lift (Shape.lift _) t) := Shape.lift_mono.go Shape.lift_mono

protected theorem Shape.Compat.lift {x y : Shape n} (le : n ≤ m) :
    (x.lift m).Compat (y.lift m) = x.Compat y := by
  induction n generalizing m with
  | zero =>
    cases m with | zero => simp [lift_self] | succ m
    cases x <;> cases y <;> simp [lift, Compat]
  | succ n ih
  let m + 1 := m; replace le := Nat.le_of_succ_le_succ le; replace ih {x y} := @ih m x y le
  let rec go {x y : ShapeFun n} :
      ShapeFun.Compat Compat (ShapeFun.lift (lift m) x) (ShapeFun.lift (lift m) y) =
      ShapeFun.Compat Compat x y := by
    rw [Bool.eq_iff_iff]; simp only [ShapeFun.lift, ShapeFun.Compat.def, List.forall_mem_map, ih]
  cases x <;> cases y <;> simp [Compat, lift, go, ctsRel_map_left, ctsRel_map_right, *]

theorem ShapeFun.Compat.lift {x y : ShapeFun n} (le : n ≤ m) :
    Compat Shape.Compat (lift (Shape.lift m) x) (lift (Shape.lift m) y) =
    Compat Shape.Compat x y := Shape.Compat.lift.go _ _ (Shape.Compat.lift le)

def ShapeFun.plift (lift : α → β × Option β) (x : List (α × α)) :
    List (β × β) × Option (List (β × β)) :=
  (x.filterMap fun (a, b) => (lift a).2.map fun a => (a, (lift b).1),
   x.mapM fun (a, b) => (lift b).2.map fun b => ((lift a).1, b))

def Shape.plift : ∀ {n m}, Shape n → Shape m × Option (Shape m)
  | 0, _, .sort r | _+1, _, .sort r => (.sort r, some (.sort r))
  | 0, _, .bot | _+1, _, .bot => (.bot, some .bot)
  | _+1, 0, _ => (.bot, none)
  | _+1, _+1, .forallE s f =>
    let (s₀, s₁) := s.plift
    let (f₀, f₁) := ShapeFun.plift plift f
    (.forallE s₀ f₀, return .forallE (← s₁) (← f₁))
  | _+1, _+1, .lam f =>
    let (f₀, f₁) := ShapeFun.plift plift f
    (.lam f₀, return .lam (← f₁))
  | _+1, _+1, .ctor c l => (.ctor c (l.map (·.plift.1)), return .ctor c (← l.mapM (·.plift.2)))
  | _+1, _+1, .rigid c ls l t =>
    (.rigid c ls (l.map (·.plift.1)) (ctsMap (·.plift.1) t),
     return .rigid c ls (← l.mapM (·.plift.2)) (← ctsMapM (·.plift.2) t))

theorem Shape.plift_eq_lift (le : n ≤ m) {s : Shape n} :
    s.plift = (s.lift m, some (s.lift m)) := by
  let rec go {n m} (IH : n ≤ m → ∀ {s : Shape n}, s.plift = (s.lift m, some (s.lift m)))
      (le : n ≤ m) {s : ShapeFun n} :
      ShapeFun.plift plift s = (ShapeFun.lift (lift m) s, some (ShapeFun.lift (lift m) s)) := by
    simp only [ShapeFun.plift, ShapeFun.lift, IH le]; congr 1
    · rw [← List.filterMap_eq_map]; rfl
    · rw [List.mapM_eq_some, List.forall₂_map_right_iff]
      exact .rfl fun _ _ => rfl
  unfold plift; split <;> simp [lift] at le ⊢ <;> simp [plift_eq_lift le, go plift_eq_lift le]
  · exact ⟨_, List.mapM_pure, rfl⟩
  · exact ⟨_, List.mapM_pure, _, ctsMapM_some, rfl⟩

theorem ShapeFun.plift_eq_lift (le : n ≤ m) {s : ShapeFun n} :
    plift Shape.plift s = (lift (Shape.lift m) s, some (lift (Shape.lift m) s)) :=
  Shape.plift_eq_lift.go Shape.plift_eq_lift le

theorem Shape.plift_lift (le : n ≤ m) {s : Shape n} :
    (s.lift m).plift = (s, some s) := by
  let rec go {n m} (IH : n ≤ m → ∀ {s : Shape n}, (s.lift m).plift = (s, some s))
      (le : n ≤ m) {s : ShapeFun n} :
      ShapeFun.plift plift (ShapeFun.lift (lift m) s) = (s, some s) := by
    simp only [ShapeFun.plift, ShapeFun.lift, List.filterMap_map, List.mapM_map]; congr 1
    · refine .trans ?_ List.filterMap_some; congr 1; funext (a, b); simp [IH le]
    · rw [List.mapM_eq_some]; refine .rfl fun (a, b) _ => by simp [IH le]
  unfold lift; split <;> (try cases m) <;> try simp [plift, sort, bot] at le ⊢
  · cases le; cases s <;> grind
  · simp [plift_lift le, go plift_lift le]
  · simp [go plift_lift le]
  · simp [Function.comp_def, plift_lift le]
    exact ⟨_, List.mapM_pure, List.map_id _ ▸ rfl⟩
  · simp [Function.comp_def, plift_lift le, ctsMap_ctsMap]
    refine ⟨by rw [ctsMap_id' fun _ _ => rfl], _, ?_, _, ?_, rfl⟩
    · rw [List.mapM_eq_some]; exact .rfl fun _ _ => rfl
    · rw [ctsMapM_eq_some, ctsRel_map_left]; exact CtsRel.rfl fun _ _ => by simp [plift_lift le]

@[simp] theorem Shape.bot_plift : (bot (n := n)).plift (m := m) = (bot, some bot) := by
  cases n <;> simp [bot, plift]

theorem List.mapM_mapM_option (f : α → Option β) (g : β → Option γ) :
    (List.mapM f l).bind (List.mapM g) = List.mapM (f · |>.bind g) l := by
  induction l with simp [Option.bind_assoc] | cons a l ih
  congr 1; ext1; rw [Option.bind_comm]; congr 1; ext1; simp [← ih, Option.bind_assoc]

theorem ctsMapM_ctsMapM_option (f : α → Option β) (g : β → Option γ) {t : List (Name × α)} :
    (ctsMapM f t).bind (ctsMapM g) = ctsMapM (f · |>.bind g) t := by
  unfold ctsMapM; rw [List.mapM_mapM_option]; congr 1; ext1 ⟨a, b⟩
  cases h : f b <;> simp [h]

theorem Shape.plift_plift (le : n₁ ≤ n₂ ∨ n₃ ≤ n₂) {s : Shape n₁} :
    ((s.plift.1 : Shape n₂).plift.1 : Shape n₃) = s.plift.1 ∧
    (s.plift.2 : Option (Shape n₃)) = (s.plift.2 : Option (Shape n₂)).bind (·.plift.2) := by
  suffices ∀ {n₁ n₂ n₃}, n₂ ≤ n₁ → n₃ ≤ n₂ → ∀ {s : Shape n₁},
      ((s.plift.1 : Shape n₂).plift.1 : Shape n₃) = s.plift.1 ∧
      (s.plift.2 : Option (Shape n₃)) = (s.plift.2 : Option (Shape n₂)).bind (·.plift.2) by
    obtain le | le := le
    · simp [plift_eq_lift le]
      obtain h1 | h1 := Nat.le_total n₂ n₃
      · simp [plift_eq_lift h1, plift_eq_lift (Nat.le_trans le h1), lift_lift (.inl le)]
      obtain h2 | h2 := Nat.le_total n₁ n₃
      · rw [← lift_lift (.inl h2), plift_lift h1, plift_eq_lift h2]; exact ⟨rfl, rfl⟩
      · rw [← (this le h2).1, (this le h2).2, plift_lift le]; exact ⟨rfl, rfl⟩
    · obtain h1 | h1 := Nat.le_total n₂ n₁
      · rw [(this h1 le).1, (this h1 le).2]; exact ⟨rfl, rfl⟩
      simp [plift_eq_lift h1]
      obtain h2 | h2 := Nat.le_total n₁ n₃
      · rw [← lift_lift (.inl h2), plift_lift le, plift_eq_lift h2]; exact ⟨rfl, rfl⟩
      · rw [← (this h1 h2).1, (this h1 h2).2, plift_lift h1]; exact ⟨rfl, rfl⟩
  intro n₁ n₂ n₃ h1 h2 s
  induction n₁ generalizing n₂ n₃ with
  | zero => cases h1; simp [plift_eq_lift (Nat.le_refl _), lift_self] | succ n₁ ih
  cases n₂ with | zero => cases h2; simp [plift_eq_lift (Nat.le_refl _), lift_self] | succ n₂
  cases n₃ with
  | zero =>
    cases s with simp [plift]
    | forallE s f => cases s.plift.2 <;> simp; cases (ShapeFun.plift plift f).2 <;> simp [plift]
    | lam f => cases (ShapeFun.plift plift f).2 <;> simp [plift]
    | ctor _ l => cases eq: l.mapM (·.plift (m := n₂) |>.2) <;> simp [plift]
    | rigid _ _ l t =>
      cases eq: l.mapM (·.plift (m := n₂) |>.2) <;> simp
      cases eq: ctsMapM (·.plift (m := n₂) |>.2) t <;> simp [plift]
  | succ n₃
  simp at h1 h2; replace ih {s} := ih (s := s) h1 h2
  let rec go {s : ShapeFun n₁} :
      (ShapeFun.plift (plift (m := n₃)) (ShapeFun.plift (plift (m := n₂)) s).1).1 =
      (ShapeFun.plift plift s).1 ∧
      ((ShapeFun.plift plift s).2 : Option (ShapeFun n₃)) =
      ((ShapeFun.plift plift s).2 : Option (ShapeFun n₂)).bind (ShapeFun.plift plift · |>.2) := by
    simp [ShapeFun.plift]; constructor
    · rw [List.filterMap_filterMap]; congr 1; ext1 ⟨x, y⟩; dsimp
      simp [Option.bind_map, Function.comp_def]
      have := @ih x; revert this
      cases (x.plift.2 : Option (Shape n₂)) <;> simp +contextual [ih.1]
    · rw [List.mapM_mapM_option]; congr 1; ext1
      simp [Option.map_eq_bind, Option.bind_assoc, Function.comp_def, ih]
  cases s with simp [plift, ih, go, Function.comp_def, Option.bind_assoc]
  | forallE => congr 1; ext; rw [Option.bind_comm]
  | ctor _ l =>
    rw [← Option.bind_assoc]; congr 1
    induction l with simp | cons a l ihl
    simp [Option.bind_assoc, ihl]; congr 1; ext1; rw [Option.bind_comm]
  | rigid _ _ l t =>
    refine ⟨by congr 1; rw [ctsMap_ctsMap]; exact ctsMap_congr fun _ _ => ih.1, ?_⟩
    rw [← List.mapM_mapM_option, ← ctsMapM_ctsMapM_option]
    simp only [Option.bind_assoc]; congr 1; ext1 y; rw [Option.bind_comm]

theorem forall₂_congr {R S : α → β → Prop} (H : ∀ a b, R a b ↔ S a b) {l l'} :
    List.Forall₂ R l l' ↔ List.Forall₂ S l l' :=
  ⟨List.Forall₂.imp fun _ _ => (H _ _).1, List.Forall₂.imp fun _ _ => (H _ _).2⟩

theorem ctsRel_congr {R S : α → β → Prop} (H : ∀ a b, R a b ↔ S a b) {l l'} :
    CtsRel R l l' ↔ CtsRel S l l' :=
  ⟨CtsRel.imp fun _ _ => (H _ _).1, CtsRel.imp fun _ _ => (H _ _).2⟩

theorem forall₂_comp_iff {R : α → β → Prop} {S : β → γ → Prop} {T : α → γ → Prop}
    (H : ∀ a c, T a c ↔ ∃ b, R a b ∧ S b c) {l₁ l₃} :
    List.Forall₂ T l₁ l₃ ↔ ∃ l₂, List.Forall₂ R l₁ l₂ ∧ List.Forall₂ S l₂ l₃ := by
  constructor
  · intro h; induction h with
    | nil => exact ⟨[], .nil, .nil⟩
    | cons h _ ih =>
      have ⟨b, h1, h2⟩ := (H _ _).1 h; have ⟨l₂, h3, h4⟩ := ih
      exact ⟨b :: l₂, .cons h1 h3, .cons h2 h4⟩
  · rintro ⟨l₂, h1, h2⟩; induction h1 generalizing l₃ with
    | nil => cases h2; exact .nil
    | cons h _ ih => cases h2 with | cons h' h2 => exact .cons ((H _ _).2 ⟨_, h, h'⟩) (ih h2)

theorem ctsRel_comp_iff {R : α → β → Prop} {S : β → γ → Prop} {T : α → γ → Prop}
    (H : ∀ a c, T a c ↔ ∃ b, R a b ∧ S b c) {l₁ l₃} :
    CtsRel T l₁ l₃ ↔ ∃ l₂, CtsRel R l₁ l₂ ∧ CtsRel S l₂ l₃ := by
  refine forall₂_comp_iff fun p q => ⟨fun ⟨h1, h2⟩ => ?_, fun ⟨b, ⟨h1, h2⟩, h3, h4⟩ => ?_⟩
  · have ⟨b, h3, h4⟩ := (H _ _).1 h2; exact ⟨(p.1, b), ⟨rfl, h3⟩, h1, h4⟩
  · exact ⟨h1.trans h3, (H _ _).2 ⟨_, h2, h4⟩⟩

theorem ShapeFun.plift_plift (le : n₁ ≤ n₂ ∨ n₃ ≤ n₂) {s : ShapeFun n₁} :
    (plift (Shape.plift (m := n₃)) (plift (Shape.plift (m := n₂)) s).1).1 =
    (plift Shape.plift s).1 ∧
    ((plift Shape.plift s).2 : Option (ShapeFun n₃)) =
    ((plift Shape.plift s).2 : Option (ShapeFun n₂)).bind (plift Shape.plift · |>.2) :=
  Shape.plift_plift.go _ _ _ (Shape.plift_plift le)

theorem Shape.plift_thm (le : n ≤ m) {s : Shape m} {t : Shape n} :
    (t.lift m ≤ s ↔ t ≤ (s.plift (m := n)).1) ∧
    (s ≤ t.lift m ↔ ∃ z, (s.plift (m := n)).2 = some z ∧ z ≤ t) := by
  let rec go {n m}
      (IH : n ≤ m → ∀ {s : Shape m} {t : Shape n},
        (t.lift m ≤ s ↔ t ≤ s.plift.1) ∧ (s ≤ t.lift m ↔ ∃ z, s.plift.2 = some z ∧ z ≤ t))
      (le : n ≤ m) {s : ShapeFun m} {t : ShapeFun n} :
      (ShapeFun.LE (ShapeFun.lift (lift _) t) s ↔ ShapeFun.LE t (ShapeFun.plift plift s).1) ∧
      (ShapeFun.LE s (ShapeFun.lift (lift _) t) ↔
        ∃ z, (ShapeFun.plift plift s).2 = some z ∧ ShapeFun.LE z t) := by
    simp [ShapeFun.LE, ShapeFun.ble, ShapeFun.lift, ShapeFun.plift, List.mapM_eq_some,
      -List.any_filterMap, -Prod.forall]
    refine ⟨⟨fun H (a, b) h => ?_, fun H (a, b) h => ?_⟩,
      ⟨fun H => ?_, fun ⟨l, hl, hl2⟩ (a, b) h => ?_⟩⟩
    · obtain ⟨a₁, b₁, h1, h2, h3⟩ := H _ h
      have ⟨z, hz, hz2⟩ := (IH le).2.1 h2
      exact ⟨_, _, ⟨_, _, h1, _, hz, rfl, rfl⟩, hz2, (IH le).1.1 h3⟩
    · obtain ⟨_, _, ⟨_, _, h1, _, h2, rfl, rfl⟩, h3, h4⟩ := H _ h
      exact ⟨_, _, h1, (IH le).2.2 ⟨_, h2, h3⟩, (IH le).1.2 h4⟩
    · induction s with | nil => exact ⟨[], .nil, nofun⟩ | cons p s ih
      simp only [List.mem_cons, or_imp, forall_and, forall_eq] at H
      have ⟨⟨a', b', h1, h2, h3⟩, H⟩ := H
      have ⟨l, hl, hl2⟩ := ih H
      have ⟨z, hz, hz2⟩ := (IH le).2.1 h3
      refine ⟨_::l, .cons ⟨_, hz, rfl⟩ hl, ?_⟩
      exact List.forall_mem_cons.2 ⟨⟨_, _, h1, (IH le).1.1 h2, hz2⟩, hl2⟩
    · obtain ⟨_, h1, _, h2, rfl⟩ := hl.forall_exists_l _ h
      have ⟨_, _, h3, h4, h5⟩ := hl2 _ h1
      exact ⟨_, _, h3, (IH le).1.2 h4, (IH le).2.2 ⟨_, h2, h5⟩⟩
  unfold plift; split
    <;> (try (first | cases Nat.le_zero.1 le | cases n); cases t)
    <;> (try · simp [lift, sort, bot, (· ≤ ·), LE, ble])
    <;> (try · cases t <;> simp [lift, sort, bot, Shape.LE.def])
  · rename_i s _ _; cases s with
    | bot | sort => grind
    | _ => cases t <;> simp [lift, sort, bot, (· ≤ ·), LE, ble]
  all_goals have le := Nat.le_of_succ_le_succ le
  · cases t with simp [lift, sort, bot, Shape.LE.def]
    | forallE => ?_ | _ => intros; subst_vars; simp
    simp [Shape.plift_thm le,
      go Shape.plift_thm le]; grind
  · cases t with simp [lift, sort, bot, Shape.LE.def]
    | lam => ?_ | _ => intros; subst_vars; simp
    simp [go Shape.plift_thm le]; grind
  · cases t with simp [lift, sort, bot, Shape.LE.def, List.mapM_eq_some]
    | ctor => ?_ | _ => intros; subst_vars; simp
    refine ⟨fun _ => ?_, ?_, ?_⟩
    · apply Iff.of_eq; congr; funext a b
      exact propext (Shape.plift_thm le).1
    · rintro ⟨rfl, h⟩; rename_i c l _ l'
      suffices ∃ z, l.Forall₂ (·.plift.2 = some ·) z ∧ z.Forall₂ LE l' from
        have ⟨z, h1, h2⟩ := this; ⟨_, ⟨_, h1, rfl⟩, rfl, h2⟩
      induction h with | nil => exact ⟨_, .nil, .nil⟩ | cons h _ ih
      have ⟨a, a1, a2⟩ := (Shape.plift_thm le).2.1 h; have ⟨z, b1, b2⟩ := ih
      exact ⟨_, .cons a1 b1, .cons a2 b2⟩
    · rintro ⟨z, ⟨a, h1, rfl⟩, h2, h3⟩; refine ⟨h2, h1.trans (fun _ _ _ h1 h3 => ?_) h3⟩
      exact (Shape.plift_thm le).2.2 ⟨_, h1, h3⟩
  · cases t with simp [lift, sort, bot, Shape.LE.def, List.mapM_eq_some]
    | rigid => ?_ | _ => intros; subst_vars; simp
    have P1 {s : Shape _} {t : Shape _} := (Shape.plift_thm (s := s) (t := t) le).1
    have P2 {s : Shape _} {t : Shape _} := (Shape.plift_thm (s := s) (t := t) le).2
    refine ⟨fun _ _ => and_congr (forall₂_congr fun a c => P1 (s := c) (t := a)) ?_, ?_⟩
    · rw [ctsRel_map_left, ctsRel_map_right]; exact ctsRel_congr fun a c => P1 (s := c) (t := a)
    constructor
    · rintro ⟨rfl, rfl, h1, h2⟩
      have ⟨z1, a1, a2⟩ := (forall₂_comp_iff (fun a c => P2 (s := a) (t := c))).1 h1
      rw [ctsRel_map_right] at h2
      have ⟨z2, b1, b2⟩ := (ctsRel_comp_iff (fun a c => P2 (s := a) (t := c))).1 h2
      exact ⟨_, ⟨_, a1, _, ctsMapM_eq_some.2 b1, rfl⟩, rfl, rfl, a2, b2⟩
    · rintro ⟨_, ⟨z1, a1, z2, a2, rfl⟩, h1, h2, h3, h4⟩
      refine ⟨h1, h2, (forall₂_comp_iff (fun a c => P2 (s := a) (t := c))).2 ⟨_, a1, h3⟩, ?_⟩
      rw [ctsRel_map_right]
      exact (ctsRel_comp_iff (fun a c => P2 (s := a) (t := c))).2 ⟨_, ctsMapM_eq_some.1 a2, h4⟩

@[simp] theorem ctsZip_cons_cons {f : α → β → γ} :
    ctsZip f (p :: t) (q :: t') = (p.1, f p.2 q.2) :: ctsZip f t t' := rfl

theorem ctsRel_cons {R : α → β → Prop} :
    CtsRel R (p :: t) (q :: t') ↔ (p.1 = q.1 ∧ R p.2 q.2) ∧ CtsRel R t t' := List.forall₂_cons

theorem forall₂_compat_of_le {WF : α → Prop} {LE C : α → α → Prop}
    (H : ∀ x y z, WF x → WF y → WF z → LE x z → LE y z → C x y)
    {l l' l₃ : List α} (wf : ∀ x ∈ l, WF x) (wf' : ∀ x ∈ l', WF x) (wf₃ : ∀ x ∈ l₃, WF x)
    (h1 : List.Forall₂ LE l l₃) (h2 : List.Forall₂ LE l' l₃) : List.Forall₂ C l l' := by
  induction l generalizing l' l₃ with
  | nil => cases h1; cases h2; exact .nil
  | cons a l ih =>
    cases h1 with | cons h h1 =>
    cases h2 with | cons h' h2 =>
    simp only [List.forall_mem_cons] at wf wf' wf₃
    exact .cons (H _ _ _ wf.1 wf'.1 wf₃.1 h h') (ih wf.2 wf'.2 wf₃.2 h1 h2)

theorem ctsRel_compat_of_le {WF : α → Prop} {LE C : α → α → Prop}
    (H : ∀ x y z, WF x → WF y → WF z → LE x z → LE y z → C x y)
    {t t' t₃ : List (Name × α)} (wf : ∀ p ∈ t, WF p.2) (wf' : ∀ p ∈ t', WF p.2)
    (wf₃ : ∀ p ∈ t₃, WF p.2)
    (h1 : CtsRel LE t t₃) (h2 : CtsRel LE t' t₃) : CtsRel C t t' :=
  forall₂_compat_of_le (WF := fun p => WF p.2)
    (fun _ _ _ a1 a2 a3 b1 b2 => ⟨b1.1.trans b2.1.symm, H _ _ _ a1 a2 a3 b1.2 b2.2⟩)
    wf wf' wf₃ h1 h2

theorem forall₂_join {J : α → α → α} {WF : α → Prop} {LE C : α → α → Prop}
    (H : ∀ x y, WF x → WF y → C x y →
      WF (J x y) ∧ ∀ z, WF z → (LE (J x y) z ↔ LE x z ∧ LE y z))
    {l l' : List α} (wf : ∀ x ∈ l, WF x) (wf' : ∀ x ∈ l', WF x) (hc : List.Forall₂ C l l') :
    (∀ x ∈ l.zipWith J l', WF x) ∧ ∀ l₃, (∀ x ∈ l₃, WF x) →
      (List.Forall₂ LE (l.zipWith J l') l₃ ↔ List.Forall₂ LE l l₃ ∧ List.Forall₂ LE l' l₃) := by
  induction hc with
  | nil => exact ⟨by simp, fun l₃ _ => by cases l₃ <;> simp⟩
  | cons h _ ih =>
    simp only [List.forall_mem_cons] at wf wf'
    have ⟨a1, a2⟩ := H _ _ wf.1 wf'.1 h; have ⟨b1, b2⟩ := ih wf.2 wf'.2
    refine ⟨by simpa [List.forall_mem_cons] using ⟨a1, b1⟩, fun l₃ wf₃ => ?_⟩
    cases l₃ with
    | nil => simp
    | cons z l₃ =>
      simp only [List.forall_mem_cons] at wf₃
      simp only [List.zipWith_cons_cons, List.forall₂_cons, a2 _ wf₃.1, b2 _ wf₃.2]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, h3⟩, h2, h4⟩
      · rintro ⟨⟨h1, h3⟩, h2, h4⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩

theorem ctsRel_join {J : α → α → α} {WF : α → Prop} {LE C : α → α → Prop}
    (H : ∀ x y, WF x → WF y → C x y →
      WF (J x y) ∧ ∀ z, WF z → (LE (J x y) z ↔ LE x z ∧ LE y z))
    {t t' : List (Name × α)} (wf : ∀ p ∈ t, WF p.2) (wf' : ∀ p ∈ t', WF p.2)
    (hc : CtsRel C t t') :
    (∀ p ∈ ctsZip J t t', WF p.2) ∧ ∀ t₃, (∀ p ∈ t₃, WF p.2) →
      (CtsRel LE (ctsZip J t t') t₃ ↔ CtsRel LE t t₃ ∧ CtsRel LE t' t₃) := by
  induction hc with
  | nil => exact ⟨by simp [ctsZip], fun t₃ _ => by cases t₃ <;> simp [ctsZip]⟩
  | cons h _ ih =>
    simp only [List.forall_mem_cons] at wf wf'
    have ⟨a1, a2⟩ := H _ _ wf.1 wf'.1 h.2; have ⟨b1, b2⟩ := ih wf.2 wf'.2
    refine ⟨fun p hp => ?_, fun t₃ wf₃ => ?_⟩
    · simp only [ctsZip_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact a1
      · exact b1 p hp
    cases t₃ with
    | nil => simp [ctsZip]
    | cons z t₃ =>
      simp only [List.forall_mem_cons] at wf₃
      simp only [ctsZip_cons_cons, ctsRel_cons, a2 _ wf₃.1, b2 _ wf₃.2]
      constructor
      · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩; exact ⟨⟨⟨h1, h2⟩, h4⟩, ⟨h.1.symm.trans h1, h3⟩, h5⟩
      · rintro ⟨⟨⟨h1, h2⟩, h4⟩, ⟨-, h3⟩, h5⟩; exact ⟨⟨h1, h2, h3⟩, h4, h5⟩

theorem Shape.le_plift (le : n ≤ m) {s : Shape m} {t : Shape n} :
    t ≤ s.plift.1 ↔ t.lift m ≤ s := (Shape.plift_thm le).1.symm

theorem Shape.plift_le (le : n ≤ m) {s : Shape m} {t : Shape n} :
    (∃ z, s.plift.2 = some z ∧ z ≤ t) ↔ s ≤ t.lift m := (Shape.plift_thm le).2.symm

theorem ShapeFun.le_plift (le : n ≤ m) {s : ShapeFun m} {t : ShapeFun n} :
    LE t (plift Shape.plift s).1 ↔ LE (lift (Shape.lift m) t) s :=
  (Shape.plift_thm.go Shape.plift_thm le).1.symm

theorem ShapeFun.plift_le (le : n ≤ m) {s : ShapeFun m} {t : ShapeFun n} :
    (∃ z, (plift Shape.plift s).2 = some z ∧ LE z t) ↔ LE s (lift (Shape.lift m) t) :=
  (Shape.plift_thm.go Shape.plift_thm le).2.symm

theorem Shape.plift_mono {s t : Shape m} (H : s ≤ t) : (s.plift (m := n)).1 ≤ t.plift.1 := by
  obtain le | le := Nat.le_total m n
  · rw [Shape.plift_eq_lift le, Shape.plift_eq_lift le]; exact Shape.lift_mono H
  · exact (Shape.le_plift le).2 (.trans ((Shape.le_plift le).1 .rfl) H)

protected theorem Shape.Compat.plift {x y : Shape n} :
    (x.Compat y → (x.plift.1 : Shape m).Compat y.plift.1) ∧
    ∀ {x' y' : Shape m}, x.plift.2 = some x' → y.plift.2 = some y' → x'.Compat y' → x.Compat y := by
  obtain le | le := Nat.le_total n m
  · simp [plift_eq_lift le, Compat.lift le]
  refine ⟨fun h => ?_, fun h1 h2 h => ?_⟩
  · rw [← Compat.lift le]
    exact Compat.mono ((Shape.le_plift le).1 .rfl) ((Shape.le_plift le).1 .rfl) h
  · apply Compat.mono ((Shape.plift_le le).1 ⟨_, h1, .rfl⟩) ((Shape.plift_le le).1 ⟨_, h2, .rfl⟩)
    rwa [Compat.lift le]

theorem forall₂_eq_map_iff {f : β → α} {l : List α} {l'} :
    List.Forall₂ (fun a b => a = f b) l l' ↔ l = l'.map f := by
  rw [← List.forall₂_eq, List.forall₂_map_right_iff]

theorem ctsRel_eq_iff {f : β → α} {t : List (Name × α)} {t'} :
    CtsRel (fun a b => a = f b) t t' ↔ t = ctsMap f t' := by
  induction t generalizing t' with
  | nil => cases t' <;> simp
  | cons p t ih => cases t' <;> simp [ih, Prod.ext_iff, and_assoc]

def ShapeFun.olift (lift : α → Option β) (x : List (α × α)) : Option (List (β × β)) :=
  x.mapM fun (a, b) => return (← lift a, ← lift b)

def Shape.olift : ∀ {n m}, Shape n → Option (Shape m)
  | 0, _, .sort r | _+1, _, .sort r => some (.sort r)
  | 0, _, .bot | _+1, _, .bot => some .bot
  | _+1, 0, _ => none
  | _+1, _+1, .forallE s f => return .forallE (← s.olift) (← ShapeFun.olift olift f)
  | _+1, _+1, .lam f => return .lam (← ShapeFun.olift olift f)
  | _+1, _+1, .ctor c l => return .ctor c (← l.mapM (·.olift))
  | _+1, _+1, .rigid c ls l t => return .rigid c ls (← l.mapM (·.olift)) (← ctsMapM (·.olift) t)

theorem Shape.olift_eq_lift (le : n ≤ m) {s : Shape n} :
    s.olift = some (s.lift m) := by
  let rec go {n m} (IH : n ≤ m → ∀ {s : Shape n}, s.olift = some (s.lift m))
      (le : n ≤ m) {s : ShapeFun n} :
      ShapeFun.olift olift s = some (ShapeFun.lift (lift m) s) := by
    simp only [ShapeFun.olift, ShapeFun.lift, IH le]
    rw [List.mapM_eq_some, List.forall₂_map_right_iff]
    exact .rfl fun _ _ => rfl
  unfold olift; split <;> simp [lift] at le ⊢ <;> simp [olift_eq_lift le, go olift_eq_lift le]
  · exact ⟨_, List.mapM_pure, rfl⟩
  · exact ⟨_, List.mapM_pure, _, ctsMapM_some, rfl⟩

theorem ShapeFun.olift_eq_lift (le : n ≤ m) {s : ShapeFun n} :
    olift Shape.olift s = some (lift (Shape.lift m) s) :=
  Shape.olift_eq_lift.go Shape.olift_eq_lift le

theorem Shape.olift_thm (le : n ≤ m) {s : Shape m} {t : Shape n} :
    s.olift (m := n) = some t ↔ s = t.lift m := by
  let rec go {n m}
      (IH : n ≤ m → ∀ {s : Shape m} {t : Shape n}, s.olift (m := n) = some t ↔ s = t.lift m)
      (le : n ≤ m) {s : ShapeFun m} {t : ShapeFun n} :
      ShapeFun.olift olift s = some t ↔ s = ShapeFun.lift (lift m) t := by
    simp [ShapeFun.lift, ShapeFun.olift, List.mapM_eq_some]
    rw [← List.forall₂_eq, List.forall₂_map_right_iff]
    apply iff_of_eq; congr; ext ⟨a, a'⟩ ⟨b, b'⟩; simp [IH le]
  unfold olift; split
    <;> (try first | cases Nat.le_zero.1 le | cases n)
    <;> cases t <;> simp [lift, bot, sort]
  iterate 4 · grind
  all_goals have le := Nat.le_of_succ_le_succ le
  · simp [olift_thm le, go olift_thm le]; grind
  · simp [go olift_thm le]; grind
  · simp [List.mapM_eq_some, olift_thm le]
    conv => rhs; apply ShapeS.ctor.injEq
    rw [← List.forall₂_eq, List.forall₂_map_right_iff]; grind
  · simp only [List.mapM_eq_some, olift_thm le, ctsMapM_eq_some]
    constructor
    · rintro ⟨a, h1, b, h2, h⟩; cases h
      rw [forall₂_eq_map_iff.1 h1, ctsRel_eq_iff.1 h2]
    · intro h; injection h with h1 h2 h3 h4; subst h1 h2 h3 h4
      exact ⟨_, forall₂_eq_map_iff.2 rfl, _, ctsRel_eq_iff.2 rfl, rfl⟩

theorem ShapeFun.olift_thm (le : n ≤ m) {s : ShapeFun m} {t : ShapeFun n} :
    olift Shape.olift s = some t ↔ s = lift (Shape.lift m) t :=
  Shape.olift_thm.go Shape.olift_thm le

theorem Shape.lift_inj (le : n ≤ m) {s t : Shape n} : s.lift m = t.lift m ↔ s = t := by
  refine ⟨fun H => ?_, (· ▸ rfl)⟩
  cases ((Shape.olift_thm le).2 H).symm.trans <| (Shape.olift_thm le).2 rfl; rfl

theorem ShapeFun.lift_inj (le : n ≤ m) {s t : ShapeFun n} :
    lift (Shape.lift m) s = lift (Shape.lift m) t ↔ s = t := by
  refine ⟨fun H => ?_, (· ▸ rfl)⟩
  cases ((ShapeFun.olift_thm le).2 H).symm.trans <| (ShapeFun.olift_thm le).2 rfl; rfl

@[simp] theorem Shape.olift_bot : Shape.olift (n := n) (m := m) .bot = some .bot := by
  cases n <;> cases m <;> rfl

@[simp] theorem ShapeFun.olift_bot :
    olift (Shape.olift (n := n) (m := m)) ShapeFun.bot = some ShapeFun.bot := by
  simp [bot, olift]

@[simp] theorem Shape.olift_sort : Shape.olift (n := n) (m := m) (.sort r) = some (.sort r) := by
  cases n <;> cases m <;> rfl

def ShapeFun.maxBelow (s : ShapeFun n) : Shape n × Shape n :=
  (s.find? fun (x, _) => s.all fun (x', _) => x' ≤ x).getD (.bot, .bot)

def ShapeFun.trunc (s : ShapeFun n) (a : Shape n) : ShapeFun n := s.filter (·.1 ≤ a)
def ShapeFun.app (s : ShapeFun n) (a : Shape n) : Shape n := maxBelow (s.trunc a) |>.2

theorem ShapeFun.lift_trunc (le : n ≤ m) :
    lift (Shape.lift m) (trunc f a : ShapeFun n) = trunc (lift (Shape.lift m) f) (a.lift m) := by
  simp [trunc, lift, List.filter_map]; congr 2; ext x; simp [Shape.lift_le_lift le]

theorem ShapeFun.lift_maxBelow {f : ShapeFun n} (le : n ≤ m) :
    (maxBelow f).1.lift m = (maxBelow (lift (Shape.lift m) f)).1 ∧
    (maxBelow f).2.lift m = (maxBelow (lift (Shape.lift m) f)).2 := by
  refine let F x := (x.1.lift m, x.2.lift m)
    have : F (maxBelow f) = maxBelow (lift (Shape.lift m) f) := ?_
    ⟨congrArg (·.1) this, congrArg (·.2) this⟩
  simp [maxBelow, lift]
  generalize eq₁ : List.find? .. = r, eq₂ : List.find? .. = r'
  suffices r = r' by subst this; cases r <;> simp [F]
  subst eq₁ eq₂; congr 1; ext x; simp; congr 1; ext y; simp [Shape.lift_le_lift le]

@[simp] theorem ShapeFun.lift_app (le : n ≤ m) :
    (app f a : Shape n).lift m = app (lift (Shape.lift m) f) (a.lift m) := by
  simp [app, lift_trunc le, lift_maxBelow le]

/-- Applying a lifted function only looks at the truncation of the argument. -/
theorem ShapeFun.app_lift_plift (le : n ≤ m) {b : ShapeFun n} {f : Shape m} :
    app (lift (Shape.lift m) b) f = (app b (f.plift (m := n)).1).lift m := by
  rw [lift_app le]; simp only [app, trunc]; congr 2
  apply List.filter_congr; intro x hx
  simp only [lift, List.mem_map] at hx; obtain ⟨⟨a, _⟩, _, rfl⟩ := hx
  simp only [decide_eq_decide]; rw [Shape.lift_le_lift le, Shape.le_plift le]

def ShapeFun.join (join : Shape n → Shape n → Shape n) (f f' : ShapeFun n) : ShapeFun n :=
  f.foldl (init := []) fun l x => f'.foldl (init := l) fun l y =>
  if x.1.Compat y.1 then let j := join x.1 y.1; (j, join (f.app j) (f'.app j)) :: l else l

theorem ShapeFun.mem_join {join} {f f' : ShapeFun n} {a} :
    a ∈ ShapeFun.join join f f' ↔ ∃ x ∈ f, ∃ y ∈ f', x.1.Compat y.1 ∧
      let j := join x.1 y.1; a = (j, join (f.app j) (f'.app j)) := by
  refine let F x := _; let G x y := _
    (?_ : a ∈ f.foldl (fun l x => f'.foldl (F x) l) [] ↔ (∃ x ∈ f, ∃ y ∈ f', G x y) ∨ a ∈ [])
    |>.trans (or_iff_left (by simp))
  generalize f = f₁, f' = f₂, [] = l
  induction f₁ generalizing l with simp [-Prod.exists, or_assoc, *] | cons _ f₁ ih
  refine .trans (or_congr_right ?_) or_left_comm; clear ih
  induction f₂ generalizing l <;> simp [-Prod.exists, or_assoc, *]
  refine .trans (or_congr_right ?_) or_left_comm
  unfold F G; split <;> rename_i h <;> simp [h]

def Shape.join : ∀ {n}, Shape n → Shape n → Shape n
  | 0, s, .bot | 0, .bot, s | _+1, .bot, s | _+1, s, .bot => s
  | 0, .sort r, .sort r' | _+1, .sort r, .sort r' => if r = r' then .sort r else .bot
  | _+1, .forallE s f, .forallE s' f' => .forallE (join s s') (ShapeFun.join join f f')
  | _+1, .lam f, .lam f' => .lam (ShapeFun.join join f f')
  | _+1, .ctor c l, .ctor c' l' => if c = c' then .ctor c (l.zipWith join l') else .bot
  | _+1, .rigid c ls l t, .rigid c' ls' l' t' =>
    if c = c' ∧ ls = ls' then .rigid c ls (l.zipWith join l') (ctsZip join t t') else .bot
  | _+1, _, _ => .bot

theorem Shape.lift_join {x y : Shape n} (le : n ≤ m) :
    (x.join y).lift m = (x.lift m).join (y.lift m) := by
  induction n generalizing m with
  | zero =>
    cases m with | zero => simp [lift_self] | succ m
    cases x <;> cases y <;> simp [lift, join, sort]; split <;> simp [lift, sort]
  | succ n ih
  let m + 1 := m; replace le := Nat.le_of_succ_le_succ le; replace ih {x y} := @ih m x y le
  let rec go {x y : ShapeFun n} :
      ShapeFun.lift (lift m) (ShapeFun.join join x y) =
      ShapeFun.join join (ShapeFun.lift (lift m) x) (ShapeFun.lift (lift m) y) := by
    refine
      let G _ := _; let F l x := List.foldl (G x) l y
      let G' _ := _; let F' l x := List.foldl (G' x) l (ShapeFun.lift (lift m) y)
      have (r:_) : ShapeFun.lift (lift m) (x.foldl F r) =
        (ShapeFun.lift (lift m) x).foldl F' (r.map fun x => (lift m x.1, lift m x.2)) := ?_
      this []
    simp [ShapeFun.lift]; generalize x = x'; induction x' generalizing r <;> simp [*]; congr 1
    unfold F F'
    simp [ShapeFun.lift]; generalize y = y'; induction y' generalizing r <;> simp [*]; congr 1
    simp [G, G', Compat.lift le]; split <;> simp [ih, ShapeFun.lift_app le]
  cases x with cases y <;> simp [join, lift, go, sort, ih]
  | sort => split <;> simp [lift, sort]
  | ctor => split <;> simp [lift, ih]
  | rigid =>
    split <;> simp [lift, ih, List.map_zipWith]
    rw [ctsZip_ctsMap fun a b => ih (x := a) (y := b)]

theorem Shape.bot_join {x : Shape n} : bot.join x = x := by cases n <;> cases x <;> rfl
theorem Shape.join_bot {x : Shape n} : x.join bot = x := by cases n <;> cases x <;> rfl
@[simp] theorem Shape.sort_join_sort :
    join (.sort r : Shape n) (.sort r') = if r = r' then .sort r else .bot := by cases n <;> rfl

theorem ShapeFun.lift_join {x y : ShapeFun n} (le : n ≤ m) :
    lift (Shape.lift m) (join Shape.join x y) =
    join Shape.join (lift (Shape.lift m) x) (lift (Shape.lift m) y) :=
  Shape.lift_join.go _ _ le (Shape.lift_join le)

def Shape.lam' (s : ShapeFun n) : Shape (n + 1) :=
  if s.all (·.2 ≤ .bot) then .bot else .lam s

def IsStruct [ShapeParams] (n : Name) : Bool := ShapeParams.isStruct n

variable [ShapeParams]

def Shape.ctor' (c : Name) (l : List (Shape n)) : Shape (n + 1) :=
  if IsStruct c ∧ l.all (· ≤ .bot) then .bot else .ctor c l

def Shape.trim : ∀ {n}, Shape n → Shape n
  | 0, s => s
  | _+1, .bot => .bot
  | _+1, .sort r => .sort r
  | _+1, .forallE s f => .forallE s.trim (f.map fun x => (x.1.trim, x.2.trim))
  | _+1, .lam f => .lam' (f.map fun x => (x.1.trim, x.2.trim))
  | _+1, .ctor c l => .ctor' c (l.map trim)
  | _+1, .rigid c ls l t => .rigid c ls (l.map trim) (ctsMap trim t)

def ShapeFun.WF (WF : Shape n → Prop) (f : ShapeFun n) : Prop :=
  ((∃ y, (.bot, y) ∈ f) ∧ ∀ x ∈ f, ∀ y ∈ f,
    (x.1.Compat y.1 → ∃ z ∈ f, x.1.join y.1 ≤ z.1 ∧ z.1 ≤ x.1.join y.1) ∧
    (x.1 ≤ y.1 → x.2 ≤ y.2)) ∧
  ∀ x ∈ f, WF x.1 ∧ WF x.2

def ShapeFun.NonZero (f : ShapeFun n) := ∃ x ∈ f, ¬x.2 ≤ .bot
def Shape.ListNonZero (l : List (Shape n)) := ∃ x ∈ l, ¬x ≤ .bot

instance {f : ShapeFun n} : Decidable f.NonZero :=
  inferInstanceAs (Decidable (∃ x ∈ f, ¬x.2 ≤ .bot))
instance {l : List (Shape n)} : Decidable (Shape.ListNonZero l) :=
  inferInstanceAs (Decidable (∃ x ∈ l, ¬x ≤ .bot))

omit [ShapeParams] in
theorem ShapeFun.NonZero.mono {f f' : ShapeFun n} (le : f.LE f') : NonZero f → NonZero f'
  | ⟨_, h1, h2⟩ => have ⟨_, _, a1, _, a2⟩ := ShapeFun.LE.def.1 le _ _ h1; ⟨_, a1, mt a2.trans h2⟩

omit [ShapeParams] in
theorem Shape.ListNonZero.mono {l l' : List (Shape n)}
    (le : l.Forall₂ (· ≤ ·) l') : ListNonZero l → ListNonZero l'
  | ⟨_, h1, h2⟩ => have ⟨_, a1, a2⟩ := le.forall_exists_l _ h1; ⟨_, a1, mt a2.trans h2⟩

def Shape.WF : ∀ {n}, Shape n → Prop
  | 0, _ | _+1, .bot | _+1, .sort .. => True
  | _+1, .forallE s f => s.WF ∧ ShapeFun.WF WF f
  | _+1, .lam f => ShapeFun.WF WF f ∧ ShapeFun.NonZero f
  | _+1, .ctor n l => (∀ x ∈ l, WF x) ∧ (IsStruct n → ListNonZero l)
  | _+1, .rigid _ _ l t => (∀ x ∈ l, WF x) ∧ ∀ p ∈ t, WF p.2

omit [ShapeParams] in
theorem ShapeFun.NonZero.lift_iff {n m} {x : ShapeFun n} (le : n ≤ m) :
    NonZero (lift (Shape.lift m) x) ↔ NonZero (n := n) x := by
  simp [NonZero, lift]
  refine ⟨fun ⟨_, _, ⟨_, _, h1, rfl, rfl⟩, h2⟩ => ?_, fun ⟨_, _, h1, h2⟩ => ?_⟩
  · exact ⟨_, _, h1, mt ((Shape.lift_le_bot le).2 ∘ Shape.le_bot.1) h2⟩
  · exact ⟨_, _, ⟨_, _, h1, rfl, rfl⟩, mt (Shape.le_bot.2 ∘ (Shape.lift_le_bot le).1) h2⟩

omit [ShapeParams] in
theorem Shape.ListNonZero.lift_iff {n m} {x : List (Shape n)} (le : n ≤ m) :
    ListNonZero (x.map (lift m)) ↔ ListNonZero (n := n) x := by
  simp [ListNonZero]
  constructor
  · exact fun ⟨_, ⟨_, h1, rfl⟩, h2⟩ => ⟨_, h1, mt ((Shape.lift_le_bot le).2 ∘ Shape.le_bot.1) h2⟩
  · exact fun ⟨_, h1, h2⟩ => ⟨_, ⟨_, h1, rfl⟩, mt (Shape.le_bot.2 ∘ (Shape.lift_le_bot le).1) h2⟩

theorem Shape.WF.lift_iff (le : n ≤ m) : WF (x.lift m) ↔ WF (n := n) x := by
  induction n generalizing m with | zero => cases m <;> cases x <;> trivial | succ n ih
  let m + 1 := m; replace le := Nat.le_of_succ_le_succ le; replace ih {x} := @ih m x le
  let rec go {x : ShapeFun n} : ShapeFun.WF WF (ShapeFun.lift (lift m) x) ↔ ShapeFun.WF WF x := by
    simp only [ShapeFun.WF, ShapeFun.lift, List.mem_map, Prod.mk.injEq,
      lift_eq_bot le, Prod.exists, exists_and_right, forall_exists_index, and_imp, Prod.forall]
    constructor
    · intro ⟨⟨⟨_, _, _, a1, rfl, rfl⟩, a2⟩, a3⟩; refine ⟨⟨⟨_, a1⟩, ?_⟩, fun _ _ h1 => ?_⟩
      · intro _ _ h1 _ _ h2; have := a2 _ _ _ _ h1 rfl rfl _ _ _ _ h2 rfl rfl
        simp [lift_le_lift le, Compat.lift le, ← lift_join le] at this
        refine ⟨fun h => ?_, this.2⟩
        let ⟨_, ⟨_, _, _, b1, rfl, rfl⟩, b2⟩ := this.1 h
        simp only [lift_le_lift le] at b2; exact ⟨_, ⟨_, b1⟩, b2⟩
      · simpa only [ih] using a3 _ _ _ _ h1 rfl rfl
    · intro ⟨⟨⟨_, a1⟩, a2⟩, a3⟩; refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact ⟨_, _, _, a1, rfl, rfl⟩
      · intro _ _ _ _ h1 rfl rfl _ _ _ _ h2 rfl rfl; have := a2 _ _ h1 _ _ h2
        simp [lift_le_lift le, Compat.lift le, ← lift_join le]
        refine ⟨fun h => ?_, this.2⟩
        let ⟨_, ⟨_, b1⟩, b2⟩ := this.1 h
        refine ⟨_, ⟨_, _, _, b1, rfl, rfl⟩, ?_⟩; simpa only [lift_le_lift le] using b2
      · intro _ _ _ _ h1 rfl rfl; simpa only [ih] using a3 _ _ h1
  cases x with simp [lift, WF, go, *]
  | lam => exact fun _ => ShapeFun.NonZero.lift_iff le
  | ctor => exact fun _ => imp_congr_right fun _ => Shape.ListNonZero.lift_iff le
  | rigid =>
    intro _; constructor
    · intro H a b h; exact ih.1 (H a (lift m b) (mem_ctsMap.2 ⟨_, h, rfl⟩))
    · intro H a b hp; obtain ⟨q, hq, h⟩ := mem_ctsMap.1 hp; cases h; exact ih.2 (H _ _ hq)

theorem ShapeFun.WF.lift_iff {x : ShapeFun n} (le : n ≤ m) :
    WF Shape.WF (lift (Shape.lift m) x) ↔ WF Shape.WF x :=
  Shape.WF.lift_iff.go _ _ le (Shape.WF.lift_iff le)

protected theorem Shape.WF.lift (le : n ≤ m) : WF (n := n) x → WF (x.lift m) := (lift_iff le).2

protected theorem ShapeFun.WF.lift {x : ShapeFun n} (le : n ≤ m) : WF Shape.WF x →
    WF Shape.WF (lift (Shape.lift m) x) := (lift_iff le).2

protected theorem Shape.WF.olift {x : Shape n} (H : x.olift (m := m) = some x') :
    WF x ↔ WF x' := by
  obtain le | le := Nat.le_total n m
  · cases olift_eq_lift le ▸ H; rw [WF.lift_iff le]
  · cases (olift_thm le).1 H; rw [WF.lift_iff le]

protected theorem ShapeFun.WF.olift {x : ShapeFun n}
    (H : olift (Shape.olift (m := m)) x = some x') : WF Shape.WF x ↔ WF Shape.WF x' := by
  obtain le | le := Nat.le_total n m
  · cases ShapeFun.olift_eq_lift le ▸ H; rw [WF.lift_iff le]
  · cases (olift_thm le).1 H; rw [WF.lift_iff le]

protected theorem Shape.WF.bot : (Shape.bot (n := n)).WF := by cases n <;> trivial
protected theorem Shape.WF.sort : (Shape.sort (n := n) r).WF := by cases n <;> trivial

protected theorem ShapeFun.WF.bot : (ShapeFun.bot (n := n)).WF Shape.WF := by
  simp [WF, bot, Shape.Compat.bot_l, Shape.bot_join, Shape.WF.bot]

@[implicit_reducible] def WShape (n : Nat) := {s : Shape n // s.WF}
@[implicit_reducible] def WShapeFun (n : Nat) := {s : ShapeFun n // s.WF Shape.WF}

instance : Membership (WShape n × WShape n) (WShapeFun n) := ⟨fun f a => (a.1.1, a.2.1) ∈ f.1⟩

theorem WShapeFun.mem_def {f : WShapeFun n} : a ∈ f ↔ (a.1.1, a.2.1) ∈ f.1 := .rfl

theorem WShapeFun.mem_val {f : WShapeFun n} {s t : Shape n} (h : (s, t) ∈ f.1) :
    (⟨s, (f.2.2 _ h).1⟩, ⟨t, (f.2.2 _ h).2⟩) ∈ f := h
theorem WShapeFun.mem_val' {f : WShapeFun n} {s t : Shape n} (h : (s, t) ∈ f.1) :
    ∃ hs ht, (⟨s, hs⟩, ⟨t, ht⟩) ∈ f := ⟨(f.2.2 _ h).1, (f.2.2 _ h).2, h⟩

def WShapeFun.elems (f : WShapeFun n) : List (WShape n × WShape n) :=
  f.1.pmap (fun a wf => (⟨a.1, wf.1⟩, ⟨a.2, wf.2⟩)) f.2.2

@[simp] theorem WShapeFun.mem_elems {f : WShapeFun n} : a ∈ f.elems ↔ a ∈ f := by
  simp only [elems, List.mem_pmap, Prod.exists, mem_def]
  exact ⟨fun ⟨_, _, h, rfl⟩ => h, fun h => ⟨_, _, h, rfl⟩⟩

@[ext] theorem WShape.ext {s t : WShape n} (h : s.1 = t.1) : s = t := Subtype.ext h
@[ext] theorem WShapeFun.ext {s t : WShapeFun n} (h : s.1 = t.1) : s = t := Subtype.ext h

def WShapeFun.NonZero (f : WShapeFun n) := f.1.NonZero
instance {f : WShapeFun n} : Decidable f.NonZero := inferInstanceAs (Decidable f.1.NonZero)

def WShape.bot : WShape n := ⟨.bot, .bot⟩
def WShape.sort (r : SLvl) : WShape n := ⟨.sort r, .sort⟩
abbrev WShape.type : WShape n := .sort (fun _ => 1)
abbrev WShape.prop : WShape n := .sort (fun _ => 0)
def WShape.forallE (s : WShape n) (f : WShapeFun n) : WShape (n + 1) := ⟨.forallE s.1 f.1, s.2, f.2⟩
def WShape.lam (f : WShapeFun n) (h : f.NonZero) :
    WShape (n + 1) := ⟨.lam f.1, f.2, h⟩
def WShape.lam' (f : WShapeFun n) : WShape (n + 1) := if h : f.NonZero then .lam f h else .bot
theorem WShape.lam_eq_lam' {f : WShapeFun n} {hl} : WShape.lam f hl = .lam' f := by
  simp [lam', hl]

/-- A rigid type former: name, evaluated levels, argument shapes, and the constructor table
(one telescope per constructor, over the constructor's fields). -/
def WShape.rigid (c : Name) (ls : List SLvl) (l : List (WShape n))
    (t : List (Name × WShape n)) : WShape (n + 1) := by
  refine ⟨.rigid c ls (l.map (·.1)) (ctsMap (·.1) t), fun _ h => ?_, fun _ h => ?_⟩
  · have ⟨x, _, eq⟩ := List.mem_map.1 h; exact eq ▸ x.2
  · have ⟨x, _, eq⟩ := mem_ctsMap.1 h; exact eq ▸ x.2.2

/-- Attach the well-formedness proofs to a constructor table. -/
def ctsAttach (t : List (Name × Shape n)) (H : ∀ p ∈ t, Shape.WF p.2) :
    List (Name × WShape n) := t.pmap (fun p h => (p.1, ⟨p.2, h⟩)) H

theorem ctsMap_ctsAttach {t : List (Name × Shape n)} {H} :
    ctsMap (·.1) (ctsAttach t H) = t := by
  simp [ctsMap, ctsAttach, List.map_pmap]

theorem WShape.mk_rigid {n} (l : List (Shape n)) (t : List (Name × Shape n))
    (wf : Shape.WF (n := n+1) (.rigid c ls l t)) :
    WShape.rigid c ls (l.pmap Subtype.mk wf.1) (ctsAttach t wf.2) = ⟨.rigid c ls l t, wf⟩ := by
  apply Subtype.ext; simp only [WShape.rigid, ctsMap_ctsAttach]
  rw [List.map_pmap, List.pmap_eq_map, List.map_id']

def WShape.ListNonZero (l : List (WShape n)) := ∃ x ∈ l, ¬x.1 ≤ .bot
instance {l : List (WShape n)} : Decidable (WShape.ListNonZero l) :=
  inferInstanceAs (Decidable (∃ x ∈ l, ¬x.1 ≤ .bot))

theorem WShape.ListNonZero.def {l : List (WShape n)} :
    ListNonZero l ↔ Shape.ListNonZero (l.map (·.1)) := by
  simp only [ListNonZero, Shape.ListNonZero, List.mem_map]
  exact ⟨fun ⟨_, h1, h2⟩ => ⟨_, ⟨_, h1, rfl⟩, h2⟩, fun ⟨_, ⟨_, h1, rfl⟩, h2⟩ => ⟨_, h1, h2⟩⟩
def WShape.ctor (c : Name) (l : List (WShape n))
    (H : IsStruct c → ListNonZero l) : WShape (n + 1) := by
  refine ⟨.ctor c (l.map (·.1)), fun _ h => ?_, ListNonZero.def.1 ∘ H⟩
  have ⟨x, _, eq⟩ := List.mem_map.1 h; exact eq ▸ x.2
def WShape.ctor' (c : Name) (l : List (WShape n)) : WShape (n + 1) :=
  if h : IsStruct c → ListNonZero l then
    .ctor c l (by simpa [Shape.le_bot] using h)
  else .bot

theorem WShape.mk_ctor {n} (l : List (Shape n)) (wf : Shape.WF (n := n+1) (.ctor c l)) :
    ∃ h, WShape.ctor c (l.pmap Subtype.mk wf.1) h = ⟨.ctor c l, wf⟩ := by
  refine ⟨fun h => ?_, Subtype.ext ?_⟩
  · simp [ListNonZero]; let ⟨_, h1, h2⟩ := wf.2 h; exact ⟨_, ⟨_, h1, rfl⟩, h2⟩
  · simp [WShape.ctor]; congr 1; rw [List.map_pmap, List.pmap_eq_map, List.map_id']

theorem WShape.ctor_eq_ctor' : ctor c l h = ctor' c l := by rw [ctor', dif_pos]

def WShapeFun.bot {n : Nat} : WShapeFun n := ⟨.bot, .bot⟩

theorem WShapeFun.NonZero.bot : ¬NonZero (n := n) .bot := by
  simp [NonZero, WShapeFun.bot, ShapeFun.bot, ShapeFun.NonZero]

@[simp] theorem WShape.lam'_bot : WShape.lam' (n := n) .bot = .bot := by
  simp [lam', WShapeFun.NonZero.bot]

theorem WShapeFun.mem_bot : (x, y) ∈ WShapeFun.bot ↔ x = .bot ∧ y = .bot := by
  simp [WShapeFun.mem_def, bot, WShape.ext_iff, WShape.bot, ShapeFun.bot]

/-- Case split on a `WShape (n+1)`. -/
@[elab_as_elim]
def WShape.casesOn' {motive : WShape (n+1) → Sort u}
    (s : WShape (n+1))
    (bot : motive .bot)
    (sort : ∀ r, motive (.sort r))
    (forallE : ∀ s f, motive (.forallE s f))
    (lam : ∀ f h, motive (.lam f h))
    (ctor : ∀ c l h, motive (.ctor c l h))
    (rigid : ∀ c ls l t, motive (.rigid c ls l t)) : motive s := by
  obtain ⟨s, wf⟩ := s
  cases s with
  | bot => exact bot
  | sort r => exact sort r
  | forallE s' f' => exact forallE ⟨s', wf.1⟩ ⟨f', wf.2⟩
  | lam f' => exact lam ⟨f', wf.1⟩ wf.2
  | ctor c l => exact (WShape.mk_ctor l wf).2 ▸ ctor ..
  | rigid c ls l t => exact WShape.mk_rigid l t wf ▸ rigid ..

/-- Case split on a `WShape n`. -/
@[elab_as_elim]
def WShape.casesOn {motive : ∀ {n}, WShape n → Sort u}
    {n} (s : WShape n)
    (bot : motive (n := n) .bot)
    (sort : ∀ r, motive (n := n) (.sort r))
    (forallE : ∀ {n'} s f, motive (n := n'+1) (.forallE s f))
    (lam : ∀ {n'} f h, motive (n := n'+1) (.lam f h))
    (ctor : ∀ {n'} c l h, motive (n := n'+1) (.ctor c l h))
    (rigid : ∀ {n'} c ls l t, motive (n := n'+1) (.rigid c ls l t)) : motive s := by
  cases n with
  | zero =>
    obtain ⟨s, wf⟩ := s
    cases s with
    | bot => exact bot
    | sort r => exact sort r
  | succ n => exact s.casesOn' bot sort forallE lam ctor rigid

def WShape.lift {n} (m) (s : WShape n) : WShape m := by
  refine ⟨(s.1.olift (m := m)).getD .bot, ?_⟩
  cases eq : s.1.olift <;> [exact .bot; exact (Shape.WF.olift eq).1 s.2]

def WShapeFun.lift {n} (m) (s : WShapeFun n) : WShapeFun m := by
  refine ⟨(ShapeFun.olift Shape.olift s.1).getD ShapeFun.bot, ?_⟩
  cases eq : ShapeFun.olift Shape.olift s.1 <;> [exact .bot; exact (ShapeFun.WF.olift eq).1 s.2]

abbrev WShape.LE (a b : WShape n) := a.1 ≤ b.1
abbrev WShapeFun.LE (a b : WShapeFun n) := a.1.LE b.1
instance : LE (WShape n) := ⟨WShape.LE⟩
instance : LE (WShapeFun n) := ⟨WShapeFun.LE⟩

instance : DecidableRel (α := WShape n) (· ≤ ·) := fun a b => inferInstanceAs (Decidable (a.1 ≤ b.1))
instance : DecidableRel (α := WShapeFun n) (· ≤ ·) :=
  fun a b => inferInstanceAs (Decidable (a.1.LE b.1))

theorem WShape.LE.def {a b : WShape n} : a ≤ b ↔ a.1 ≤ b.1 := .rfl
theorem WShapeFun.LE.def {a b : WShapeFun n} : a ≤ b ↔ a.1.LE b.1 := .rfl

theorem WShapeFun.NonZero.iff {f : WShapeFun n} : f.NonZero ↔ ∃ x ∈ f, ¬x.2 ≤ .bot :=
  ⟨fun ⟨_, h1, h2⟩ => ⟨_, f.mem_val h1, h2⟩, fun ⟨_, h1, h2⟩ => ⟨_, h1, h2⟩⟩

theorem WShapeFun.NonZero.mono {f f' : WShapeFun n} :
    (h1 : f.LE f') → (h2 : NonZero f) → NonZero f' :=
  ShapeFun.NonZero.mono

theorem WShape.ListNonZero.mono {l l' : List (WShape n)}
    (le : l.Forall₂ (· ≤ ·) l') : ListNonZero l → ListNonZero l' := by
  simp [ListNonZero.def]; apply Shape.ListNonZero.mono; simpa

theorem WShape.lift_val {s : WShape n} (le : n ≤ m) : (s.lift m).1 = s.1.lift m := by
  simp [lift, Shape.olift_eq_lift le]

theorem WShapeFun.lift_val {s : WShapeFun n} (le : n ≤ m) :
    (s.lift m).1 = ShapeFun.lift (Shape.lift m) s.1 := by
  simp [lift, ShapeFun.olift_eq_lift le]

theorem WShapeFun.mem_lift {s : WShapeFun n} (le : n ≤ m) :
    (x, x') ∈ s.lift m ↔ ∃ y y', (y, y') ∈ s ∧ x = y.lift m ∧ x' = y'.lift m := by
  cases x; cases x'
  simp [mem_def, lift_val le, WShape.lift_val le, ShapeFun.lift, WShape.ext_iff]
  constructor <;> exact fun ⟨_, _, h1, h2, h3⟩ => ⟨_, _, s.mem_val h1, h2.symm, h3.symm⟩

theorem WShape.forallE.inj {f : WShapeFun n} :
    WShape.forallE a f = WShape.forallE a' f' ↔ a = a' ∧ f = f' := by
  simp [WShape.ext_iff, WShapeFun.ext_iff, forallE]
  exact iff_of_eq (ShapeS.forallE.injEq ..)

theorem ctsMap_val_inj {t t' : List (Name × WShape n)} :
    ctsMap (·.1) t = ctsMap (·.1) t' ↔ t = t' := by
  induction t generalizing t' with
  | nil => cases t' <;> simp
  | cons p t ih =>
    cases t' with
    | nil => simp
    | cons q t' => simp [ih, Prod.ext_iff, WShape.ext_iff]

theorem WShape.rigid.inj {l l' : List (WShape n)} {t t'} :
    WShape.rigid c ls l t = WShape.rigid c' ls' l' t' ↔ c = c' ∧ ls = ls' ∧ l = l' ∧ t = t' := by
  simp only [WShape.ext_iff, rigid]
  refine iff_of_eq (ShapeS.rigid.injEq ..) |>.trans ?_
  exact and_congr_right' (and_congr_right' (and_congr (List.map_inj_right fun _ _ => Subtype.ext)
    ctsMap_val_inj))

@[simp] theorem WShape.lift_bot : (WShape.bot : WShape n).lift m = .bot := by
  ext; simp [lift, bot]

@[simp] theorem WShapeFun.lift_bot : WShapeFun.lift (n := n) m .bot = .bot := by
  ext1; simp [WShapeFun.lift, bot, ShapeFun.olift_bot]

@[simp] theorem WShape.lift_sort : (WShape.sort r : WShape n).lift m = .sort r := by
  ext; simp [lift, sort]

@[simp] theorem WShape.lift_type : (WShape.type (n := n)).lift m = WShape.type := WShape.lift_sort

theorem WShape.lift_self {s : WShape n} : s.lift n = s := by
  ext; rw [lift_val (Nat.le_refl _), Shape.lift_self]

theorem WShapeFun.lift_self {s : WShapeFun n} : s.lift n = s := by
  ext; rw [lift_val (Nat.le_refl _), ShapeFun.lift_self]

theorem WShape.lift_lift {s : WShape n₁} (le : n₁ ≤ n₂ ∨ n₃ ≤ n₂) :
    (s.lift n₂).lift n₃ = s.lift n₃ := by
  ext; simp [lift]
  by_cases h1 : n₁ ≤ n₂
  · congr 1; ext t; rw [Shape.olift_eq_lift h1, Option.getD]
    obtain h2 | h2 := Nat.le_total n₂ n₃
    · rw [Shape.olift_eq_lift h2, Shape.lift_lift (.inl h1),
        Shape.olift_eq_lift (Nat.le_trans h1 h2)]
    rw [Shape.olift_thm h2]
    obtain h3 | h3 := Nat.le_total n₁ n₃
    · rw [Shape.olift_eq_lift h3, Option.some_inj, ← Shape.lift_lift (.inl h3), Shape.lift_inj h2]
    · rw [Shape.olift_thm h3, ← Shape.lift_lift (.inl h3), Shape.lift_inj h1]
  · have h2 := le.resolve_left h1; have h1 := Nat.le_of_not_ge h1
    cases eq : s.1.olift (m := n₂) <;> simp
    · cases eq' : s.1.olift (m := n₃) <;> simp
      rw [Shape.olift_thm (Nat.le_trans h2 h1), ← Shape.lift_lift (.inl h2),
        ← Shape.olift_thm h1, eq] at eq'; cases eq'
    · rw [(Shape.olift_thm h1).1 eq]; rename_i t
      cases eq₁ : t.olift
      · cases eq₂ : (Shape.lift n₁ t).olift; · rfl
        rw [Shape.olift_thm (Nat.le_trans h2 h1), ← Shape.lift_lift (.inl h2)] at eq₂
        rw [(Shape.lift_inj h1).1 eq₂, (Shape.olift_thm h2).2 rfl] at eq₁; cases eq₁
      · rw [(Shape.olift_thm h2).1 eq₁, Shape.lift_lift (.inl h2),
          (Shape.olift_thm (Nat.le_trans h2 h1)).2 rfl]

theorem WShapeFun.lift_lift {s : WShapeFun n₁} (le : n₁ ≤ n₂ ∨ n₃ ≤ n₂) :
    (s.lift n₂).lift n₃ = s.lift n₃ := by
  ext1; simp [lift]
  by_cases h1 : n₁ ≤ n₂
  · congr 1; ext t; rw [ShapeFun.olift_eq_lift h1, Option.getD]
    obtain h2 | h2 := Nat.le_total n₂ n₃
    · rw [ShapeFun.olift_eq_lift h2, ShapeFun.lift_lift (.inl h1),
        ShapeFun.olift_eq_lift (Nat.le_trans h1 h2)]
    rw [ShapeFun.olift_thm h2]
    obtain h3 | h3 := Nat.le_total n₁ n₃
    · rw [ShapeFun.olift_eq_lift h3, Option.some_inj, ← ShapeFun.lift_lift (.inl h3),
        ShapeFun.lift_inj h2]
    · rw [ShapeFun.olift_thm h3, ← ShapeFun.lift_lift (.inl h3), ShapeFun.lift_inj h1]
  · have h2 := le.resolve_left h1; have h1 := Nat.le_of_not_ge h1
    cases eq : ShapeFun.olift (Shape.olift (m := n₂)) s.1 <;> simp
    · cases eq' : ShapeFun.olift (Shape.olift (m := n₃)) s.1 <;> simp
      rw [ShapeFun.olift_thm (Nat.le_trans h2 h1), ← ShapeFun.lift_lift (.inl h2),
        ← ShapeFun.olift_thm h1, eq] at eq'; cases eq'
    · rw [(ShapeFun.olift_thm h1).1 eq]; rename_i t
      cases eq₁ : ShapeFun.olift Shape.olift t
      · cases eq₂ : ShapeFun.olift Shape.olift (ShapeFun.lift (Shape.lift n₁) t); · rfl
        rw [ShapeFun.olift_thm (Nat.le_trans h2 h1), ← ShapeFun.lift_lift (.inl h2)] at eq₂
        rw [(ShapeFun.lift_inj h1).1 eq₂, (ShapeFun.olift_thm h2).2 rfl] at eq₁; cases eq₁
      · rw [(ShapeFun.olift_thm h2).1 eq₁, ShapeFun.lift_lift (.inl h2),
          (ShapeFun.olift_thm (Nat.le_trans h2 h1)).2 rfl]

theorem WShape.lift_le_lift {s t : WShape n} (le : n ≤ m) :
    s.lift m ≤ t.lift m ↔ s ≤ t := by
  show (s.lift m).1 ≤ (t.lift m).1 ↔ s.1 ≤ t.1
  rw [lift_val le, lift_val le]; exact Shape.lift_le_lift le

theorem WShapeFun.lift_le_lift {s t : WShapeFun n} (le : n ≤ m) :
    s.lift m ≤ t.lift m ↔ s ≤ t := by
  show (s.lift m).1.LE (t.lift m).1 ↔ s.1.LE t.1
  rw [lift_val le, lift_val le]; exact ShapeFun.lift_le_lift le

theorem WShapeFun.lift_mono {s t : WShapeFun n} (le : n ≤ m) (h : s ≤ t) : s.lift m ≤ t.lift m :=
  (lift_le_lift le).2 h

theorem WShapeFun.LE.def' {f f' : WShapeFun n} : f ≤ f' ↔
    ∀ x y : WShape n, (x, y) ∈ f → ∃ x' y' : WShape n, (x', y') ∈ f' ∧ x' ≤ x ∧ y ≤ y' := by
  simp [(· ≤ ·), ShapeFun.LE.def]
  constructor <;> intro H x y h1
  · have ⟨_, _, h2, h3⟩ := H _ _ h1
    exact ⟨⟨_, (f'.2.2 _ h2).1⟩, ⟨_, (f'.2.2 _ h2).2⟩, h2, h3⟩
  · have ⟨x', y', h2, h3⟩ := H ⟨_, (f.2.2 _ h1).1⟩ ⟨_, (f.2.2 _ h1).2⟩ h1
    exact ⟨_, _, h2, h3⟩

theorem WShape.lift_mono {s t : WShape n} (le : n ≤ m) : s ≤ t → s.lift m ≤ t.lift m :=
  (lift_le_lift le).2

theorem WShape.lift_le_bot {s : WShape n} (h : n ≤ m) : s.lift m ≤ .bot ↔ s = .bot := by
  rw [← WShape.lift_bot (n := n), WShape.lift_le_lift h]
  exact ⟨fun h => WShape.ext (Shape.le_bot.1 h), fun h => h ▸ Shape.LE.rfl⟩

theorem WShape.lift_eq_bot {s : WShape n} (h : n ≤ m) : s.lift m = .bot ↔ s = .bot := by
  exact ⟨fun h' => (lift_le_bot h).1 (h' ▸ Shape.LE.rfl), fun h' => h' ▸ lift_bot⟩

theorem WShape.le_bot {s : WShape n} : s ≤ .bot ↔ s = .bot :=
  Shape.le_bot.trans (Subtype.ext_iff (a1 := s) (a2 := WShape.bot)).symm

@[simp] theorem WShape.lift_forallE {s : WShape n} {f : WShapeFun n} (h : n ≤ m) :
    (WShape.forallE s f).lift (m+1) = .forallE (s.lift m) (f.lift m) := by
  ext; simp [lift_val (Nat.succ_le_succ h), Shape.lift, WShape.forallE,
    lift_val h, WShapeFun.lift_val h]

theorem WShapeFun.NonZero.lift_iff {n m} {x : WShapeFun n} (le : n ≤ m) :
    (x.lift m).NonZero ↔ NonZero (n := n) x := by
  simp [NonZero, lift_val le, ShapeFun.NonZero.lift_iff le]

theorem WShape.ListNonZero.lift_iff {n m} {x : List (WShape n)} (le : n ≤ m) :
    ListNonZero (x.map (lift m)) ↔ ListNonZero (n := n) x := by
  simp [ListNonZero.def, ← Shape.ListNonZero.lift_iff le]
  apply iff_of_eq; congr 2; ext x; simp [lift_val le]

@[simp] theorem WShape.lift_lam' {f : WShapeFun n} (le : n ≤ m) :
    (WShape.lam' f).lift (m+1) = .lam' (f.lift m) := by
  ext1; simp [lam']; split <;> simp [WShapeFun.lift_val le, WShapeFun.NonZero.lift_iff le,
    lift_val (Nat.succ_le_succ le), lam, Shape.lift, *]

theorem WShape.lift_lam {f : WShapeFun n} {hl} (h : n ≤ m) :
    (WShape.lam f hl).lift (m+1) = .lam (f.lift m) ((WShapeFun.NonZero.lift_iff h).2 hl) := by
  ext1; simp [WShape.lift_val (Nat.succ_le_succ h), lam, WShapeFun.lift_val h, Shape.lift]

theorem WShape.lift_eq_lam' {s : WShape (n+1)} (le : n ≤ m)
    {f : WShapeFun m} (eq : s.lift (m+1) = .lam' f) :
    s = .bot ∧ f ≤ .bot ∨ ∃ f' : WShapeFun n, s = .lam' f' ∧ f = f'.lift m := by
  obtain ⟨f, hf⟩ := f
  have eq := congrArg (·.1) eq; simp [lift_val (Nat.succ_le_succ le)] at eq
  unfold lam' at eq; split at eq <;> rename_i h <;>
    obtain ⟨⟨⟩, wf⟩ := s <;> simp [lam, Shape.lift] at eq <;> cases eq
  · refine .inr ⟨⟨_, wf.1⟩, ?_⟩; rw [lam', dif_pos (by exact (ShapeFun.NonZero.lift_iff le).1 h)]
    exact ⟨rfl, WShapeFun.ext (WShapeFun.lift_val le ▸ rfl)⟩
  · refine .inl ⟨rfl, WShapeFun.LE.def'.2 fun x y h => ?_⟩; rename_i hn
    refine ⟨_, _, WShapeFun.mem_bot.2 ⟨rfl, rfl⟩, Shape.bot_le, Decidable.by_contra (hn ⟨_, h, ·⟩)⟩

theorem WShape.lift_ctor {c : Name} {l : List (WShape n)} {hc} (le : n ≤ m) :
    (WShape.ctor c l hc).lift (m+1) =
    .ctor c (l.map (.lift m)) ((WShape.ListNonZero.lift_iff le).2 ∘ hc) := by
  ext1; simp [WShape.lift_val (Nat.succ_le_succ le), ctor, Shape.lift]
  congr 2; ext1 x; simp [lift_val le]

@[simp] theorem WShape.lift_ctor' {c : Name} {l : List (WShape n)} (le : n ≤ m) :
    (WShape.ctor' c l).lift (m+1) = .ctor' c (l.map (.lift m)) := by
  ext1; simp [ctor']; split <;> rename_i hc <;>
    [rw [dif_pos ((WShape.ListNonZero.lift_iff le).2 ∘ hc)];
     rw [dif_neg (mt ((WShape.ListNonZero.lift_iff le).1 ∘ ·) hc)]] <;>
    simp [lift_val (Nat.succ_le_succ le), ctor, Shape.lift]
  congr 2; ext1 x; simp [lift_val le]

@[simp] theorem WShape.lift_rigid {c : Name} {l : List (WShape n)} {t} (le : n ≤ m) :
    (WShape.rigid c ls l t).lift (m+1) = .rigid c ls (l.map (.lift m)) (ctsMap (.lift m) t) := by
  ext1; simp only [WShape.lift_val (Nat.succ_le_succ le), rigid, Shape.lift, ctsMap_ctsMap,
    List.map_map]
  congr 2
  · ext1 x; simp [lift_val le]
  · funext x; exact (lift_val le).symm

@[simp] theorem WShape.bot_le : WShape.bot ≤ (s : WShape n) := Shape.bot_le

protected theorem WShape.LE.rfl {s : WShape n} : s ≤ s := Shape.LE.rfl
protected theorem WShape.LE.trans {s t u : WShape n} : s ≤ t → t ≤ u → s ≤ u := Shape.LE.trans

theorem WShape.LE.forallE_decomp {s : WShape (n+1)} {a : WShape n} {f : WShapeFun n} :
    s ≤ .forallE a f → s = .bot ∨ ∃ a' f', s = .forallE a' f' := by
  simp [WShape.LE.def, Shape.LE.def, forallE]; obtain ⟨⟨⟩, _⟩ := s <;> simp
  · simp [bot, Shape.bot]
  · rename_i wf; intros; exact .inr ⟨⟨_, wf.1⟩, ⟨_, wf.2⟩, rfl⟩

@[simp] theorem WShape.forallE_le_forallE {a a' : WShape n} {f f' : WShapeFun n} :
    WShape.forallE a f ≤ .forallE a' f' ↔ a ≤ a' ∧ f ≤ f' := Shape.forallE_le_forallE

theorem WShape.le_forallE_iff {s : WShape (n+1)} {a' : WShape n} {f' : WShapeFun n} :
    s ≤ .forallE a' f' ↔ s = .bot ∨ ∃ a f, s = .forallE a f ∧ a ≤ a' ∧ f ≤ f' := by
  constructor
  · cases s using WShape.casesOn' with
    | bot => exact fun _ => .inl rfl
    | forallE a f => exact fun h => .inr ⟨a, f, rfl, forallE_le_forallE.1 h⟩
    | _ => simp only [sort, lam, ctor, rigid, forallE, LE.def, Shape.LE.def, false_implies]
  · rintro (rfl | ⟨a, f, rfl, h1, h2⟩)
    · exact bot_le
    · exact forallE_le_forallE.2 ⟨h1, h2⟩

theorem WShape.le_sort {s : WShape n} : s ≤ .sort r ↔ s = .bot ∨ s = .sort r :=
  Shape.le_sort.trans <| by simp [WShape.ext_iff, WShape.bot, WShape.sort]

theorem WShape.sort_le {s : WShape n} : .sort r ≤ s ↔ .sort r = s :=
  Shape.sort_le.trans <| by simp [WShape.ext_iff, WShape.sort]

theorem forall₂_val_iff {R : Shape n → Shape n → Prop} {l l' : List (WShape n)} :
    List.Forall₂ R (l.map (·.1)) (l'.map (·.1)) ↔ List.Forall₂ (fun a b => R a.1 b.1) l l' := by
  simp

theorem ctsRel_val_iff {R : Shape n → Shape n → Prop} {t t' : List (Name × WShape n)} :
    CtsRel R (ctsMap (·.1) t) (ctsMap (·.1) t') ↔ CtsRel (fun a b => R a.1 b.1) t t' := by
  rw [ctsRel_map_left, ctsRel_map_right]

@[simp] theorem WShape.rigid_le_rigid {l l' : List (WShape n)} {t t'} :
    WShape.rigid c ls l t ≤ .rigid c' ls' l' t' ↔
      c = c' ∧ ls = ls' ∧ l.Forall₂ (· ≤ ·) l' ∧ CtsRel (· ≤ ·) t t' := by
  simp only [LE.def, rigid, Shape.rigid_le_rigid]
  rw [forall₂_val_iff, ctsRel_val_iff]

theorem WShape.rigid_le {s : WShape (n+1)} {l : List (WShape n)} {t} :
    WShape.rigid c ls l t ≤ s ↔
      ∃ l' t', s = .rigid c ls l' t' ∧ l.Forall₂ (· ≤ ·) l' ∧ CtsRel (· ≤ ·) t t' := by
  constructor
  · cases s using WShape.casesOn' with
    | rigid c' ls' l' t' =>
      rw [rigid_le_rigid]; rintro ⟨rfl, rfl, h1, h2⟩; exact ⟨_, _, rfl, h1, h2⟩
    | _ => simp only [sort, lam, ctor, rigid, forallE, bot, Shape.bot, LE.def, Shape.LE.def,
        false_implies]
  · rintro ⟨l', t', rfl, h1, h2⟩; exact rigid_le_rigid.2 ⟨rfl, rfl, h1, h2⟩

theorem WShape.le_rigid {s : WShape (n+1)} {l : List (WShape n)} {t} :
    s ≤ .rigid c ls l t ↔ s = .bot ∨
      ∃ l' t', s = .rigid c ls l' t' ∧ l'.Forall₂ (· ≤ ·) l ∧ CtsRel (· ≤ ·) t' t := by
  constructor
  · cases s using WShape.casesOn' with
    | bot => exact fun _ => .inl rfl
    | rigid c' ls' l' t' =>
      rw [rigid_le_rigid]; rintro ⟨rfl, rfl, h1, h2⟩; exact .inr ⟨_, _, rfl, h1, h2⟩
    | _ => simp only [sort, lam, ctor, rigid, forallE, LE.def, Shape.LE.def, false_implies]
  · rintro (rfl | ⟨l', t', rfl, h1, h2⟩)
    · exact bot_le
    · exact rigid_le_rigid.2 ⟨rfl, rfl, h1, h2⟩

theorem WShape.forallE_le {s : WShape (n+1)} {a : WShape n} {f : WShapeFun n} :
    WShape.forallE a f ≤ s ↔
      ∃ a' : WShape n, ∃ f' : WShapeFun n, a ≤ a' ∧ f ≤ f' ∧ s = .forallE a' f' := by
  constructor
  · intro h
    have ⟨a', b', h1, h2, h3⟩ := Shape.forallE_le.1 h
    have wf := h3 ▸ s.2
    exact ⟨⟨a', wf.1⟩, ⟨b', wf.2⟩, h1, h2, WShape.ext h3.symm⟩
  · intro ⟨a', f', h1, h2, h3⟩; subst h3; exact WShape.forallE_le_forallE.2 ⟨h1, h2⟩

theorem WShape.lam_le_lam {f f' : WShapeFun n} {hf hf'} :
    WShape.lam f hf ≤ .lam f' hf' ↔ f ≤ f' := .rfl

theorem WShape.lam'_le_lam' {f f' : WShapeFun n} :
    WShape.lam' f ≤ .lam' f' ↔ f ≤ f' := by
  simp [WShape.LE.def, lam', WShapeFun.LE.def]
  split <;> [split <;> rename_i h h'; rename_i h] <;> simp [lam, bot, Shape.LE.def, ShapeFun.LE.def]
  · let ⟨_, h1, h2⟩ := h
    refine ⟨_, _, h1, fun _ _ h3 h4 h5 => h' ⟨_, h3, mt h5.trans h2⟩⟩
  · intro _ y h1; have h2 := Decidable.by_contra (mt (⟨_, h1, ·⟩) h)
    have ⟨_, h⟩ := f'.2.1.1; exact ⟨_, _, h, Shape.bot_le, .trans h2 Shape.bot_le⟩

theorem WShape.LE.le_lam {s : WShape (n+1)} {f : WShapeFun n} {hl} :
    s ≤ .lam f hl → s = .bot ∨ ∃ f' hl', s = .lam f' hl' := by
  simp [WShape.LE.def, Shape.LE.def, lam]; obtain ⟨⟨⟩, _⟩ := s <;> simp
  · simp [bot, Shape.bot]
  · rename_i wf; intros; exact .inr ⟨⟨_, wf.1⟩, wf.2, rfl⟩

theorem WShape.LE.lam_le {s : WShape (n+1)} {f : WShapeFun n} {hl} :
    .lam f hl ≤ s → ∃ f' hl', s = .lam f' hl' := by
  simp [WShape.LE.def, Shape.LE.def, lam]; obtain ⟨⟨⟩, _⟩ := s <;> simp
  rename_i wf; intros; exact ⟨⟨_, wf.1⟩, wf.2, rfl⟩

theorem WShape.LE.le_lam' {s : WShape (n+1)} {f : WShapeFun n} :
    s ≤ .lam' f → ∃ f', s = .lam' f' := by
  rw [lam']; split
  · intro h; obtain rfl | ⟨_, h, rfl⟩ := h.le_lam
    · exact ⟨.bot, by simp⟩
    · exact ⟨_, lam_eq_lam'⟩
  · simp [le_bot]; rintro rfl; exact ⟨.bot, by simp⟩

theorem WShape.lam.inj {f f' : WShapeFun n} {h h'} :
    WShape.lam f h = WShape.lam f' h' ↔ f = f' := by
  simp [WShape.ext_iff, WShapeFun.ext_iff, lam]
  exact iff_of_eq (ShapeS.lam.injEq ..)

theorem WShape.ctor.inj {f f' : List (WShape n)} {h h'} :
    WShape.ctor c f h = WShape.ctor c' f' h' ↔ c = c' ∧ f = f' := by
  simp [WShape.ext_iff, ctor]
  refine iff_of_eq (ShapeS.ctor.injEq ..) |>.trans ?_
  exact and_congr_right' <| List.map_inj_right fun _ _ => Subtype.ext

theorem WShapeFun.bot_mem (f : WShapeFun n) : ∃ y, (.bot, y) ∈ f :=
  let ⟨_, h⟩ := f.2.1.1; ⟨_, f.mem_val h⟩

@[simp] theorem WShapeFun.bot_le {f : WShapeFun n} : bot ≤ f := by
  simp [LE.def', mem_bot, WShape.le_bot, and_left_comm, WShape.bot_le, f.bot_mem]

def WShape.Compat (a b : WShape n) : Prop := a.1.Compat b.1
def WShapeFun.Compat (a b : WShapeFun n) : Prop := ShapeFun.Compat Shape.Compat a.1 b.1
instance : Decidable (WShape.Compat a b) := inferInstanceAs (Decidable (_ = true))
instance : Decidable (WShapeFun.Compat a b) := inferInstanceAs (Decidable (_ = true))

@[simp] theorem WShape.Compat.bot_l {n} {s : WShape n} : bot.Compat s := Shape.Compat.bot_l
@[simp] theorem WShape.Compat.bot_r {n} {s : WShape n} : s.Compat bot := Shape.Compat.bot_r
@[simp] theorem WShape.Compat.sort_sort : Compat (sort r : WShape n) (sort r') ↔ r = r' :=
  Shape.Compat.sort_sort

@[simp] theorem WShape.Compat.forallE_forallE {a a' : WShape n} {f f' : WShapeFun n} :
    (WShape.forallE a f).Compat (.forallE a' f') ↔ a.Compat a' ∧ WShapeFun.Compat f f' :=
  Shape.Compat.forallE_forallE

@[simp] theorem WShape.Compat.lam_lam {f f' : WShapeFun n} {hf hf'} :
    (WShape.lam f hf).Compat (.lam f' hf') ↔ WShapeFun.Compat f f' := Shape.Compat.lam_lam

@[simp] theorem WShape.Compat.ctor_ctor {l l' : List (WShape n)} {hl hl'} :
    (WShape.ctor c l hl).Compat (.ctor c' l' hl') ↔ c = c' ∧ l.Forall₂ Compat l' := by
  simp [WShape.Compat, ctor, Shape.Compat.ctor_ctor]; intro; rfl

@[simp] theorem WShape.Compat.rigid_rigid {l l' : List (WShape n)} {t t'} :
    (WShape.rigid c ls l t).Compat (.rigid c' ls' l' t') ↔
      c = c' ∧ ls = ls' ∧ l.Forall₂ Compat l' ∧ CtsRel Compat t t' := by
  simp only [WShape.Compat, rigid, Shape.Compat.rigid_rigid]
  rw [forall₂_val_iff, ctsRel_val_iff]; rfl

theorem WShape.Compat.lam'_lam' {f f' : WShapeFun n} (H : f.Compat f') :
    (WShape.lam' f).Compat (.lam' f') := by
  unfold lam'; split <;> [split <;> [exact lam_lam.2 H; exact .bot_r]; exact .bot_l]

theorem WShape.Compat.ctor'_ctor' {l l' : List (WShape n)}
    (H : l.Forall₂ Compat l') : (WShape.ctor' c l).Compat (.ctor' c l') := by
  unfold ctor'; split <;> [split <;> [exact ctor_ctor.2 ⟨rfl, H⟩; exact .bot_r]; exact .bot_l]

theorem WShapeFun.Compat.def {n} {f f' : WShapeFun n} :
    f.Compat f' ↔ ∀ x ∈ f, ∀ y ∈ f', x.1.Compat y.1 → x.2.Compat y.2 := by
  simp [Compat, ShapeFun.Compat.def]
  constructor <;> intro H _ _ h1 _ _ h2
  · exact H _ _ h1 _ _ h2
  · exact H _ _ (f.mem_val h1) _ _ (f'.mem_val h2)

theorem WShapeFun.join_mem' {f : WShapeFun n}
    (hx : (x, y) ∈ f) (hy : (x', y') ∈ f) (hc : x.Compat x') :
    ∃ z, z ∈ f ∧ x.1.join x'.1 ≤ z.1.1 ∧ z.1.1 ≤ x.1.join x'.1 := by
  let ⟨_, h1, h2⟩ := (f.2.1.2 _ (f.mem_val hx) _ (f.mem_val hy)).1 hc
  exact ⟨_, f.mem_val h1, h2⟩

theorem WShapeFun.mem_mono {f : WShapeFun n}
    (hx : (x, y) ∈ f) (hy : (x', y') ∈ f) : x ≤ x' → y ≤ y' :=
  (f.2.1.2 _ (f.mem_val hx) _ (f.mem_val hy)).2

protected theorem WShape.Compat.lift {x y : WShape n} (le : n ≤ m) :
    (x.lift m).Compat (y.lift m) ↔ x.Compat y := by
  simp [WShape.Compat, lift_val le, Shape.Compat.lift le]

omit [ShapeParams] in
theorem ShapeFun.mem_trunc {f : ShapeFun n} : x ∈ f.trunc a ↔ x ∈ f ∧ x.1 ≤ a := by simp [trunc]
namespace WShape.join_prop
variable (ih : ∀ {x y : WShape n}, (∀ z, x ≤ z → y ≤ z → x.Compat y) ∧
  (x.Compat y → (x.1.join y.1).WF ∧ ∀ z, x.1.join y.1 ≤ z.1 ↔ x ≤ z ∧ y ≤ z))
include ih

theorem exists_max {f : WShapeFun n}
    (hc : ∀ x ∈ f, ∀ y ∈ f, x.1.Compat y.1) : ∃ x ∈ f.1, ∀ x' ∈ f.1, x'.1 ≤ x.1 := by
  suffices ∀ l : ShapeFun n, (∀ x ∈ l, x ∈ f.1) → ∃ x ∈ f.1, ∀ x' ∈ l, x'.1 ≤ x.1 from
    have ⟨_, h1, h2⟩ := this _ fun _ => id; ⟨_, f.mem_val h1, fun _ => h2 _⟩
  intro l hl; induction l with
  | nil => let ⟨_, h⟩ := f.2.1.1; exact ⟨_, h, nofun⟩
  | cons a l ihl =>
    have ⟨hm, hl⟩ := List.forall_mem_cons.1 hl
    have ⟨x, h1, h2⟩ := ihl hl
    have := hc _ (f.mem_val hm) _ (f.mem_val h1)
    have ⟨_, a1, a2⟩ := f.join_mem' (f.mem_val hm) (f.mem_val h1) this
    have ⟨b1, b2⟩ := ((ih.2 this).2 ⟨_, (f.2.2 _ a1).1⟩).1 a2.1
    exact ⟨_, a1, List.forall_mem_cons.2 ⟨b1, fun _ h => (h2 _ h).trans b2⟩⟩

def wf_trunc (f : WShapeFun n) (a : WShape n) : WShapeFun n := by
  refine ⟨f.1.trunc a.1, ?_, fun _ h1 => f.2.2 _ (ShapeFun.mem_trunc.1 h1).1⟩
  simp [ShapeFun.trunc]
  refine ⟨f.2.1.1, fun _ _ h1 h2 _ _ h3 h4 => ?_⟩
  have ⟨a1, a2, h1⟩ := f.mem_val' h1; have ⟨b1, b2, h3⟩ := f.mem_val' h3
  have ⟨a3, a4⟩ := f.2.1.2 _ h1 _ h3; refine ⟨fun h => ?_, a4⟩
  have ⟨⟨z, z'⟩, a5, a6⟩ := a3 h
  refine ⟨_, ⟨⟨_, a5⟩, a6.2.trans ?_⟩, a6⟩
  exact (ih.2 <| (@ih ⟨_, a1⟩ ⟨_, b1⟩).1 _ h2 h4).2 _ |>.2 ⟨h2, h4⟩

theorem trunc_compat (f : WShapeFun n) (a : WShape n)
    {{x}} (h1 : x ∈ wf_trunc ih f a) {{y}} (h2 : y ∈ wf_trunc ih f a) : x.1.Compat y.1 :=
  have ⟨a1, a2⟩ := ShapeFun.mem_trunc.1 h1
  have ⟨b1, b2⟩ := ShapeFun.mem_trunc.1 h2
  (@ih ⟨_, (f.2.2 _ a1).1⟩ ⟨_, (f.2.2 _ b1).1⟩).1 a a2 b2

theorem app_core (f : WShapeFun n) (x : WShape n) :
    ∃ x', x' ≤ x.1 ∧ (x', f.1.app x.1) ∈ f.1 ∧ ∀ y ∈ f.1, y.1 ≤ x.1 → y.2 ≤ f.1.app x.1 := by
  simp only [ShapeFun.app, ShapeFun.maxBelow]
  have ⟨_, h1, h2⟩ := exists_max ih (trunc_compat ih f x)
  simp [wf_trunc, ShapeFun.mem_trunc] at h1 h2
  show let P := _; ∃ x', x' ≤ x.1 ∧ let y' := ((List.find? P _).getD (Shape.bot, Shape.bot)).snd
    (x', y') ∈ f.1 ∧ ∀ y ∈ f.1, y.1 ≤ x.1 → y.2 ≤ y'
  intro P
  have ⟨⟨x', y'⟩, h⟩ := Option.isSome_iff_exists.1 <|
    (List.find?_isSome (p := P)).2 ⟨_, ShapeFun.mem_trunc.2 h1, by simpa [P, ShapeFun.mem_trunc]⟩
  have := List.find?_some h; simp [P, ShapeFun.mem_trunc, h] at this ⊢
  have ⟨h1, h2⟩ := ShapeFun.mem_trunc.1 <| List.mem_of_find?_eq_some h
  exact ⟨_, h2, h1, fun _ _ a1 a2 => (f.2.1.2 _ a1 _ h1).2 (this _ _ a1 a2)⟩

theorem of_compat {x x' : WShape n} (hc : x.Compat x') :
    ∃ j : WShape n, j.1 = x.1.join x'.1 ∧ ∀ w, j ≤ w ↔ x ≤ w ∧ x' ≤ w :=
  ⟨⟨_, (ih.2 hc).1⟩, rfl, (ih.2 hc).2⟩

theorem join_mem' {f : WShapeFun n} {x y x' y'}
    (hx : (x, y) ∈ f) (hy : (x', y') ∈ f) (hc : x.Compat x') :
    ∃ j : WShape n, j.1 = x.1.join x'.1 ∧ ∃ z, z ∈ f ∧ j ≤ z.1 ∧ z.1 ≤ j ∧
      ∀ w, j ≤ w ↔ x ≤ w ∧ x' ≤ w :=
  let ⟨_, a1, a2, a3⟩ := f.join_mem' hx hy hc
  ⟨⟨_, (ih.2 hc).1⟩, rfl, _, a1, a2, a3, (ih.2 hc).2⟩

theorem compat_app_r {f : WShapeFun n} {x x' : WShape n} (hc : x.Compat x') :
    (f.1.app x.1).Compat (f.1.app x'.1) :=
  have ⟨_, a1, a2, _⟩ := app_core ih f x; have a2 := f.mem_val a2
  have ⟨_, b1, b2, _⟩ := app_core ih f x'; have b2 := f.mem_val b2
  have ⟨_, _, _, c2, c3, _, c5⟩ := join_mem' ih a2 b2 (Shape.Compat.mono a1 b1 hc)
  have ⟨c6, c7⟩ := (c5 _).1 .rfl
  ih.1 _ (f.mem_mono a2 c2 (c6.trans c3)) (f.mem_mono b2 c2 (c7.trans c3))

theorem compat_app_l {f f' : WShapeFun n} (hc : f.Compat f') (x : WShape n) :
    (f.1.app x.1).Compat (f'.1.app x.1) := by
  have ⟨_, a1, a2, _⟩ := app_core ih f x; have ⟨a4, a5, a2⟩ := f.mem_val' a2
  have ⟨_, b1, b2, _⟩ := app_core ih f' x; have ⟨b4, b5, b2⟩ := f'.mem_val' b2
  exact (ShapeFun.Compat.def.1 hc _ a2 _ b2 ((@ih ⟨_, a4⟩ ⟨_, b4⟩).1 _ a1 b1) :)

theorem ih_fun {f f' : WShapeFun n} :
    (∀ z, f ≤ z → f' ≤ z → f.Compat f') ∧
    (f.Compat f' → ∃ h, ∀ z, ⟨ShapeFun.join Shape.join f.1 f'.1, h⟩ ≤ z ↔ f ≤ z ∧ f' ≤ z) := by
  simp only [WShapeFun.LE.def']
  refine ⟨fun z le₁ le₂ => ShapeFun.Compat.def.2 fun _ h1 _ h2 h => ?_, fun hc => ?_⟩
  · have ⟨_, _, a1, a2, a3⟩ := le₁ _ _ (f.mem_val h1)
    have ⟨_, _, b1, b2, b3⟩ := le₂ _ _ (f'.mem_val h2)
    have h := Shape.Compat.mono a2 b2 h
    refine Shape.Compat.mono a3 b3 ?_
    have ⟨_, c1, c2, c3⟩ := z.join_mem' a1 b1 h
    have ⟨e1, e2⟩ := ((ih.2 h).2 _).1 c2
    exact ih.1 _ (z.mem_mono a1 c1 e1) (z.mem_mono b1 c1 e2)
  simp only [ShapeFun.WF, ShapeFun.mem_join]
  refine ⟨⟨⟨?_, ?_⟩, fun a => ?_⟩, ?_⟩
  · let ⟨_, a1⟩ := f.bot_mem; let ⟨_, a2⟩ := f'.bot_mem
    refine ⟨_, _, a1, _, a2, Compat.bot_l, cast (Prod.mk.injEq ..).symm ⟨.symm ?_, rfl⟩⟩
    exact Shape.le_bot.1 <| ((ih.2 .bot_l).2 _).2 ⟨.rfl, .rfl⟩
  · rintro _ ⟨x, a1, x', a2, a3, rfl⟩ _ ⟨y, b1, y', b2, b3, rfl⟩
    replace a1 := f.mem_val a1; replace a2 := f'.mem_val a2
    replace b1 := f.mem_val b1; replace b2 := f'.mem_val b2
    change Compat ⟨x.1, (f.2.2 _ a1).1⟩ ⟨x'.1, (f'.2.2 _ a2).1⟩ at a3
    change Compat ⟨y.1, (f.2.2 _ b1).1⟩ ⟨y'.1, (f'.2.2 _ b2).1⟩ at b3
    dsimp only
    have ⟨a, a5, a6⟩ := of_compat ih a3; have ⟨a31, a32⟩ := (a6 _).1 .rfl; have ac := ih.1 _ a31 a32
    have ⟨b, b5, b6⟩ := of_compat ih b3; have ⟨b31, b32⟩ := (b6 _).1 .rfl; have bc := ih.1 _ b31 b32
    refine ⟨fun h1 => ?_, fun h1 => a5 ▸ b5 ▸ ?_⟩
    · have h1' : a.Compat b := by simp [Compat, a5, b5, h1]
      have ⟨c, c1, c2⟩ := of_compat ih h1'; have ⟨c3, c4⟩ := (c2 _).1 .rfl
      have dc := ih.1 _ (a31.trans c3) (b31.trans c4)
      have ⟨d, d1, d', d2, d3, d4, d5⟩ := join_mem' ih a1 b1 dc; have ⟨d6, d7⟩ := (d5 _).1 .rfl
      have ec := ih.1 _ (a32.trans c3) (b32.trans c4)
      have ⟨e, e1, e', e2, e3, e4, e5⟩ := join_mem' ih a2 b2 ec; have ⟨e6, e7⟩ := (e5 _).1 .rfl
      have h4 := d4.trans <| (d5 _).2 ⟨a31.trans c3, b31.trans c4⟩
      have h5 := e4.trans <| (e5 _).2 ⟨a32.trans c3, b32.trans c4⟩
      have hc := ih.1 _ h4 h5
      have ⟨j, j1, j2⟩ := of_compat ih hc; have ⟨j3, j4⟩ := (j2 _).1 .rfl
      refine ⟨_, ⟨_, d2, _, e2, hc, rfl⟩, j1 ▸ a5 ▸ b5 ▸ c1 ▸ ?_⟩; dsimp only
      refine ⟨(c2 _).2 ⟨?_, ?_⟩, (j2 _).2 ⟨h4, h5⟩⟩
      · exact (a6 _).2 ⟨d6.trans (d3.trans j3), e6.trans (e3.trans j4)⟩
      · exact (b6 _).2 ⟨d7.trans (d3.trans j3), e7.trans (e3.trans j4)⟩
    · have ⟨_, c1, c2, _⟩ := app_core ih f a; have ⟨c3, c4, c2⟩ := f.mem_val' c2
      have ⟨_, d1, d2, _⟩ := app_core ih f' a; have ⟨d3, d4, d2⟩ := f'.mem_val' d2
      have ⟨_, f1, f2, cf⟩ := app_core ih f b; have ⟨f3, f4, f2⟩ := f.mem_val' f2
      have ⟨_, g1, g2, dg⟩ := app_core ih f' b; have ⟨g3, g4, g2⟩ := f'.mem_val' g2
      have ⟨e, e1, e2⟩ := of_compat ih (x := ⟨_, c4⟩) (x' := ⟨_, d4⟩) (compat_app_l ih hc a)
      have ⟨k, k1, k2⟩ := of_compat ih (x := ⟨_, f4⟩) (x' := ⟨_, g4⟩) (compat_app_l ih hc b)
      refine e1 ▸ k1 ▸ (e2 _).2 ⟨?_, ?_⟩
      · exact (cf _ c2 (c1.trans (a5 ▸ b5 ▸ h1))).trans ((k2 _).1 .rfl).1
      · exact (dg _ d2 (d1.trans (a5 ▸ b5 ▸ h1))).trans ((k2 _).1 .rfl).2
  · rintro ⟨b, b3, c, c3, a1, rfl⟩
    have ⟨b1, b2, b3⟩ := f.mem_val' b3; have ⟨c1, c2, c3⟩ := f'.mem_val' c3
    have ⟨d, d1, d2⟩ := of_compat ih (x := ⟨_, b1⟩) (x' := ⟨_, c1⟩) a1
    have ⟨_, f1, f2, cf⟩ := app_core ih f d; have ⟨f3, f4, f2⟩ := f.mem_val' f2
    have ⟨_, g1, g2, dg⟩ := app_core ih f' d; have ⟨g3, g4, g2⟩ := f'.mem_val' g2
    have ⟨e, e1, e2⟩ := of_compat ih (x := ⟨_, f4⟩) (x' := ⟨_, g4⟩) (compat_app_l ih hc d)
    refine d1 ▸ e1 ▸ ⟨d.2, e.2⟩
  · intro f₃; conv =>
      enter [1,x,y,1]; (conv => apply propext WShapeFun.mem_def); simp only [ShapeFun.mem_join]
    refine ⟨fun H => ?_, fun ⟨H1, H2⟩ => ?_⟩
    · refine ⟨fun x y hf => ?_, fun x y hf' => ?_⟩
      · have ⟨_, hf'⟩ := f'.bot_mem
        have ⟨_, f1, f2, cf⟩ := app_core ih f x; have ⟨f3, f4, f2⟩ := f.mem_val' f2
        have ⟨_, g1, g2, dg⟩ := app_core ih f' x; have ⟨g3, g4, g2⟩ := f'.mem_val' g2
        have ⟨e, e1, e2⟩ := of_compat ih (x := ⟨_, f4⟩) (x' := ⟨_, g4⟩) (compat_app_l ih hc x)
        have ⟨c₁, c₂, c1, c2, c3⟩ := H ⟨_, Shape.join_bot ▸ x.2⟩ ⟨_, Shape.join_bot ▸ e1 ▸ e.2⟩
          ⟨_, hf, _, hf', Compat.bot_r, rfl⟩
        simp only [bot, Shape.join_bot] at c2 c3
        exact ⟨_, _, c1, c2, .trans ((cf _ hf .rfl).trans (e1 ▸ (show _ ≤ e.1 from ((e2 _).1 .rfl).1) :)) c3⟩
      · have ⟨_, hf⟩ := f.bot_mem
        have ⟨_, f1, f2, cf⟩ := app_core ih f x; have ⟨f3, f4, f2⟩ := f.mem_val' f2
        have ⟨_, g1, g2, dg⟩ := app_core ih f' x; have ⟨g3, g4, g2⟩ := f'.mem_val' g2
        have ⟨e, e1, e2⟩ := of_compat ih (x := ⟨_, f4⟩) (x' := ⟨_, g4⟩) (compat_app_l ih hc x)
        have ⟨c₁, c₂, c1, c2, c3⟩ := H ⟨_, Shape.bot_join ▸ x.2⟩ ⟨_, Shape.bot_join ▸ e1 ▸ e.2⟩
          ⟨_, hf, _, hf', Compat.bot_l, rfl⟩
        simp only [bot, Shape.bot_join] at c2 c3
        exact ⟨_, _, c1, c2, .trans ((dg _ hf' .rfl).trans (e1 ▸ (show _ ≤ e.1 from ((e2 _).1 .rfl).2) :)) c3⟩
    · rintro ⟨_, hx⟩ ⟨_, hy⟩ ⟨x, a3, y, b3, xy, ⟨⟩⟩
      have ⟨a1, a2, a3⟩ := f.mem_val' a3; have ⟨b1, b2, b3⟩ := f'.mem_val' b3
      have ⟨e, e1, e2⟩ := of_compat ih (x := ⟨_, a1⟩) (x' := ⟨_, b1⟩) xy
      have ⟨f₁, f1, f2, cf⟩ := app_core ih f e; have ⟨f3, f4, f2⟩ := f.mem_val' f2
      have ⟨g₁, g1, g2, dg⟩ := app_core ih f' e; have ⟨g3, g4, g2⟩ := f'.mem_val' g2
      have ⟨i, i1, i2, hi⟩ := app_core ih f₃ e; have ⟨i3, i4, i2⟩ := f₃.mem_val' i2
      have ⟨j, j1, j2⟩ := of_compat ih (x := ⟨_, f4⟩) (x' := ⟨_, g4⟩) (compat_app_l ih hc e)
      have ⟨l1, l2⟩ := (e2 _).1 .rfl
      refine ⟨_, _, i2, (e1 ▸ i1 :), ?_⟩
      simp only [WShape.LE.def, ← e1, ← j1]
      refine (j2 ⟨_, i4⟩).2 ⟨?_, ?_⟩
      · have ⟨m, m', m1, m2, m3⟩ := H1 _ _ f2; exact m3.trans (hi _ m1 (m2.trans f1))
      · have ⟨m, m', m1, m2, m3⟩ := H2 _ _ g2; exact m3.trans (hi _ m1 (m2.trans g1))

end WShape.join_prop

theorem WShape.join_prop {x y : WShape n} :
    (∀ z, x ≤ z → y ≤ z → x.Compat y) ∧
    (x.Compat y → (x.1.join y.1).WF ∧ ∀ z, x.1.join y.1 ≤ z.1 ↔ x ≤ z ∧ y ≤ z) := by
  induction n with
  | zero =>
    obtain ⟨⟨⟩, wf⟩ := x <;> obtain ⟨⟨⟩, _⟩ := y <;>
      simp +contextual [(·≤·), Compat, Shape.LE, Shape.ble, Shape.Compat, Shape.join, *]
    refine ⟨?_, (· ▸ ⟨wf, ?_⟩)⟩ <;> rintro ⟨⟨⟩⟩ <;> simp [Shape.ble]
    exact (·.trans ·.symm)
  | succ n ih
  have go {f f' : ShapeFun n} (wf : ShapeFun.WF Shape.WF f) (wf' : ShapeFun.WF Shape.WF f') :=
    @join_prop.ih_fun _ _ @ih ⟨f, wf⟩ ⟨f', wf'⟩
  let ⟨x, wf⟩ := x; let ⟨y, wf'⟩ := y
  simp only [WShape.LE.def]; simp [WShape, Compat]
  constructor
  · (cases x with | bot => exact fun _ _ _ _ => Shape.Compat.bot_l | _) <;>
    rintro ⟨⟩ wf₃ h2 h3 <;> simp [Shape.LE.def] at h2 <;>
    (cases y with | bot => exact Shape.Compat.bot_r | _) <;>
    simp [Shape.LE.def, Shape.Compat] at h3 ⊢ <;> dsimp [Shape.WF] at wf wf' wf₃
    · exact h2.trans h3.symm
    · exact ⟨(@ih ⟨_, wf.1⟩ ⟨_, wf'.1⟩).1 ⟨_, wf₃.1⟩ h2.1 h3.1,
        (go wf.2 wf'.2).1 ⟨_, wf₃.2⟩ h2.2 h3.2⟩
    · exact (go wf.1 wf'.1).1 ⟨_, wf₃.1⟩ h2 h3
    · refine ⟨h2.1.trans h3.1.symm, h2.2.and_mem.trans ?_ h3.2.and_mem.flip⟩
      rintro _ _ _ ⟨h1, h2, h3⟩ ⟨h4, h5, _⟩
      exact (@ih ⟨_, wf.1 _ h2⟩ ⟨_, wf'.1 _ h5⟩).1 ⟨_, wf₃.1 _ h3⟩ h1 h4
    · obtain ⟨rfl, rfl, h2a, h2b⟩ := h2; obtain ⟨rfl, rfl, h3a, h3b⟩ := h3
      have H x y z (a1 : Shape.WF x) (a2 : Shape.WF y) (a3 : Shape.WF z)
          (b1 : x ≤ z) (b2 : y ≤ z) : x.Compat y := (@ih ⟨x, a1⟩ ⟨y, a2⟩).1 ⟨z, a3⟩ b1 b2
      exact ⟨⟨⟨rfl, rfl⟩, forall₂_compat_of_le H wf.1 wf'.1 wf₃.1 h2a h3a⟩,
        ctsRel_compat_of_le H wf.2 wf'.2 wf₃.2 h2b h3b⟩
  · (cases x with | bot => intro; exact ⟨wf', fun _ _ => (and_iff_right Shape.bot_le).symm⟩ | _) <;>
    (cases y with | bot => intro; exact ⟨wf, fun _ _ => (and_iff_left Shape.bot_le).symm⟩ | _) <;>
    simp [Shape.WF] at wf wf' <;>
    simp +contextual [Shape.Compat, Shape.join, Shape.sort, Shape.LE.def, Shape.WF]
    · intro h1 h2
      have ⟨a1, a2⟩ := (@ih ⟨_, wf.1⟩ ⟨_, wf'.1⟩).2 h1
      have ⟨b1, b2⟩ := (go wf.2 wf'.2).2 h2
      simp only [WShape.LE.def, WShapeFun.LE.def] at a1 a2 b1 b2
      simp [WShape, WShapeFun] at a2 b2 ⊢
      refine ⟨⟨a1, b1⟩, ?_⟩
      rintro ⟨⟨⟩⟩ <;> simp +contextual [Shape.WF, and_assoc, and_left_comm, *]
    · intro h1
      have ⟨a1, a2⟩ := (go wf.1 wf'.1).2 h1
      simp only [WShapeFun.LE.def] at a1 a2; simp [WShapeFun] at a2
      exact ⟨⟨a1, wf.2.mono ((a2 _ a1).1 .rfl).1⟩, by rintro ⟨⟩ <;> simp +contextual [Shape.WF, *]⟩
    · rintro rfl H; constructor
      · have := H.and_mem.zipWith_l (f := Shape.join) (S := fun x y => x ≤ y ∧ y.WF)
          fun _ _ ⟨h1, h2⟩ =>
            have ⟨a1, a2⟩ := (@ih ⟨_, wf.1 _ h2.1⟩ ⟨_, wf'.1 _ h2.2⟩).2 h1
            ⟨((a2 ⟨_, a1⟩).1 .rfl).1, a1⟩
        refine ⟨fun _ h => ?_, fun hs => (wf.2 hs).mono <| this.imp fun _ _ => And.left⟩
        have ⟨_, h⟩ := this.forall_exists_r _ h; exact h.2.2
      · rintro ⟨⟩ <;> simp +contextual [Shape.WF, and_left_comm]; rintro wf₃ - -
        rename_i l l' _ l₃
        replace wf := wf.1; replace wf' := wf'.1
        induction l₃ generalizing l l' with cases H <;> simp | cons a₃ l₃ ihl
        have ⟨wf₁, wf₂⟩ := List.forall_mem_cons.1 wf
        have ⟨wf₁', wf₂'⟩ := List.forall_mem_cons.1 wf'
        have ⟨wf₁₃, wf₂₃⟩ := List.forall_mem_cons.1 wf₃
        rename_i h₃ H₃
        refine and_congr (((@ih ⟨_, wf₁⟩ ⟨_, wf₁'⟩).2 h₃).2 ⟨_, wf₁₃⟩)
          (ihl _ _ H₃ wf₂₃ wf₂ wf₂') |>.trans ?_
        simp [(· ≤ ·), and_comm, and_assoc, and_left_comm]
    · rintro rfl rfl hl ht
      have H x y (a1 : Shape.WF x) (a2 : Shape.WF y) (hc : x.Compat y) :
          (x.join y).WF ∧ ∀ z, Shape.WF z → (x.join y ≤ z ↔ x ≤ z ∧ y ≤ z) :=
        ⟨((@ih ⟨x, a1⟩ ⟨y, a2⟩).2 hc).1, fun z a3 => ((@ih ⟨x, a1⟩ ⟨y, a2⟩).2 hc).2 ⟨z, a3⟩⟩
      have ⟨j1, j2⟩ := forall₂_join H wf.1 wf'.1 hl
      have ⟨k1, k2⟩ := ctsRel_join H (fun p h => wf.2 _ _ h) (fun p h => wf'.2 _ _ h) ht
      refine ⟨⟨j1, fun a b h => k1 _ h⟩, fun z wf₃ => ?_⟩
      cases z with
      | rigid c₃ ls₃ l₃ t₃ =>
        dsimp only
        constructor
        · rintro ⟨rfl, rfl, h1, h2⟩
          have ⟨a1, a2⟩ := (j2 _ wf₃.1).1 h1; have ⟨b1, b2⟩ := (k2 _ wf₃.2).1 h2
          exact ⟨⟨rfl, rfl, a1, b1⟩, ⟨rfl, rfl, a2, b2⟩⟩
        · rintro ⟨⟨rfl, rfl, a1, b1⟩, ⟨-, -, a2, b2⟩⟩
          exact ⟨rfl, rfl, (j2 _ wf₃.1).2 ⟨a1, a2⟩, (k2 _ wf₃.2).2 ⟨b1, b2⟩⟩
      | _ => simp

theorem WShape.Compat.iff {x y : WShape n} : x.Compat y ↔ ∃ z, x ≤ z ∧ y ≤ z := by
  refine ⟨fun h => ?_, fun ⟨_, h1, h2⟩ => WShape.join_prop.1 _ h1 h2⟩
  have ⟨_, _, h2⟩ := WShape.join_prop.of_compat WShape.join_prop h
  exact ⟨_, (h2 _).1 .rfl⟩

theorem WShape.Compat.of_le {x : WShape n} (h : x ≤ y) : x.Compat y :=
  WShape.Compat.iff.2 ⟨_, h, .rfl⟩
theorem WShape.Compat.rfl {x : WShape n} : x.Compat x := .of_le .rfl
theorem WShape.Compat.symm {x : WShape n} : x.Compat y → y.Compat x := Shape.Compat.symm

def WShape.join (a b : WShape n) : WShape n :=
  if h : a.Compat b then ⟨a.1.join b.1, (WShape.join_prop.2 h).1⟩ else .bot
def WShape.Join (x y z : WShape n) : Prop :=
  ∀ w : WShape n, z ≤ w ↔ x ≤ w ∧ y ≤ w
theorem WShape.join_val {a b : WShape n} (h : a.Compat b) : (a.join b).1 = a.1.join b.1 := by
  simp [WShape.join, h]
theorem WShape.Join.le (H : WShape.Join x y z) : x ≤ z ∧ y ≤ z := (H _).1 .rfl
theorem WShape.Join.mk (h : x.Compat y) : WShape.Join x y (x.join y) := by
  simp only [join, dif_pos h]; exact (WShape.join_prop.2 h).2

theorem WShape.Join.compat (H : WShape.Join x y z) : x.Compat y :=
  WShape.Compat.iff.2 ⟨z, (H _).1 .rfl⟩

theorem WShape.Join.iff {x y z : WShape n} :
    WShape.Join x y z ↔ x.Compat y ∧ x.join y ≤ z ∧ z ≤ x.join y := by
  refine ⟨fun h => ⟨Compat.iff.2 ⟨_, h.le⟩, ?_⟩, fun ⟨h1, h2, h3⟩ w => ?_⟩
  · exact ⟨((mk h.compat _).2 h.le), (h _).2 (mk h.compat).le⟩
  · exact ⟨fun h => (mk h1 _).1 (h2.trans h), fun h => h3.trans <| (mk h1 _).2 h⟩

theorem WShape.lift_join {x y : WShape n} (le : n ≤ m) :
    (x.join y).lift m = (x.lift m).join (y.lift m) := by
  simp [join]; split <;> rename_i h
  · rw [dif_pos ((WShape.Compat.lift le).2 h)]; ext1; simp [lift_val le, Shape.lift_join le]
  · rw [dif_neg (mt (WShape.Compat.lift le).1 h), lift_bot]

theorem WShapeFun.join_mem {f : WShapeFun n}
    (hx : (x, y) ∈ f) (hy : (x', y') ∈ f) (hc : x.Compat x') :
    ∃ z, z ∈ f ∧ x.join x' ≤ z.1 ∧ z.1 ≤ x.join x' := by
  simp only [WShape.LE.def, WShape.join_val hc, f.join_mem' hx hy hc]

@[simp] theorem WShape.bot_join {x : WShape n} : bot.join x = x := by
  ext1; rw [join_val Compat.bot_l, bot, Shape.bot_join]
@[simp] theorem WShape.join_bot {x : WShape n} : x.join bot = x := by
  ext1; rw [join_val Compat.bot_r, bot, Shape.join_bot]
@[simp] theorem WShape.sort_join_sort :
    join (.sort r : WShape n) (.sort r') = if r = r' then .sort r else .bot := by
  ext1; simp [join, WShape.Compat, sort, Shape.Compat.sort_sort]; split <;> rfl


theorem WShape.Join.lift {x y z : WShape n} (le : n ≤ m) :
    (x.lift m).Join (y.lift m) (z.lift m) ↔ x.Join y z := by
  constructor
  · intro hJ w
    have := hJ (w.lift m)
    rwa [lift_le_lift le, lift_le_lift le, lift_le_lift le] at this
  · intro hJ; have ⟨h1, h2, h3⟩ := Join.iff.1 hJ
    refine Join.iff.2 ⟨(Compat.lift le).2 h1, ?_⟩
    exact lift_join le ▸ ⟨WShape.lift_mono le h2, WShape.lift_mono le h3⟩

theorem WShape.join_self {x y : WShape n} : WShape.Join x x y ↔ x ≤ y ∧ y ≤ x :=
  ⟨fun H => ⟨((H _).1 .rfl).1, (H _).2 ⟨.rfl, .rfl⟩⟩,
   fun ⟨H1, H2⟩ _ => ⟨fun h => ⟨H1.trans h, H1.trans h⟩, fun h => H2.trans h.1⟩⟩

theorem WShape.Join.left {x y : WShape n} (h : y ≤ x) : WShape.Join x y x :=
  fun _ => ⟨fun H => ⟨H, h.trans H⟩, (·.1)⟩

theorem WShape.Join.right {x y : WShape n} (h : y ≤ x) : WShape.Join y x x :=
  fun _ => ⟨fun H => ⟨h.trans H, H⟩, (·.2)⟩

def WShapeFun.Join (x y z : WShapeFun n) : Prop := ∀ w : WShapeFun n, z ≤ w ↔ x ≤ w ∧ y ≤ w

theorem WShapeFun.Join.le (H : WShapeFun.Join x y z) : x ≤ z ∧ y ≤ z := (H _).1 .rfl

def WShapeFun.join (x y : WShapeFun n) : WShapeFun n :=
  if h : x.Compat y then
    ⟨ShapeFun.join Shape.join x.1 y.1, ((WShape.join_prop.ih_fun WShape.join_prop).2 h).1⟩
  else .bot

theorem WShapeFun.join_val {x y : WShapeFun n} (H : Compat x y) :
    (x.join y).1 = x.1.join Shape.join y.1 := by simp [join, dif_pos H]

@[simp] theorem WShape.forallE_join_forallE {a a' : WShape n} {f f' : WShapeFun n}
    (hc1 : a.Compat a') (hc2 : WShapeFun.Compat f f') :
    (WShape.forallE a f).join (.forallE a' f') = .forallE (a.join a') (f.join f') := by
  have hc := Compat.forallE_forallE.2 ⟨hc1, hc2⟩
  ext1; rw [join_val hc]; simp [forallE, Shape.join, join_val hc1, WShapeFun.join_val hc2]

theorem WShapeFun.Join.mk (H : WShapeFun.Compat x y) : WShapeFun.Join x y (x.join y) := by
  simp [Join, WShapeFun.LE.def, join_val H]
  have ⟨_, h⟩ := (WShape.join_prop.ih_fun WShape.join_prop).2 H; exact h

theorem WShapeFun.Compat.iff {x y : WShapeFun n} : x.Compat y ↔ ∃ z, x ≤ z ∧ y ≤ z := by
  refine ⟨fun h => ⟨_, (Join.mk h).le⟩, fun ⟨_, h1, h2⟩ => ?_⟩
  exact (WShape.join_prop.ih_fun WShape.join_prop).1 _ h1 h2

@[simp] theorem WShapeFun.Compat.bot_l {s : WShapeFun n} : bot.Compat s := iff.2 ⟨_, bot_le, .rfl⟩
@[simp] theorem WShapeFun.Compat.bot_r {s : WShapeFun n} : s.Compat bot := iff.2 ⟨_, .rfl, bot_le⟩

theorem WShapeFun.Join.compat (H : Join x y z) : x.Compat y := Compat.iff.2 ⟨z, (H _).1 .rfl⟩

theorem WShapeFun.Join.iff :
    Join x y z ↔ x.Compat y ∧ x.join y ≤ z ∧ z ≤ x.join y := by
  refine ⟨fun h => ⟨Compat.iff.2 ⟨_, h.le⟩, ?_⟩, fun ⟨h1, h2, h3⟩ w => ?_⟩
  · exact ⟨((mk h.compat _).2 h.le), (h _).2 (mk h.compat).le⟩
  · exact ⟨fun h => (mk h1 _).1 (h2.trans h), fun h => h3.trans <| (mk h1 _).2 h⟩

theorem WShapeFun.join_mem'' {f : WShapeFun n}
    (hx : (x, y) ∈ f) (hy : (x', y') ∈ f) (hc : x.Compat x') : ∃ z, z ∈ f ∧ x.Join x' z.1 := by
  have ⟨⟨z, w⟩, h1, h2⟩ := f.join_mem' hx hy hc
  refine ⟨_, h1, WShape.Join.iff.2 ⟨hc, ?_⟩⟩
  simpa only [WShape.LE.def, WShape.join_val hc]

def WShapeFun.ofElems (f : List (WShape n × WShape n))
    (h1 : ∃ y, (WShape.bot, y) ∈ f)
    (h2 : ∀ x ∈ f, ∀ y ∈ f,
      (x.1.Compat y.1 → ∃ z ∈ f, x.1.Join y.1 z.1) ∧
      (x.1 ≤ y.1 → x.2 ≤ y.2)) : WShapeFun n := by
  refine ⟨f.map fun x => (x.1.1, x.2.1), ?_, ?_⟩
  · simp only [List.mem_map, Prod.mk.injEq]
    have ⟨_, h1⟩ := h1; refine ⟨⟨_, _, h1, rfl, rfl⟩, ?_⟩
    rintro _ ⟨⟨x, y⟩, a1, rfl⟩ ⟨x', y'⟩ ⟨⟨u, v⟩, a2, ⟨⟩⟩; dsimp
    have ⟨b1, b2⟩ := h2 _ a1 _ a2; refine ⟨fun hc => ?_, b2⟩
    have ⟨_, c1, c2⟩ := b1 hc; have := (WShape.Join.iff.1 c2).2
    simp only [WShape.LE.def, WShape.join_val hc] at this
    exact ⟨_, ⟨⟨_, _⟩, c1, rfl⟩, this⟩
  · simp; rintro _ _ x y _ rfl rfl; exact ⟨x.2, y.2⟩

theorem WShapeFun.mem_ofElems {f : List (WShape n × WShape n)} {h1 h2} :
    (x, y) ∈ WShapeFun.ofElems f h1 h2 ↔ (x, y) ∈ f := by
  show (x.1, y.1) ∈ f.map (fun p => (p.1.1, p.2.1)) ↔ _
  simp only [List.mem_map, Prod.mk.injEq]
  exact ⟨fun ⟨⟨a, b⟩, h, ha, hb⟩ => by cases WShape.ext ha; cases WShape.ext hb; exact h,
    fun h => ⟨_, h, rfl, rfl⟩⟩

@[implicit_reducible] def TShape := Σ n, WShape n
abbrev WShape.T : WShape n → TShape := Sigma.mk _

def TShape.LE (a b : TShape) : Prop := a.2.lift (max a.1 b.1) ≤ b.2.lift _
instance : _root_.LE TShape := ⟨TShape.LE⟩
theorem TShape.LE.def' {a b : TShape} : a ≤ b ↔ a.2.lift (max a.1 b.1) ≤ b.2.lift _ := .rfl

def TShapeFun.LE (a : WShapeFun n) (b : WShapeFun m) : Prop :=
  a.lift (max n m) ≤ b.lift _

theorem TShape.LE.def {a b : TShape} (h1 : a.1 ≤ m) (h2 : b.1 ≤ m) :
    a ≤ b ↔ a.2.lift m ≤ b.2.lift m := by
  refine (WShape.lift_le_lift (Nat.max_le.2 ⟨h1, h2⟩)).symm.trans ?_
  rw [WShape.lift_lift (.inl (Nat.le_max_left ..)), WShape.lift_lift (.inl (Nat.le_max_right ..))]

theorem TShapeFun.LE.def {a : WShapeFun n} {b : WShapeFun m} (h1 : n ≤ k) (h2 : m ≤ k) :
    TShapeFun.LE a b ↔ a.lift k ≤ b.lift k := by
  refine (WShapeFun.lift_le_lift (Nat.max_le.2 ⟨h1, h2⟩)).symm.trans ?_
  rw [WShapeFun.lift_lift (.inl (Nat.le_max_left ..)),
    WShapeFun.lift_lift (.inl (Nat.le_max_right ..))]

theorem TShape.LE.forallE_decomp {b : WShape n} {f : WShapeFun n} {b' : WShape n'} {f' : WShapeFun n'}
    (le : (WShape.forallE b f).T ≤ (WShape.forallE b' f').T) :
    b.lift (max n n') ≤ b'.lift (max n n') ∧
      f.lift (max n n') ≤ f'.lift (max n n') := by
  have le₁ := Nat.le_max_left n n'; have le₂ := Nat.le_max_right n n'
  have h := (TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂)).1 le
  have h_raw : ((WShape.forallE b f).lift _).1 ≤ ((WShape.forallE b' f').lift _).1 := h
  rw [WShape.lift_val (Nat.succ_le_succ le₁), WShape.lift_val (Nat.succ_le_succ le₂)] at h_raw
  simp only [WShape.forallE, Shape.lift, Shape.LE.def] at h_raw
  constructor
  · show (b.lift _).1 ≤ (b'.lift _).1
    rw [WShape.lift_val le₁, WShape.lift_val le₂]; exact h_raw.1
  · show (f.lift _).1.LE (f'.lift _).1
    rw [WShapeFun.lift_val le₁, WShapeFun.lift_val le₂]; exact h_raw.2

theorem TShape.LE.lam'_decomp {f : WShapeFun n} {f' : WShapeFun n'} :
    (WShape.lam' f).T ≤ (WShape.lam' f').T →
    f.lift (max n n') ≤ f'.lift (max n n') := by
  have le₁ := Nat.le_max_left n n'; have le₂ := Nat.le_max_right n n'
  have le₁' := Nat.succ_le_succ le₁; have le₂' := Nat.succ_le_succ le₂
  rw [TShape.LE.def le₁' le₂', WShape.LE.def, WShape.lift_val le₁', WShape.lift_val le₂',
    WShape.lam', WShape.lam']
  dsimp; split <;> rename_i hf
  · split <;> rename_i hf' <;>
      simp [WShape.lam, Shape.lift, WShapeFun.LE.def, WShapeFun.lift_val, le₁, le₂]
    intro h; cases Shape.le_bot.1 h
  · rintro -
    refine WShapeFun.LE.def'.2 fun x y h => ?_
    obtain ⟨_, _, h1, ⟨⟩, ⟨⟩⟩ := (WShapeFun.mem_lift le₁).1 h
    have := WShape.le_bot.1 <| Decidable.by_contra fun h => hf ⟨_, h1, h⟩
    dsimp at this; cases this
    have ⟨_, h⟩ := f'.bot_mem
    exact ⟨_, _, (WShapeFun.mem_lift le₂).2 ⟨_, _, h, rfl, rfl⟩, by simp⟩

theorem TShape.LE.le_lam {f : WShapeFun n} {hl} {f' : WShapeFun n'} {hl'}
    (le : (WShape.lam f hl).T ≤ (WShape.lam f' hl').T) :
    f.lift (max n n') ≤ f'.lift (max n n') := by
  have le₁ := Nat.le_max_left n n'; have le₂ := Nat.le_max_right n n'
  have h := (TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂)).1 le
  have h_raw : ((WShape.lam f hl).lift _).1 ≤ ((WShape.lam f' hl').lift _).1 := h
  rw [WShape.lift_val (Nat.succ_le_succ le₁), WShape.lift_val (Nat.succ_le_succ le₂)] at h_raw
  simp only [WShape.lam, Shape.lift, Shape.LE.def] at h_raw
  show (f.lift _).1.LE (f'.lift _).1
  rw [WShapeFun.lift_val le₁, WShapeFun.lift_val le₂]; exact h_raw

def TShape.bot : TShape := WShape.T (n := 0) .bot
def TShape.sort (r : SLvl) : TShape := WShape.T (n := 0) (.sort r)
def TShape.type : TShape := .sort (fun _ => 1)

nonrec theorem TShape.LE.rfl {a : TShape} : a ≤ a := WShape.LE.rfl

theorem TShape.LE.trans {a b c : TShape} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  let k := max (max a.1 b.1) c.1
  have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
  exact (LE.def hk.1.1 hk.2).2 (.trans ((LE.def hk.1.1 hk.1.2).1 h1) ((LE.def hk.1.2 hk.2).1 h2))

theorem TShape.LE.lift_l {a b : TShape} (h1 : a.1 ≤ b.1) : a ≤ b ↔ a.2.lift (b.1) ≤ b.2 :=
  (LE.def h1 (Nat.le_refl _)).trans (WShape.lift_self ▸ .rfl)
theorem TShape.LE.lift_r {a b : TShape} (h1 : b.1 ≤ a.1) : a ≤ b ↔ a.2 ≤ b.2.lift (a.1) :=
  (LE.def (Nat.le_refl _) h1).trans (WShape.lift_self ▸ .rfl)
theorem WShape.LE.T_iff {a b : WShape n} : a.T ≤ b.T ↔ a ≤ b :=
  (TShape.LE.lift_l (Nat.le_refl _) (a := a.T) (b := b.T)).trans (WShape.lift_self ▸ .rfl)
theorem WShape.LE.T {a b : WShape n} : a ≤ b → a.T ≤ b.T := T_iff.2
theorem WShape.LE.of_T {a b : WShape n} : a.T ≤ b.T → a ≤ b := T_iff.1

theorem TShape.bot_eqv : (WShape.bot (n := n)).T ≤ bot ∧ bot ≤ (WShape.bot (n := n)).T := by
  simp [TShape.LE.def', bot, WShape.lift_bot]

theorem TShape.bot_le' : (WShape.bot (n := n)).T ≤ a := by
  simp [TShape.LE.def', WShape.lift_bot]

theorem TShape.bot_le {a : TShape} : bot ≤ a := bot_le'

theorem TShape.le_bot {a : TShape} : a ≤ bot ↔ a.2 = .bot := by
  simp [TShape.LE.def', bot, WShape.lift_le_bot (Nat.le_max_left ..), WShape.lift_bot]

theorem TShape.le_bot' {a : TShape} : a ≤ bot ↔ a = WShape.T (n := a.1) .bot := by
  rw [le_bot]; let ⟨n, s⟩ := a
  exact ⟨fun h => congrArg (Sigma.mk n) h, fun h => Sigma.mk.inj h |>.2 |> eq_of_heq⟩

theorem TShape.lift_eqv {a : TShape} (h : a.1 ≤ m) :
    (a.2.lift m).T ≤ a ∧ a ≤ (a.2.lift m).T := by
  simp [TShape.LE.def', WShape.lift_lift (.inl h), WShape.LE.rfl]

theorem TShape.sort_eqv :
    (WShape.sort (n := n) r).T ≤ .sort r ∧ .sort r ≤ (WShape.sort (n := n) r).T := by
  simp [sort, TShape.LE.def', WShape.lift_sort, WShape.LE.rfl]

theorem TShape.sort_not_le_lam' {f : WShapeFun n'} :
    ¬(.sort r : WShape n).T ≤ (WShape.lam' f).T := by
  rw [TShape.LE.def']; simp only [WShape.T, WShape.lift_sort]
  intro h; have h := congrArg (·.1) (WShape.sort_le.1 h)
  simp only [WShape.sort, WShape.lam'] at h; split at h <;>
  · simp only [WShape.lam, WShape.bot, WShape.lift_val (Nat.le_max_right ..)] at h
    have hk : max n (n' + 1) = max n (n' + 1) - 1 + 1 := by omega
    rw [hk] at h; simp [Shape.sort, Shape.lift, Shape.bot] at h

theorem TShape.forallE_not_le_lam' {a : WShape n} {f₁ : WShapeFun n} {f₂ : WShapeFun n'} :
    ¬(.forallE a f₁ : WShape (n+1)).T ≤ (WShape.lam' f₂).T := by
  have' le₁ := Nat.le_max_left ..; have' le₂ := Nat.le_max_right ..
  rw [TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂),
    WShape.lift_forallE le₁, WShape.lift_lam' le₂]
  intro hle; have ⟨_, _, _, _, hle⟩ := WShape.forallE_le.1 hle
  unfold WShape.lam' at hle; split at hle <;>
    simp [WShape.ext_iff, WShape.forallE, WShape.lam] at hle
  cases hle

theorem TShape.ctor_not_le_lam' {c : Name} {l : List (WShape n)} {h} {f : WShapeFun n'} :
    ¬(WShape.ctor c l h : WShape (n+1)).T ≤ (WShape.lam' f).T := by
  have' le₁ := Nat.le_max_left ..; have' le₂ := Nat.le_max_right ..
  rw [TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂),
    WShape.lift_ctor le₁, WShape.lift_lam' le₂]
  intro hle
  unfold WShape.lam' at hle; split at hle <;>
    simp_all [WShape.LE.def, WShape.ctor, WShape.lam, WShape.bot, Shape.LE.def]

theorem TShape.rigid_not_le_lam' {l : List (WShape n)} {t} {f : WShapeFun n'} :
    ¬(WShape.rigid c ls l t).T ≤ (WShape.lam' f).T := by
  rw [TShape.LE.def (Nat.succ_le_succ (Nat.le_max_left ..))
    (Nat.succ_le_succ (Nat.le_max_right ..)), WShape.lift_rigid (Nat.le_max_left ..),
    WShape.lift_lam' (Nat.le_max_right ..), WShape.rigid_le]
  unfold WShape.lam'; split <;> rintro ⟨_, _, h, _⟩ <;> cases congrArg (·.1) h

theorem TShape.lam_not_le_forallE {f₁ : WShapeFun n} {hl} {a' : WShape n'} {f' : WShapeFun n'} :
    ¬(.lam f₁ hl : WShape (n+1)).T ≤ (.forallE a' f' : WShape (n'+1)).T := by
  have' le₁ := Nat.le_max_left ..; have' le₂ := Nat.le_max_right ..
  rw [TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂),
    WShape.lift_lam le₁, WShape.lift_forallE le₂]
  simp [(· ≤ ·), Shape.LE, Shape.ble, WShape.lam, WShape.forallE]

theorem TShape.sort_not_le_forallE {a' : WShape n'} {f' : WShapeFun n'} :
    ¬(.sort r : WShape n).T ≤ (.forallE a' f' : WShape (n'+1)).T := by
  rw [TShape.LE.def']; simp only [WShape.T, WShape.lift_sort]
  intro h; have h := congrArg (·.1) (WShape.sort_le.1 h)
  simp only [WShape.sort, WShape.forallE, WShape.lift_val (Nat.le_max_right ..)] at h
  have hk : max n (n' + 1) = max n (n' + 1) - 1 + 1 := by omega
  rw [hk] at h; simp [Shape.sort, Shape.lift] at h

theorem TShape.sort_not_le_ctor' {c : Name} {l : List (WShape n')} :
    ¬(.sort r : WShape n).T ≤ (WShape.ctor' c l).T := by
  rw [TShape.LE.def']; simp only [WShape.T, WShape.lift_sort]
  intro h; have h := congrArg (·.1) (WShape.sort_le.1 h)
  simp only [WShape.sort, WShape.ctor', WShape.lift_val (Nat.le_max_right ..)] at h
  split at h
  · simp only [WShape.ctor] at h
    have hk : max n (n' + 1) = max n (n' + 1) - 1 + 1 := by omega
    rw [hk] at h; simp [Shape.sort, Shape.lift] at h
  · simp only [WShape.bot] at h
    have hk : max n (n' + 1) = max n (n' + 1) - 1 + 1 := by omega
    rw [hk] at h; simp [Shape.sort, Shape.lift, Shape.bot] at h

theorem TShape.forallE_not_le_ctor' {a : WShape n} {f : WShapeFun n}
    {c : Name} {l : List (WShape n')} :
    ¬(.forallE a f : WShape (n+1)).T ≤ (WShape.ctor' c l).T := by
  have' le₁ := Nat.le_max_left ..; have' le₂ := Nat.le_max_right ..
  rw [TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂),
    WShape.lift_forallE le₁, WShape.lift_ctor' le₂]
  intro hle; have ⟨_, _, _, _, hle⟩ := WShape.forallE_le.1 hle
  unfold WShape.ctor' at hle; split at hle
  · simp [WShape.ext_iff, WShape.forallE, WShape.ctor] at hle
  · have := congrArg (·.1) hle
    simp only [WShape.forallE, WShape.bot, Shape.bot] at this
    cases this

theorem TShape.lam_not_le_ctor' {f : WShapeFun n} {hl}
    {c : Name} {l : List (WShape n')} :
    ¬(.lam f hl : WShape (n+1)).T ≤ (WShape.ctor' c l).T := by
  have' le₁ := Nat.le_max_left ..; have' le₂ := Nat.le_max_right ..
  rw [TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂),
    WShape.lift_lam le₁, WShape.lift_ctor' le₂]
  unfold WShape.ctor'; split <;>
    simp [(· ≤ ·), Shape.LE, Shape.ble, WShape.lam, WShape.ctor, WShape.bot]

theorem TShape.rigid_not_le_forallE {l : List (WShape n)} {t} {a' : WShape n'}
    {f' : WShapeFun n'} :
    ¬(WShape.rigid c ls l t).T ≤ (.forallE a' f' : WShape (n'+1)).T := by
  rw [TShape.LE.def (Nat.succ_le_succ (Nat.le_max_left ..))
    (Nat.succ_le_succ (Nat.le_max_right ..)), WShape.lift_rigid (Nat.le_max_left ..),
    WShape.lift_forallE (Nat.le_max_right ..), WShape.rigid_le]
  rintro ⟨_, _, h, _⟩; cases congrArg (·.1) h

theorem TShape.rigid_not_le_sort {l : List (WShape n)} {t} :
    ¬(WShape.rigid c ls l t).T ≤ (.sort r : WShape n').T := by
  intro h
  have := h.trans TShape.sort_eqv.1
  rw [TShape.LE.def (Nat.le_refl _) (Nat.zero_le _), WShape.lift_self] at this
  simp only [TShape.sort, WShape.T, WShape.lift_sort] at this
  obtain ⟨_, _, h, _⟩ := WShape.rigid_le.1 this; cases congrArg (·.1) h

theorem TShape.rigid_not_le_ctor' {l : List (WShape n)} {t} {c' : Name} {l' : List (WShape n')} :
    ¬(WShape.rigid c ls l t).T ≤ (WShape.ctor' c' l').T := by
  rw [TShape.LE.def (Nat.succ_le_succ (Nat.le_max_left ..))
    (Nat.succ_le_succ (Nat.le_max_right ..)), WShape.lift_rigid (Nat.le_max_left ..),
    WShape.lift_ctor' (Nat.le_max_right ..), WShape.rigid_le]
  unfold WShape.ctor'; split <;> rintro ⟨_, _, h, _⟩ <;> cases congrArg (·.1) h

theorem TShape.sort_not_le_rigid {l : List (WShape n')} {t} :
    ¬(.sort r : WShape n).T ≤ (WShape.rigid c ls l t).T := by
  rw [TShape.LE.def']; simp only [WShape.T, WShape.lift_sort]
  intro h; have h := congrArg (·.1) (WShape.sort_le.1 h)
  simp only [WShape.sort, WShape.rigid, WShape.lift_val (Nat.le_max_right ..)] at h
  have hk : max n (n' + 1) = max n (n' + 1) - 1 + 1 := by omega
  rw [hk] at h; simp [Shape.sort, Shape.lift] at h

theorem TShape.forallE_not_le_rigid {a : WShape n} {f : WShapeFun n} {l : List (WShape n')} {t} :
    ¬(.forallE a f : WShape (n+1)).T ≤ (WShape.rigid c ls l t).T := by
  have' le₁ := Nat.le_max_left ..; have' le₂ := Nat.le_max_right ..
  rw [TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂),
    WShape.lift_forallE le₁, WShape.lift_rigid le₂]
  intro hle; have ⟨_, _, _, _, hle⟩ := WShape.forallE_le.1 hle
  cases congrArg (·.1) hle

theorem TShape.lam_not_le_rigid {f : WShapeFun n} {hl} {l : List (WShape n')} {t} :
    ¬(.lam f hl : WShape (n+1)).T ≤ (WShape.rigid c ls l t).T := by
  have' le₁ := Nat.le_max_left ..; have' le₂ := Nat.le_max_right ..
  rw [TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂),
    WShape.lift_lam le₁, WShape.lift_rigid le₂]
  simp [(· ≤ ·), Shape.LE, Shape.ble, WShape.lam, WShape.rigid]

/-- Rigid heads are separated from each other by their name and levels. -/
theorem TShape.LE.rigid_inv {l : List (WShape n)} {t} {l' : List (WShape n')} {t'}
    (h : (WShape.rigid c ls l t).T ≤ (WShape.rigid c' ls' l' t').T) : c = c' ∧ ls = ls' := by
  rw [TShape.LE.def (Nat.succ_le_succ (Nat.le_max_left ..))
    (Nat.succ_le_succ (Nat.le_max_right ..)), WShape.lift_rigid (Nat.le_max_left ..),
    WShape.lift_rigid (Nat.le_max_right ..), WShape.rigid_le_rigid] at h
  exact ⟨h.1, h.2.1⟩

theorem WShape.Compat_lift_val {a : WShape n₁} {b : WShape n₂}
    (le₁ : n₁ ≤ m) (le₂ : n₂ ≤ m) :
    (a.lift m).Compat (b.lift m) ↔ (a.1.lift m).Compat (b.1.lift m) := by
  show (a.lift m).1.Compat (b.lift m).1 ↔ _
  rw [lift_val le₁, lift_val le₂]

def TShape.Compat (x y : TShape) : Prop := (x.2.lift (max x.1 y.1)).Compat (y.2.lift _)

theorem TShape.Compat.def {x y : TShape} (h1 : x.1 ≤ m) (h2 : y.1 ≤ m) :
    x.Compat y ↔ (x.2.lift m).Compat (y.2.lift _) := by
  refine (WShape.Compat.lift (Nat.max_le.2 ⟨h1, h2⟩)).symm.trans ?_
  rw [WShape.lift_lift (.inl (Nat.le_max_left ..)), WShape.lift_lift (.inl (Nat.le_max_right ..))]

theorem WShape.Compat.T_iff {x y : WShape n} : x.Compat y ↔ x.T.Compat y.T := by
  refine .trans ?_ (TShape.Compat.def (x := x.T) (y := y.T) (Nat.le_refl _) (Nat.le_refl _)).symm
  rw [WShape.lift_self, WShape.lift_self]

theorem WShape.Compat.T {x y : WShape n} : x.Compat y → x.T.Compat y.T := T_iff.1

theorem TShape.Compat.def' {x y : TShape} : x.Compat y ↔ ∃ z, x ≤ z ∧ y ≤ z := by
  refine ⟨fun h => ?_, fun ⟨z, h1, h2⟩ => ?_⟩
  · have ⟨z, h1, h2⟩ := WShape.Compat.iff.1 h
    exact ⟨z.T, (LE.lift_l (Nat.le_max_left ..)).2 h1, (LE.lift_l (Nat.le_max_right ..)).2 h2⟩
  · let k := max x.1 (max y.1 z.1); have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
    exact (TShape.Compat.def hk.1 hk.2.1).2 <|
      WShape.Compat.iff.2 ⟨z.2.lift k, (LE.def hk.1 hk.2.2).1 h1, (LE.def hk.2.1 hk.2.2).1 h2⟩

theorem TShape.Compat.bot_l : TShape.bot.Compat x :=
  TShape.Compat.def'.2 ⟨x, TShape.bot_le, .rfl⟩

theorem TShape.Compat.bot_r : Compat x TShape.bot :=
  TShape.Compat.def'.2 ⟨x, .rfl, TShape.bot_le⟩

theorem TShape.Compat.bot_l' : (WShape.bot (n := n)).T.Compat x :=
  TShape.Compat.def'.2 ⟨x, TShape.bot_le', .rfl⟩

theorem TShape.Compat.bot_r' : Compat x (WShape.bot (n := n)).T :=
  TShape.Compat.def'.2 ⟨x, .rfl, TShape.bot_le'⟩

theorem NonZero.not_iff {f : WShapeFun n} : ¬f.NonZero ↔ f ≤ .bot := by
  simp only [WShapeFun.NonZero, ShapeFun.NonZero, Prod.exists, not_exists, not_and,
    Decidable.not_not, WShapeFun.bot, ShapeFun.bot, WShapeFun.LE.def, ShapeFun.LE.def,
    List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, and_assoc, exists_and_left,
    exists_eq_left, Shape.bot_le, true_and]

theorem NonZero.iff {f : WShapeFun n} : f.NonZero ↔ ¬f ≤ .bot :=
  (Decidable.not_iff_comm.1 NonZero.not_iff).symm

theorem WShapeFun.NonZero.join {f f' : WShapeFun n} (h : f.Compat f') :
    (f.join f').NonZero ↔ f.NonZero ∨ f'.NonZero := by
  refine ⟨fun hjoin => ?_, ?_⟩
  · by_cases h1 : f.NonZero <;> [exact .inl h1; skip]
    by_cases h2 : f'.NonZero <;> [exact .inr h2; skip]
    refine (ShapeModel.NonZero.iff.1 hjoin ?_).elim
    exact (WShapeFun.Join.mk h _).2 ⟨ShapeModel.NonZero.not_iff.1 h1, ShapeModel.NonZero.not_iff.1 h2⟩
  · rintro (h1 | h1) <;> refine ShapeModel.NonZero.iff.2 fun hbot => ShapeModel.NonZero.iff.1 h1 ?_
    · exact ((WShapeFun.Join.mk h _).1 hbot).1
    · exact ((WShapeFun.Join.mk h _).1 hbot).2

theorem WShape.Compat.mono {x y x' y' : WShape n}
    (h1 : x ≤ x') (h2 : y ≤ y') (H : x'.Compat y') : x.Compat y :=
  have ⟨_, a1, a2⟩ := WShape.Compat.iff.1 H
  WShape.Compat.iff.2 ⟨_, h1.trans a1, h2.trans a2⟩

theorem WShapeFun.Compat.mono {x y x' y' : WShapeFun n}
    (h1 : x ≤ x') (h2 : y ≤ y') (H : x'.Compat y') : x.Compat y :=
  have ⟨_, a1, a2⟩ := WShapeFun.Compat.iff.1 H
  WShapeFun.Compat.iff.2 ⟨_, h1.trans a1, h2.trans a2⟩

theorem TShape.Compat.mono {x y x' y' : TShape}
    (h1 : x ≤ x') (h2 : y ≤ y') (H : x'.Compat y') : x.Compat y := by
  let k := max (max x.1 y.1) (max x'.1 y'.1)
  have hk := Nat.max_le.1 (Nat.le_refl k); simp only [Nat.max_le] at hk
  have h1 := (TShape.LE.def hk.1.1 hk.2.1).1 h1
  have h2 := (TShape.LE.def hk.1.2 hk.2.2).1 h2
  have H := (TShape.Compat.def hk.2.1 hk.2.2).1 H
  exact (TShape.Compat.def hk.1.1 hk.1.2).2 <| H.mono h1 h2

theorem WShape.Compat.lam' {a b : WShapeFun n} : Compat (.lam' a) (.lam' b) ↔ a.Compat b := by
  rw [WShape.lam']; split <;> rename_i h1
  · rw [WShape.lam']; split <;> [rfl; rename_i h2]
    simp; exact .mono .rfl (NonZero.not_iff.1 h2) .bot_r
  · simp; exact .mono (NonZero.not_iff.1 h1) .rfl .bot_l

theorem WShape.Join.lam' {a b c : WShapeFun n} :
    Join (.lam' a) (.lam' b) (.lam' c) ↔ a.Join b c := by
  refine ⟨fun H z => by simpa [lam'_le_lam'] using H (.lam' z), fun H z => ?_⟩
  by_cases hz : ∃ z', .lam' z' = z
  · obtain ⟨z', rfl⟩ := hz; simp only [lam'_le_lam', H _]
  have {x} : WShape.lam' x ≤ z ↔ x ≤ .bot := by
    unfold WShape.lam'; split <;> rename_i h
    · simp [← NonZero.not_iff, h, WShape.LE.def, lam, Shape.lam_le]
      obtain ⟨_, wf⟩ := z; rintro _ h1 ⟨⟩; refine hz ⟨⟨_, wf.1⟩, ?_⟩
      rw [WShape.lam', dif_pos (by exact wf.2)]; rfl
    · simp [NonZero.not_iff.1 h]
  simp only [this, H _]

theorem WShape.ctor'_join {l l' : List (WShape n)} {c : Name}
    (h : List.Forall₂ Compat l l') :
    (WShape.ctor' c l).join (WShape.ctor' c l') = WShape.ctor' c (l.zipWith join l') := by
  have key : (IsStruct c = true → ListNonZero (l.zipWith join l')) ↔
      (IsStruct c = true → ListNonZero l) ∨ (IsStruct c = true → ListNonZero l') := by
    suffices ListNonZero (l.zipWith join l') ↔ ListNonZero l ∨ ListNonZero l' by
      rw [this]
      by_cases hIs : IsStruct c <;> simp [hIs]
    induction h with | nil => simp [ListNonZero] | @cons x y L L' hh _ ih
    have hcompat_join : ¬(x.join y).1 ≤ .bot ↔ ¬x.1 ≤ .bot ∨ ¬y.1 ≤ .bot := by
      have hJ := WShape.Join.mk hh .bot
      simp only [WShape.LE.def, WShape.bot] at hJ
      rw [hJ]
      by_cases hx : x.1 ≤ .bot <;> by_cases hy : y.1 ≤ .bot <;> simp [hx, hy]
    simp only [List.zipWith, ListNonZero, List.mem_cons]
    constructor
    · rintro ⟨z, (rfl | hzL), hznz⟩
      · rcases hcompat_join.mp hznz with hh | hh
        · exact .inl ⟨x, .inl rfl, hh⟩
        · exact .inr ⟨y, .inl rfl, hh⟩
      · rcases ih.mp ⟨z, hzL, hznz⟩ with ⟨z', hz'L, hz'nz⟩ | ⟨z', hz'L, hz'nz⟩
        · exact .inl ⟨z', .inr hz'L, hz'nz⟩
        · exact .inr ⟨z', .inr hz'L, hz'nz⟩
    · rintro (⟨z, (rfl | hzL), hznz⟩ | ⟨z, (rfl | hzL), hznz⟩)
      · exact ⟨_, .inl rfl, hcompat_join.mpr (.inl hznz)⟩
      · obtain ⟨w, hwL, hwnz⟩ := ih.mpr (.inl ⟨z, hzL, hznz⟩)
        exact ⟨w, .inr hwL, hwnz⟩
      · exact ⟨_, .inl rfl, hcompat_join.mpr (.inr hznz)⟩
      · obtain ⟨w, hwL, hwnz⟩ := ih.mpr (.inr ⟨z, hzL, hznz⟩)
        exact ⟨w, .inr hwL, hwnz⟩
  ext1; rw [join_val (Compat.ctor'_ctor' h)]
  unfold WShape.ctor'; split <;> rename_i h1 <;> split <;> rename_i h2
  · rw [dif_pos (key.mpr (.inl h1))]; simp [ctor, Shape.join]
    congr 1; clear h1 h2 key
    induction h with
    | nil => rfl
    | @cons x y L L' hh _ ih => simp [WShape.join_val hh, ih]
  · rw [dif_pos (key.mpr (.inl h1))]; simp [ctor, bot, Shape.join_bot]
    have h2' : ∀ x ∈ l', x.1 ≤ Shape.bot := by simpa [ListNonZero] using fun hNZ => h2 fun _ => hNZ
    congr 1; clear h1 h2 key
    induction h with | nil => rfl | @cons x y L L' hh _ ih
    have hy_bot : y.1 = .bot := Shape.le_bot.1 (h2' y (.head _))
    simp [WShape.join_val hh, hy_bot, Shape.join_bot]
    exact ih (fun z hz => h2' z (.tail _ hz))
  · rw [dif_pos (key.mpr (.inr h2))]; simp [ctor, bot, Shape.bot_join]
    have h1' : ∀ x ∈ l, x.1 ≤ Shape.bot := by
      have ⟨_, hNZ⟩ := Decidable.not_imp_iff_and_not.1 h1
      simp [ListNonZero] at hNZ; exact hNZ
    congr 1; clear h1 h2 key
    induction h with | nil => rfl | @cons x y L L' hh _ ih
    have hx_bot : x.1 = .bot := Shape.le_bot.1 (h1' x (.head _))
    simp [WShape.join_val hh, hx_bot, Shape.bot_join]
    exact ih fun z hz => h1' z (.tail _ hz)
  · rw [dif_neg fun hh => (key.mp hh).elim h1 h2]; rfl

theorem WShape.ctor_le :
    WShape.ctor c l h ≤ s ↔ ∃ l' h', s = WShape.ctor c l' h' ∧ l.Forall₂ (· ≤ ·) l' := by
  simp [ctor, WShape.LE.def, WShape.ext_iff]
  cases s using WShape.casesOn' <;>
    simp [bot, sort, forallE, lam, ctor, rigid, Shape.bot, Shape.sort, Shape.LE.def]
  rename_i l₁ wf; refine ⟨fun ⟨rfl, h2⟩ => ⟨_, rfl, wf, h2⟩, fun ⟨_, h1, _, h3⟩ => ?_⟩
  injection h1 with eq1 eq2
  rw [← List.forall₂_map_right_iff, eq2, List.forall₂_map_right_iff]
  exact ⟨eq1.symm, h3⟩

theorem WShape.ctor'_le : WShape.ctor' c l ≤ s ↔
    ((IsStruct c → ListNonZero l) → ∃ l' h', s = WShape.ctor c l' h' ∧ l.Forall₂ (· ≤ ·) l') := by
  unfold ctor'; split <;> rename_i h1 <;> simp [eq_true h1, h1, WShape.ctor_le]

theorem WShape.ctor'_le_ctor' (h : List.Forall₂ (· ≤ ·) l l') :
    WShape.ctor' c l ≤ WShape.ctor' c l' := by
  unfold ctor'
  split <;> rename_i h1 <;> [skip; exact WShape.bot_le]
  rw [dif_pos (WShape.ListNonZero.mono h ∘ h1)]
  exact Shape.LE.def.2 ⟨rfl, by simpa⟩

theorem TShape.ctor_not_le_forallE :
    ¬(WShape.ctor c l h : WShape (n+1)).T ≤ (.forallE a' f' : WShape (n'+1)).T := fun h => by
  rw [TShape.LE.def (Nat.succ_le_succ (Nat.le_max_left ..))
    (Nat.succ_le_succ (Nat.le_max_right ..)), WShape.lift_ctor (Nat.le_max_left ..),
    WShape.lift_forallE (Nat.le_max_right ..), WShape.ctor_le] at h; obtain ⟨_, _, ⟨⟩, _⟩ := h

theorem WShape.le_zipWith_join (hc : List.Forall₂ WShape.Compat l l') :
    l.Forall₂ (· ≤ ·) (l.zipWith WShape.join l') ∧
    l'.Forall₂ (· ≤ ·) (l.zipWith WShape.join l') := by
  induction hc with | nil => exact ⟨.nil, .nil⟩ | cons h _ ih
  have h := (WShape.Join.mk h).le; exact ⟨.cons h.1 ih.1, .cons h.2 ih.2⟩

def TShape.join (x y : TShape) : TShape := ⟨max x.1 y.1, (x.2.lift _).join (y.2.lift _)⟩

theorem TShape.lift_join {x y : TShape} (h1 : x.1 ≤ m) (h2 : y.1 ≤ m) :
    (x.join y).2.lift m = (x.2.lift m).join (y.2.lift m) := by
  simp [join, WShape.lift_join (Nat.max_le.2 ⟨h1, h2⟩), WShape.lift_lift (.inl (Nat.le_max_left ..)),
    WShape.lift_lift (.inl (Nat.le_max_right ..))]

theorem WShape.T_join {a b : WShape n} : a.T.join b.T = (a.join b).T := by
  rw [TShape.join, Nat.max_self n]; simp [lift_self]

def TShape.Join (x y z : TShape) := ∀ w, z ≤ w ↔ x ≤ w ∧ y ≤ w

theorem TShape.Join.le (H : Join x y z) : x ≤ z ∧ y ≤ z := (H _).1 .rfl

theorem TShape.Join.def (h1 : x.1 ≤ m) (h2 : y.1 ≤ m) (h3 : z.1 ≤ m) :
    Join x y z ↔ WShape.Join (x.2.lift m) (y.2.lift m) (z.2.lift m) := by
  constructor <;> intro hJ w
  · have hle : m ≤ m := Nat.le_refl m
    have := hJ (⟨m, w⟩ : TShape)
    rwa [TShape.LE.def h3 hle, TShape.LE.def h1 hle, TShape.LE.def h2 hle, WShape.lift_self] at this
  · let k := max m w.1
    have hk : m ≤ k := Nat.le_max_left ..
    have hwk : w.1 ≤ k := Nat.le_max_right ..
    rw [TShape.LE.def (Nat.le_trans h3 hk) hwk, TShape.LE.def (Nat.le_trans h1 hk) hwk,
      TShape.LE.def (Nat.le_trans h2 hk) hwk, ← WShape.lift_lift (.inl h3),
      ← WShape.lift_lift (.inl h1), ← WShape.lift_lift (.inl h2)]
    exact (WShape.Join.lift hk |>.2 hJ) _

theorem WShape.Join.T_iff {x y z : WShape n} : WShape.Join x y z ↔ TShape.Join x.T y.T z.T := by
  refine .symm <| (TShape.Join.def (x := x.T) (y := y.T) (z := z.T)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)).trans ?_
  rw [WShape.lift_self, WShape.lift_self, WShape.lift_self]

theorem WShape.Join.T {x y z : WShape n} : Join x y z → TShape.Join x.T y.T z.T := T_iff.1

theorem TShape.Join.mk (H : x.Compat y) : Join x y (x.join y) := by
  let m := max x.1 y.1; have ⟨hx, hy⟩ := Nat.max_le.1 (Nat.le_refl m)
  rw [TShape.Join.def hx hy (Nat.le_refl _), TShape.lift_join hx hy]
  exact .mk ((TShape.Compat.def hx hy).1 H)

theorem ShapeFun.WF.bot_le (wf : WF Shape.WF f) : ShapeFun.bot.LE f := by
  simp [ShapeFun.LE.def, bot]
  exact ⟨.bot, wf.1.1, Shape.bot_le⟩

theorem Shape.WF.lam_non_bot (wf : WF (n := n+1) (.lam f)) : ∃ x y, (x, y) ∈ f ∧ y ≠ .bot :=
  have ⟨⟨_, _⟩, h1, h2⟩ := wf.2; ⟨_, _, h1, mt Shape.le_bot.2 h2⟩

omit [ShapeParams] in
theorem ShapeFun.app_core (f : ShapeFun n) (x) :
    f.app x = .bot ∨ ∃ x', x' ≤ x ∧ (x', f.app x) ∈ f ∧ ∀ y ∈ f, y.1 ≤ x → y.1 ≤ x' := by
  refine let P := _; let f' := f.trunc x; (?_ :
    let y' := ((f'.find? P).getD (.bot, .bot)).2
    y' = .bot ∨ ∃ x', x' ≤ x ∧ (x', y') ∈ f ∧ ∀ y ∈ f, y.1 ≤ x → y.1 ≤ x')
  cases h : f'.find? P <;> simp
  have := List.find?_some h; simp [P, mem_trunc] at this ⊢
  have ⟨h1, h2⟩ := mem_trunc.1 <| List.mem_of_find?_eq_some h
  refine .inr ⟨_, h2, h1, this⟩

theorem ShapeFun.WF.app {f : ShapeFun n} (wf : WF Shape.WF f) (wfa : a.WF) : (ShapeFun.app f a).WF := by
  have ⟨_, _, h, _⟩ := WShape.join_prop.app_core WShape.join_prop ⟨_, wf⟩ ⟨_, wfa⟩
  exact (wf.2 _ h).2

def WShapeFun.app (f : WShapeFun n) (a : WShape n) : WShape n :=
  ⟨ShapeFun.app f.1 a.1, f.2.app a.2⟩

theorem WShapeFun.app_core (f : WShapeFun n) (x) :
    ∃ x', x' ≤ x ∧ (x', f.app x) ∈ f ∧ ∀ y ∈ f, y.1 ≤ x → y.2 ≤ f.app x := by
  have ⟨_, h1, h2, h3⟩ := WShape.join_prop.app_core WShape.join_prop f x
  exact ⟨_, h1, f.mem_val h2, fun _ a1 => h3 _ (f.mem_val a1)⟩

theorem WShapeFun.Compat.app_l {f f' : WShapeFun n} :
    f.Compat f' → ∀ x, (f.app x).Compat (f'.app x) := WShape.join_prop.compat_app_l WShape.join_prop

theorem WShape.Compat.app_r (f : WShapeFun n) :
    x.Compat x' → (f.app x).Compat (f.app x') := WShape.join_prop.compat_app_r WShape.join_prop

omit [ShapeParams] in
@[simp] theorem ShapeFun.bot_app : (@ShapeFun.bot n).app x = .bot := by
  simp [ShapeFun.bot, ShapeFun.app, ShapeFun.maxBelow, trunc]

def Shape.app : Shape (n + 1) → Shape n → Shape n
  | .lam f, x => ShapeFun.app f x
  | _, _ => .bot

omit [ShapeParams] in
@[simp] theorem Shape.bot_app : (@Shape.bot (n+1)).app x = .bot := rfl

omit [ShapeParams] in
@[simp] theorem Shape.lift_app (le : n ≤ m) :
    (app f a : Shape n).lift m = app (f.lift _) (a.lift _) := by
  cases f <;> simp [app, lift, ShapeFun.lift_app le]

def WShape.app (f : WShape (n+1)) (a : WShape n) : WShape n := by
  refine ⟨Shape.app f.1 a.1, ?_⟩
  obtain ⟨⟨⟩, wf⟩ := f <;> try exact .bot
  exact (WShapeFun.app ⟨_, wf.1⟩ _).2

@[simp] theorem WShape.bot_app {x : WShape n} : WShape.app (WShape.bot (n := n+1)) x = .bot :=
  WShape.ext (Shape.bot_app (x := x.1))

@[simp] theorem WShape.lam_app {f : WShapeFun n} {hl} {x : WShape n} :
    WShape.app (WShape.lam f hl) x = f.app x := rfl

theorem WShapeFun.app_of_mem {f : WShapeFun n} (h : (x, y) ∈ f) :
    f.app x ≤ y ∧ y ≤ f.app x :=
  have ⟨_, h1, h2, h3⟩ := f.app_core x
  ⟨f.mem_mono h2 h h1, h3 _ h .rfl⟩

theorem WShapeFun.app_eq (f : WShapeFun n) (x : WShape n) :
    ∃ x', x' ≤ x ∧ (x', f.app x) ∈ f :=
  let ⟨x', h1, h2, _⟩ := f.app_core x; ⟨x', h1, h2⟩

theorem WShapeFun.app_mono_l {f f' : WShapeFun n} (h : f ≤ f') (a : WShape n) :
    f.app a ≤ f'.app a := by
  have ⟨_, a1, a2, a3⟩ := f.app_core a
  have ⟨_, b1, b2, b3⟩ := f'.app_core a
  have ⟨_, _, c1, c2, c3⟩ := WShapeFun.LE.def'.1 h _ _ a2
  exact c3.trans <| b3 _ c1 (c2.trans a1)

theorem WShapeFun.app_mono_r {f : WShapeFun n} {a a' : WShape n} (h : a ≤ a') :
    f.app a ≤ f.app a' := by
  have ⟨_, a1, a2, a3⟩ := f.app_core a
  have ⟨_, b1, b2, b3⟩ := f.app_core a'
  exact b3 _ a2 (a1.trans h)

theorem WShape.app_mono_l {f f' : WShape (n+1)} (h : f ≤ f') (a : WShape n) :
    f.app a ≤ f'.app a := by
  change f.1 ≤ f'.1 at h; show Shape.app f.1 a.1 ≤ Shape.app f'.1 a.1
  cases hf : f.1 with | lam => ?_ | _ => exact Shape.bot_le
  let ⟨f', wf'⟩ := f'; have := hf ▸ f.2
  cases f' with rw [hf] at h | lam => ?_ | _ => exact (Shape.LE.def.1 h).elim
  exact WShapeFun.app_mono_l (f := ⟨_, (hf ▸ f.2).1⟩) (f' := ⟨_, wf'.1⟩) h _

theorem WShape.app_mono_r {f : WShape (n+1)} {a a' : WShape n} (h : a ≤ a') :
    f.app a ≤ f.app a' := by
  obtain ⟨⟨⟩, wf⟩ := f <;> try exact .rfl
  exact WShapeFun.app_mono_r (f := ⟨_, wf.1⟩) h

@[simp] theorem WShapeFun.bot_app : (WShapeFun.bot (n := n)).app x = .bot := by
  ext1; exact ShapeFun.bot_app

theorem WShapeFun.lift_app {f : WShapeFun n} {a : WShape n} (le : n ≤ m) :
    (f.app a).lift m = (f.lift m).app (a.lift m) := by
  ext1; simp [WShape.lift_val le, app, WShapeFun.lift_val le]
  exact ShapeFun.lift_app le

@[simp] theorem WShape.lift_app (le : n ≤ m) :
    (app f a : WShape n).lift m = app (f.lift _) (a.lift _) := by
  ext1; simp [lift_val le, app, Shape.lift_app le, lift_val (Nat.succ_le_succ le)]

@[simp] theorem WShape.lam'_app {f : WShapeFun n} {x : WShape n} : (lam' f).app x = f.app x := by
  simp [lam']; split <;> simp; rename_i h
  have ⟨_, h1, h2⟩ := f.app_eq x
  rw [eq_comm, ← WShape.le_bot]; exact Decidable.by_contra <| mt (⟨_, h2, ·⟩) h

theorem TShape.app_mono {f : WShape (n + 1)} {f' : WShape (m + 1)} {a : WShape n} {a' : WShape m}
    (le₁ : f.T ≤ f'.T) (le₂ : a.T ≤ a'.T) : (f.app a).T ≤ (f'.app a').T := by
  have lm₁ := Nat.le_max_left n m; have lm₂ := Nat.le_max_right n m
  rw [TShape.LE.def', WShape.lift_app lm₁, WShape.lift_app lm₂]
  refine (WShape.app_mono_l ?_ _).trans (WShape.app_mono_r le₂)
  exact (LE.def (Nat.succ_le_succ lm₁) (Nat.succ_le_succ lm₂)).1 le₁

theorem WShape.Compat.app {f f' : WShape (n+1)} {a a' : WShape n}
    (cf : f.Compat f') (ca : a.Compat a') : (f.app a).Compat (f'.app a') := by
  have ⟨zf, hf1, hf2⟩ := WShape.Compat.iff.1 cf
  have ⟨za, ha1, ha2⟩ := WShape.Compat.iff.1 ca
  exact WShape.Compat.iff.2 ⟨zf.app za,
    (WShape.app_mono_l hf1 _).trans (WShape.app_mono_r ha1),
    (WShape.app_mono_l hf2 _).trans (WShape.app_mono_r ha2)⟩

theorem TShape.Compat.app {f : WShape (n + 1)} {f' : WShape (m + 1)}
    {a : WShape n} {a' : WShape m}
    (cf : f.T.Compat f'.T) (ca : a.T.Compat a'.T) :
    (f.app a).T.Compat (f'.app a').T := by
  have le₁ := Nat.le_max_left n m; have le₂ := Nat.le_max_right n m
  rw [TShape.Compat.def le₁ le₂, WShape.lift_app le₁, WShape.lift_app le₂]
  exact WShape.Compat.app
    ((TShape.Compat.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂)).1 cf)
    ((TShape.Compat.def le₁ le₂).1 ca)

theorem WShapeFun.mem_join {f f' : WShapeFun n} {a} (hc : f.Compat f') :
    (a, b) ∈ f.join f' ↔ ∃ x ∈ f, ∃ y ∈ f', x.1.Compat y.1 ∧
      let j := x.1.join y.1; a = j ∧ b = (f.app j).join (f'.app j) := by
  simp only [WShapeFun.mem_def, WShapeFun.join_val hc, ShapeFun.mem_join]
  constructor
  · intro ⟨x, h1, y, h2, h3, h4⟩
    refine have h3' := ?_; ⟨_, f.mem_val h1, _, f'.mem_val h2, h3', ?_⟩; · exact h3
    cases a; cases b; cases h4; simp; constructor <;> ext1
    · simp [WShape.join_val h3']
    · rw [WShape.join_val (hc.app_l _)]; simp [app, WShape.join_val h3']
  · rintro ⟨x, h1, y, h2, h3, rfl, rfl⟩; refine ⟨_, h1, _, h2, h3, ?_⟩
    simp [WShape.join_val h3]; rw [WShape.join_val (hc.app_l _)]; simp [app, WShape.join_val h3]

def ShapeFun.single (x y : Shape n) : ShapeFun n :=
  (x, y) :: if x ≤ .bot then [] else [(.bot, .bot)]

omit [ShapeParams] in
theorem ShapeFun.self_mem_single : (x, y) ∈ single x y := .head _

protected theorem ShapeFun.WF.single (x y : WShape n) : WF Shape.WF (single x.1 y.1) := by
  refine ⟨?_, fun p hp => ?_⟩; rotate_left
  · simp [single] at hp
    obtain rfl | ⟨_, rfl⟩ := hp
    · exact ⟨x.2, y.2⟩
    · exact ⟨.bot, .bot⟩
  simp only [single, List.mem_cons, List.mem_ite_nil_left, List.not_mem_nil, or_false,
    exists_eq_or_imp, forall_eq_or_imp, and_imp, forall_eq_apply_imp_iff, Shape.bot_le,
    imp_self, and_true]
  have self : x.1.join x.1 ≤ x.1 ∧ x.1 ≤ x.1.join x.1 :=
    WShape.join_val .rfl ▸ (WShape.Join.iff.1 (WShape.join_self.2 ⟨.rfl, .rfl⟩)).2
  refine ⟨?_, ⟨⟨fun _ => .inl self, fun _ => .rfl⟩, ?_⟩, fun nle => ⟨fun h1 => ?_, fun h1 => ?_⟩⟩
  · obtain ⟨x, _⟩ := x; by_cases h : x ≤ .bot
    · cases Shape.le_bot.1 h; exact ⟨_, .inl rfl⟩
    · exact ⟨_, .inr ⟨h, rfl⟩⟩
  · exact (⟨by simp [Shape.join_bot, Shape.LE.rfl], ·.elim⟩)
  · simp [Shape.bot_join, Shape.LE.rfl]
  · simp [Shape.bot_join, nle]

def WShapeFun.single (x y : WShape n) : WShapeFun n :=
  ⟨ShapeFun.single x.1 y.1, .single x y⟩

omit [ShapeParams] in
theorem ShapeFun.single_app : (single x y).app x' = if x ≤ x' then y else .bot := by
  simp [single, app, trunc, maxBelow, List.find?]
  by_cases h : x ≤ x' <;> simp [h, Shape.LE.rfl]; split <;> simp

theorem WShapeFun.single_app {x y : WShape n} {x' : WShape n} :
    (WShapeFun.single x y).app x' = if x ≤ x' then y else .bot := by
  ext1; simp [WShapeFun.single, app, ShapeFun.single_app]
  split <;> simp [*, WShape.LE.def, WShape.bot]

theorem WShapeFun.mem_single {x y : WShape n} :
    a ∈ WShapeFun.single x y ↔ a = (x, y) ∨ ¬x ≤ .bot ∧ a = (.bot, .bot) := by
  cases a; simp [WShapeFun.mem_def, WShapeFun.single, ShapeFun.single,
    WShape.ext_iff, WShape.LE.def, WShape.bot]

theorem WShapeFun.single_le {f : WShapeFun n} :
    WShapeFun.single x y ≤ f ↔ ∃ x' y', (x', y') ∈ f ∧ x' ≤ x ∧ y ≤ y' := by
  simp [WShapeFun.LE.def', WShapeFun.mem_single]
  refine ⟨fun H => H _ _ (.inl ⟨rfl, rfl⟩), ?_⟩
  rintro H _ _ (⟨rfl, rfl⟩ | ⟨h4, rfl, rfl⟩)
  · exact H
  · let ⟨_, h1⟩ := f.bot_mem; exact ⟨_, _, h1, .rfl, WShape.bot_le⟩

theorem WShapeFun.lift_single (le : n ≤ m) {x y : WShape n} :
    (WShapeFun.single x y).lift m = WShapeFun.single (x.lift m) (y.lift m) := by
  ext1; simp [lift_val le, single, WShape.lift_val le, ShapeFun.single, ShapeFun.lift]
  split <;> simp [*, Shape.lift_le_bot le, ← Shape.le_bot]

theorem WShapeFun.compat_single {f : WShapeFun n} :
    Compat f (single x y) ↔ ∀ a ∈ f, a.1.Compat x → a.2.Compat y := by
  simp [WShapeFun.Compat.def, mem_single, WShape.Compat.bot_r]

omit [ShapeParams] in
theorem ShapeFun.lift_single (le : n ≤ m) {x y : Shape n} :
    lift (Shape.lift _) (ShapeFun.single x y) = (ShapeFun.single (x.lift m) (y.lift m)) := by
  simp [lift, single] <;> split <;> rename_i h <;>
    simpa [Shape.lift_le_bot le, Shape.le_bot] using h

theorem WShapeFun.Join.app_l {f g h : WShapeFun n}
    (hJ : Join f g h) (p : WShape n) : WShape.Join (f.app p) (g.app p) (h.app p) := by
  refine fun z => ⟨fun H => ⟨?_, ?_⟩, fun ⟨h1, h2⟩ => ?_⟩
  · exact (app_mono_l hJ.le.1 p).trans H
  · exact (app_mono_l hJ.le.2 p).trans H
  · refine (app_mono_l (Join.iff.1 hJ).2.2 _).trans ?_
    have ⟨x, a1, a2, a3⟩ := (f.join g).app_core p
    obtain ⟨⟨a, _⟩, b1, ⟨b, _⟩, b2, b3, rfl, b5⟩ := (WShapeFun.mem_join hJ.compat).1 a2
    have hJ' := WShape.Join.mk (hJ.compat.app_l (a.join b))
    exact b5 ▸ (hJ' _).2 ⟨(app_mono_r a1).trans h1, (app_mono_r a1).trans h2⟩

theorem WShape.rigid_join_rigid {l l' : List (WShape n)} {t t'}
    (hl : l.Forall₂ Compat l') (ht : CtsRel Compat t t') :
    (WShape.rigid c ls l t).join (.rigid c ls l' t') =
      .rigid c ls (l.zipWith join l') (ctsZip join t t') := by
  have hc : (WShape.rigid c ls l t).Compat (.rigid c ls l' t') :=
    Compat.rigid_rigid.2 ⟨rfl, rfl, hl, ht⟩
  ext1; rw [join_val hc]; simp only [rigid, Shape.join, and_self, ↓reduceIte]
  congr 1
  · clear ht hc; induction hl with | nil => rfl | cons h _ ih => simp [join_val h, ih]
  · clear hl hc; induction ht with
    | nil => rfl
    | cons h _ ih => simp only [ctsMap_cons, ctsZip_cons_cons, join_val h.2, ih]

theorem WShape.le_rigid_join {l l' : List (WShape n)} {t t'}
    (hl : l.Forall₂ Compat l') (ht : CtsRel Compat t t') :
    WShape.rigid c ls l t ≤ (WShape.rigid c ls l t).join (.rigid c ls l' t') ∧
    WShape.rigid c ls l' t' ≤ (WShape.rigid c ls l t).join (.rigid c ls l' t') :=
  (WShape.Join.mk (Compat.rigid_rigid.2 ⟨rfl, rfl, hl, ht⟩)).le

end

end Lean4Lean.ShapeModel
