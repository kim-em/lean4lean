import Lean4Lean.Theory.Typing.ShapeModel.Domain

/-!
# Shape typing

This is a port of the shape typing relation of Mario Carneiro's prototype
(`Lean4Lean/Experimental/ShapeLogRel.lean`, from `hasType.core` up to `WShape.HasDom.mono`),
over the domain of `Domain.lean`. Names and proof structure follow the prototype. The typing
relation `Shape.hasType` is structurally recursive on the depth; its clauses are:

* `bot : a` iff `a : type` (for `a` a sort, a Pi, or a rigid type former);
* `sort l : sort j` iff `¬j.IsZero`; a sort level only matters through `SLvl.IsZero`, so the
  constructor `HasTypeU.sort` types a sort at every non-zero sort, not only at `type`;
* `forallE a b : sort r` and `lam f : forallE a b` as in the prototype (`HasTypePi` now takes
  the level `r : SLvl`, and `HasTypeLam` uses `HasTypePi b a (fun _ => 1)`);
* `rigid c ls as cts : sort r` iff `(r.IsZero → famProp c ls)` and every telescope of `cts`
  is a type (`CtsTypes cts`);
* `ctor c fs : rigid I ls as cts` iff `CtsTypes cts`, `famProp I ls = false`,
  `ctorTy? c cts = some T` (the telescope of the *first* constructor named `c`), and
  `Fits fs T`.

`Fits fs T` (`hasType.fits`) types the fields along the Pi telescope `T`, at the depth of the
fields: `Fits [] T` holds, and `Fits (f :: fs) T` holds iff `T = forallE a b`, `f` is typed at
`a` lifted to the depth of `T`, and `Fits fs (b' f)` where `b'` is `b` lifted to the depth of
`T` (`Shape.unPi`). Applying the lifted codomain to `f` is the same as lifting the codomain
applied to the truncation `f.plift.1` (`ShapeFun.app_lift_plift`), so this is the
plift/truncation formulation of `PHASE1_NOTES.md` without the explicit truncation. Elements of a rigid
former that is a proposition at its levels are only `bot` (`WShape.HasType.rigid_prop`).

Deviations from the specification, with rationale:

* The `ctor` clause also requires `CtsTypes cts`, i.e. that the rigid former is a type.
  Without it `HasType.isType` (`m : a → a : type`) is false, and `Fits` would not be
  monotone in the telescope (`WShape.Fits.mono_T` needs the larger telescope to be a type,
  just as `HasType.mono_r` needs the larger type to be typed).
* The lemmas `WShape.Fits.mono_T`, `mono_l`, `join` are first proved as `*_aux`, taking the
  lower-depth `mono_r`/`mono_l`/`join` as hypotheses, because they are used inside the
  depth recursion of those typing lemmas; the plain versions are stated at the end.
* Restated for levels: `HasTypePi.toType` (to level `fun _ => 1`), `HasType.toType`,
  `HasType.retype`, and `HasType.proofIrrel` (now `r.IsZero → m : a → a : sort r → m = bot`).
  `HasType.sort` takes the non-zero proof; `HasType.sort_type` is the prototype's `sort`.
* `indTy` lemmas are replaced by `rigid` ones (`HasType.rigid`, `rigid_type`, `rigid_inv`,
  `rigid_sort_inv`, `rigid_prop`, `ctor`, `ctor'`, `*_not_rigid`).
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean

noncomputable section

variable [ShapeParams]

omit [ShapeParams] in
theorem Shape.not_isZero_type : ¬SLvl.IsZero (fun _ => 1) := SLvl.not_isZero_one

def hasType.core (hasType : Shape n → Shape n → Bool)
    (f : ShapeFun n) (a : Shape n) (G : Shape n → Shape n) : Bool :=
  f.all fun (x, y) => (f.any fun (x', y') => x' ≤ x && y ≤ y' && hasType x' a) && hasType y (G x)

/-- View a shape as a Pi telescope at its own depth: its domain and codomain function, lifted
up to the depth of the shape (`none` if the shape is not a `forallE`). -/
def Shape.unPi : ∀ {n}, Shape n → Option (Shape n × ShapeFun n)
  | _+1, .forallE a b => some (a.lift _, ShapeFun.lift (Shape.lift _) b)
  | _, _ => none

/-- `fits hasType fs T`: the fields `fs` are typed along the Pi telescope `T`: the first field
at the domain of `T`, the remaining fields along the codomain of `T` applied to the first
field. -/
def hasType.fits (hasType : Shape n → Shape n → Bool) : List (Shape n) → Shape n → Bool
  | [], _ => true
  | f :: fs, T => match T.unPi with
    | some (a, b) => hasType f a && fits hasType fs (b.app f)
    | none => false

/-- The telescope of the first constructor named `c` in a constructor table. -/
def ctorTy? (c : Name) : List (Name × α) → Option α
  | [] => none
  | (c', T) :: t => if c' = c then some T else ctorTy? c t

def Shape.hasType : ∀ {n}, Shape n → Shape n → Bool
  | _+1, .bot, .forallE a b => hasType.core hasType b a fun _ => .type
  | _+1, .bot, .rigid _ _ _ t => t.all fun p => hasType p.2 .type
  | _+1, .forallE a b, .sort r => hasType.core hasType b a fun _ => .sort r
  | 0, .bot, _ | _+1, .bot, .bot | _+1, .bot, .sort _ => true
  | 0, .sort _, .sort j | _+1, .sort _, .sort j => !decide j.IsZero
  | _+1, .lam f, .forallE a b =>
    hasType.core hasType b a (fun _ => .type) && hasType.core hasType f a (ShapeFun.app b)
  | _+1, .ctor c fs, .rigid I ls _ t =>
    (t.all fun p => hasType p.2 .type) && !ShapeParams.famProp I ls &&
      match ctorTy? c t with
      | some T => hasType.fits hasType fs T
      | none => false
  | _+1, .rigid c ls _ t, .sort r =>
    (!decide r.IsZero || ShapeParams.famProp c ls) && t.all fun p => hasType p.2 .type
  | _, _, _ => false

def Shape.HasType : Shape n → Shape n → Prop := (hasType · ·)

def Shape.HasDom (f : ShapeFun n) (a : Shape n) :=
  ∀ x y, (x, y) ∈ f → ∃ x' y', (x', y') ∈ f ∧ x' ≤ x ∧ y ≤ y' ∧ x'.HasType a

def Shape.HasTypePi (b : ShapeFun n) (a : Shape n) (r : SLvl) :=
  Shape.HasDom b a ∧ ∀ x y, (x, y) ∈ b → y.HasType (.sort r)

def Shape.HasTypeLam (f : ShapeFun n) (a : Shape n) (b : ShapeFun n) :=
  Shape.HasTypePi b a (fun _ => 1) ∧ Shape.HasDom f a ∧ ∀ x y, (x, y) ∈ f → y.HasType (b.app x)

/-- The fields `fs` are typed along the telescope `T` (see `hasType.fits`). -/
def Shape.Fits (fs : List (Shape n)) (T : Shape n) : Prop := hasType.fits hasType fs T

/-- Every telescope of a constructor table is a type. -/
def Shape.CtsTypes (t : List (Name × Shape n)) : Prop := ∀ p ∈ t, p.2.HasType .type

theorem Shape.hasType.core.iff {a : Shape n} :
    hasType.core hasType f a G ↔ HasDom f a ∧ ∀ x y, (x, y) ∈ f → y.HasType (G x) := by
  simp [hasType.core, HasDom, forall_and, HasType, and_assoc]

theorem Shape.CtsTypes.iff {t : List (Name × Shape n)} :
    (t.all fun p => hasType p.2 .type) ↔ CtsTypes t := by
  simp [CtsTypes, HasType]

omit [ShapeParams] in
@[simp] theorem Shape.unPi_zero {T : Shape 0} : T.unPi = none := rfl

omit [ShapeParams] in
theorem Shape.unPi_succ {T : Shape (n+1)} :
    T.unPi = some (a, b) ↔ ∃ a₀ b₀, T = .forallE a₀ b₀ ∧
      a = a₀.lift (n+1) ∧ b = ShapeFun.lift (Shape.lift (n+1)) b₀ := by
  cases T with
  | forallE a₀ b₀ =>
    simp only [unPi, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨_, _, rfl, rfl, rfl⟩
    · rintro ⟨_, _, h, rfl, rfl⟩; cases h; exact ⟨rfl, rfl⟩
  | _ => simp only [unPi, reduceCtorEq, false_iff, not_exists, not_and]; intro _ _ h; cases h

@[simp] theorem Shape.Fits.nil : Fits [] T := rfl

theorem Shape.Fits.cons_iff {T : Shape n} :
    Fits (f :: fs) T ↔ ∃ a b, T.unPi = some (a, b) ∧ f.HasType a ∧ Fits fs (b.app f) := by
  simp only [Fits, hasType.fits, HasType]
  cases T.unPi with
  | none => simp
  | some p =>
    obtain ⟨a, b⟩ := p; simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · intro h; exact ⟨_, _, ⟨rfl, rfl⟩, by simpa using h⟩
    · rintro ⟨_, _, ⟨rfl, rfl⟩, h⟩; simpa using h

omit [ShapeParams] in
theorem ctorTy?_mem {t : List (Name × α)} (h : ctorTy? c t = some T) : (c, T) ∈ t := by
  induction t with
  | nil => cases h
  | cons p t ih =>
    obtain ⟨c', T'⟩ := p; simp only [ctorTy?] at h; split at h
    · cases h; subst c'; exact .head _
    · exact .tail _ (ih h)

omit [ShapeParams] in
theorem ctorTy?_ctsMap {f : α → β} {t : List (Name × α)} :
    ctorTy? c (ctsMap f t) = (ctorTy? c t).map f := by
  induction t with
  | nil => rfl
  | cons p t ih => obtain ⟨c', T'⟩ := p; simp only [ctsMap_cons, ctorTy?]; split <;> simp [ih]

omit [ShapeParams] in
theorem ctorTy?_rel {R : α → β → Prop} {t : List (Name × α)} {t'} (h : CtsRel R t t')
    (e : ctorTy? c t = some T) : ∃ T', ctorTy? c t' = some T' ∧ R T T' := by
  induction h with
  | nil => cases e
  | @cons p q t t' h _ ih =>
    obtain ⟨c₁, T₁⟩ := p; obtain ⟨c₂, T₂⟩ := q; obtain ⟨rfl, h⟩ := h
    simp only [ctorTy?] at e ⊢; split at e
    · cases e; exact ⟨_, if_pos ‹_›, h⟩
    · rw [if_neg ‹_›]; exact ih e

inductive Shape.HasTypeU : ∀ {n}, Shape n → Shape n → Prop
  | bot : HasType x .type → HasTypeU .bot x
  | sort : ¬j.IsZero → HasTypeU (.sort r) (.sort j)
  | forallE : HasTypePi (n := n) b a r → HasTypeU (n := n+1) (.forallE a b) (.sort r)
  | lam : HasTypeLam (n := n) f a b → HasTypeU (n := n+1) (.lam f) (.forallE a b)
  | ctor {l : List (Shape n)} {t : List (Name × Shape n)} : CtsTypes t → ShapeParams.famProp I ls = false → ctorTy? c t = some T →
    Fits (n := n) fs T → HasTypeU (n := n+1) (.ctor c fs) (.rigid I ls l t)
  | rigid {l : List (Shape n)} {t : List (Name × Shape n)} : (r.IsZero → ShapeParams.famProp c ls = true) → CtsTypes t →
    HasTypeU (n := n+1) (.rigid c ls l t) (.sort r)

theorem Shape.HasType.unfold_iff {m a : Shape n} : HasType m a ↔ HasTypeU m a := by
  cases n with
  | zero =>
    cases m <;> cases a <;> simp [HasType, hasType] <;>
      first
      | exact .bot (by simp [HasType, hasType, SLvl.not_isZero_one])
      | (constructor
         · intro h; exact .sort h
         · intro h; cases h; assumption)
      | (intro h; cases h)
  | succ n =>
    constructor
    · intro H
      cases m <;> cases a <;> simp [HasType, hasType, hasType.core.iff] at H
      · exact .bot rfl
      · exact .bot (by simp [HasType, hasType, SLvl.not_isZero_one])
      · exact .bot (by simpa [HasType, hasType, hasType.core.iff] using H)
      · exact .bot (by simpa [HasType, hasType, SLvl.not_isZero_one] using H)
      · exact .sort H
      · exact .forallE H
      · exact .lam H
      · obtain ⟨⟨h1, h2⟩, h3⟩ := H
        split at h3
        · exact .ctor (fun p hp => h1 _ _ hp) h2 ‹_› h3
        · cases h3
      · exact .rigid (fun hz => H.1.resolve_left (fun h => h hz)) (fun p hp => H.2 _ _ hp)
    · intro H
      cases H with
      | bot h =>
        revert h; cases a <;> simp [HasType, hasType, hasType.core.iff, SLvl.not_isZero_one]
      | sort => rename_i h; simpa [HasType, hasType] using h
      | forallE h => simpa [HasType, hasType, hasType.core.iff, HasTypePi] using h
      | lam h => simpa [HasType, hasType, hasType.core.iff, HasTypeLam, HasTypePi] using h
      | ctor h1 h2 h3 h4 =>
        simp only [HasType, hasType, h2, h3, Bool.and_eq_true, List.all_eq_true]
        exact ⟨⟨fun p hp => h1 p hp, rfl⟩, h4⟩
      | rigid h1 h2 =>
        simp only [HasType, hasType, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
          Bool.not_eq_true', decide_eq_false_iff_not]
        refine ⟨?_, fun p hp => h2 p hp⟩
        rename_i r _ _
        by_cases hz : SLvl.IsZero r
        · exact .inr (h1 hz)
        · exact .inl hz

theorem Shape.HasType.unfold {m a : Shape n} : HasType m a → HasTypeU m a := unfold_iff.1

omit [ShapeParams] in
theorem Shape.unPi_lift (le : n ≤ n') {T : Shape n} :
    (T.lift n').unPi = T.unPi.map fun p => (p.1.lift n', ShapeFun.lift (lift n') p.2) := by
  cases n with
  | zero => cases n' <;> cases T <;> rfl
  | succ k =>
    obtain ⟨k', rfl⟩ : ∃ k', n' = k' + 1 := ⟨n' - 1, by omega⟩
    have le' : k ≤ k' := by omega
    cases T <;> simp [lift, unPi]
    exact ⟨by rw [lift_lift (.inl le'), lift_lift (.inl (Nat.le_succ k))],
      by rw [ShapeFun.lift_lift (.inl le'), ShapeFun.lift_lift (.inl (Nat.le_succ k))]⟩

theorem Shape.fits_lift (le : n ≤ n')
    (ih : ∀ {m a : Shape n}, hasType (m.lift n') (a.lift n') = hasType m a)
    {fs : List (Shape n)} {T : Shape n} :
    hasType.fits hasType (fs.map (lift n')) (T.lift n') = hasType.fits hasType fs T := by
  induction fs generalizing T with
  | nil => rfl
  | cons f fs ihf =>
    simp only [List.map_cons, hasType.fits, unPi_lift le]
    cases T.unPi with
    | none => rfl
    | some p =>
      obtain ⟨a, b⟩ := p; simp only [Option.map_some]; rw [ih, ← ShapeFun.lift_app le, ihf]

protected theorem Shape.HasType.lift (le : n ≤ n') :
    Shape.HasType (m.lift n') (a.lift n') ↔ Shape.HasType (n := n) m a := by
  dsimp [HasType]; rw [← Bool.eq_iff_iff]
  induction n generalizing n' with
  | zero =>
    cases n' with | zero => simp [Shape.lift_self] | succ n'
    cases m <;> cases a <;> simp [Shape.lift, hasType]
  | succ n ih =>
    let n' + 1 := n'; replace le := Nat.le_of_succ_le_succ le
    replace ih {m a} := @ih _ m a le
    have core {a : ShapeFun n} {a' : Shape n} {G G'}
        (H : ∀ x, G' (lift n' x) = lift n' (G x)) :
        hasType.core hasType (ShapeFun.lift (lift n') a) (lift n' a') G' =
        hasType.core hasType a a' G := by
      rw [Bool.eq_iff_iff]; simp [hasType.core, ShapeFun.lift, H, ih, lift_le_lift le]
    have allTy {t : List (Name × Shape n)} :
        ((ctsMap (lift n') t).all fun p => hasType p.2 type) = t.all fun p => hasType p.2 type := by
      simp only [ctsMap, List.all_map, Function.comp_def]
      congr; funext p; rw [← lift_type (n := n) (m := n'), ih]
    cases m <;> cases a <;> simp only [lift, hasType, type, allTy] <;>
      try rw [core fun _ => lift_sort.symm]
    · rw [core fun _ => (ShapeFun.lift_app le).symm]
    · rw [ctorTy?_ctsMap]; cases ctorTy? _ _ with
      | none => rfl
      | some T => simp only [Option.map_some]; rw [fits_lift le ih]

protected theorem Shape.Fits.lift (le : n ≤ n') {fs : List (Shape n)} {T : Shape n} :
    Fits (fs.map (lift n')) (T.lift n') ↔ Fits fs T := by
  unfold Fits; rw [fits_lift le fun {_ _} => Bool.eq_iff_iff.2 (HasType.lift le)]

protected theorem Shape.CtsTypes.lift (le : n ≤ n') {t : List (Name × Shape n)} :
    CtsTypes (ctsMap (lift n') t) ↔ CtsTypes t := by
  simp only [CtsTypes, mem_ctsMap]
  constructor
  · intro H p hp
    have := H _ ⟨_, hp, rfl⟩; rw [← lift_type (n := n) (m := n')] at this
    exact (HasType.lift le).1 this
  · rintro H _ ⟨p, hp, rfl⟩; exact lift_type (n := n) ▸ (HasType.lift le).2 (H _ hp)

protected theorem Shape.HasDom.lift (le : n ≤ n') :
    HasDom (ShapeFun.lift (lift n') m) (a.lift n') ↔ HasDom (n := n) m a := by
  simp only [HasDom, ShapeFun.lift, List.mem_map, Prod.mk.injEq]
  constructor <;> [intro H x y h; rintro H x y ⟨_, h, rfl, rfl⟩]
  · obtain ⟨_, _, ⟨_, h1, rfl, rfl⟩, h2, h3, h4⟩ := H _ _ ⟨_, h, rfl, rfl⟩
    exact ⟨_, _, h1, (Shape.lift_le_lift le).1 h2,
      (Shape.lift_le_lift le).1 h3, (Shape.HasType.lift le).1 h4⟩
  · have ⟨_, _, h1, h2, h3, h4⟩ := H _ _ h
    exact ⟨_, _, ⟨_, h1, rfl, rfl⟩, Shape.lift_mono h2,
      Shape.lift_mono h3, (Shape.HasType.lift le).2 h4⟩

protected theorem Shape.HasTypePi.lift (le : n ≤ n') :
    HasTypePi (ShapeFun.lift (lift n') m) (a.lift n') r ↔ HasTypePi (n := n) m a r := by
  simp only [HasTypePi]
  exact and_congr (HasDom.lift le) <| by
    simp only [ShapeFun.lift, List.mem_map, Prod.mk.injEq]
    constructor <;> [intro H x y h; rintro H _ _ ⟨⟨x, y⟩, h, rfl, rfl⟩]
    · exact (Shape.HasType.lift le).1 (Shape.lift_sort.symm ▸ H _ _ ⟨_, h, rfl, rfl⟩)
    · exact Shape.lift_sort ▸ (Shape.HasType.lift le).2 (H _ _ h)

theorem Shape.HasTypeLam.lift (le : n ≤ n') :
    HasTypeLam (ShapeFun.lift (lift n') f) (a.lift n') (ShapeFun.lift (lift n') b) ↔
    HasTypeLam (n := n) f a b := by
  simp only [HasTypeLam]
  refine and_congr (HasTypePi.lift le) <| and_congr (HasDom.lift le) ⟨?_, ?_⟩ <;> intro H x y h
  · have h' : (x.lift n', y.lift n') ∈ ShapeFun.lift (Shape.lift n') f :=
      List.mem_map.2 ⟨_, h, rfl⟩
    have := H _ _ h'
    rw [← ShapeFun.lift_app le] at this
    exact (Shape.HasType.lift le).1 this
  · obtain ⟨⟨x₀, y₀⟩, h₀, heq⟩ := List.mem_map.1 h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    rw [← ShapeFun.lift_app le]
    exact (Shape.HasType.lift le).2 (H _ _ h₀)

protected theorem Shape.HasType.bot {a : Shape n} (H : HasType a .type) : HasType .bot a :=
  unfold_iff.2 (.bot H)
protected theorem Shape.HasType.sort (h : ¬j.IsZero) : HasType (n := n) (.sort r) (.sort j) :=
  unfold_iff.2 (.sort h)
protected theorem Shape.HasType.sort_type : HasType (n := n) (.sort r) .type :=
  .sort SLvl.not_isZero_one
protected theorem Shape.HasType.forallE (H : HasTypePi (n := n) b a r) :
    HasType (n := n+1) (.forallE a b) (.sort r) := unfold_iff.2 (.forallE H)
protected theorem Shape.HasType.lam (H : HasTypeLam (n := n) f a b) :
    HasType (n := n+1) (.lam f) (.forallE a b) := unfold_iff.2 (.lam H)
protected theorem Shape.HasType.ctor {l : List (Shape n)} {t : List (Name × Shape n)}
    (h1 : CtsTypes t) (h2 : ShapeParams.famProp I ls = false) (h3 : ctorTy? c t = some T)
    (h4 : Fits fs T) : HasType (n := n+1) (.ctor c fs) (.rigid I ls l t) :=
  unfold_iff.2 (.ctor h1 h2 h3 h4)
protected theorem Shape.HasType.rigid {l : List (Shape n)} {t : List (Name × Shape n)}
    (h1 : r.IsZero → ShapeParams.famProp c ls = true) (h2 : CtsTypes t) :
    HasType (n := n+1) (.rigid c ls l t) (.sort r) := unfold_iff.2 (.rigid h1 h2)
protected theorem Shape.HasType.rigid_type {l : List (Shape n)} {t : List (Name × Shape n)}
    (h : CtsTypes t) : HasType (n := n+1) (.rigid c ls l t) .type :=
  .rigid (fun h => absurd h SLvl.not_isZero_one) h

theorem Shape.HasType.bot_r (H : HasType (n := n) x .bot) : x = .bot := by
  cases n <;> cases x <;> simp [HasType, hasType, bot] at H ⊢

theorem Shape.HasType.toType {m : Shape n} (H : HasType m (.sort r)) : HasType m .type := by
  induction n generalizing r with
  | zero =>
    cases H.unfold with
    | bot => exact .bot .sort_type
    | sort => exact .sort_type
  | succ n ih =>
    cases H.unfold with
    | bot => exact .bot .sort_type
    | sort => exact .sort_type
    | forallE h => exact .forallE ⟨h.1, fun _ _ h3 => ih (h.2 _ _ h3)⟩
    | rigid _ h2 => exact .rigid_type h2

theorem Shape.HasType.isType (H : HasType m a) : a.HasType .type := by
  cases H.unfold with
  | bot H => exact H
  | sort | forallE | rigid => exact .sort_type
  | lam H' => exact .forallE H'.1
  | ctor h1 => exact .rigid_type h1

theorem Shape.HasTypePi.toType (H : HasTypePi b a r) : HasTypePi b a (fun _ => 1) :=
  ⟨H.1, fun _ _ h => (H.2 _ _ h).toType⟩

def WShape.HasType (m a : WShape n) : Prop := Shape.HasType m.1 a.1
def WShape.HasDom (f : WShapeFun n) (a : WShape n) := Shape.HasDom f.1 a.1
def WShape.HasTypePi (b : WShapeFun n) (a : WShape n) := Shape.HasTypePi b.1 a.1
def WShape.HasTypeLam (f : WShapeFun n) (a : WShape n) (b : WShapeFun n) :=
  Shape.HasTypeLam f.1 a.1 b.1
/-- The fields `fs` are typed along the telescope `T` (see `hasType.fits`). -/
def WShape.Fits (fs : List (WShape n)) (T : WShape n) : Prop := Shape.Fits (fs.map (·.1)) T.1
/-- Every telescope of a constructor table is a type. -/
def WShape.CtsTypes (t : List (Name × WShape n)) : Prop := ∀ p ∈ t, p.2.HasType .type

theorem WShape.HasDom.def : HasDom f a ↔
    ∀ x y, (x, y) ∈ f → ∃ x' y', (x', y') ∈ f ∧ x' ≤ x ∧ y ≤ y' ∧ x'.HasType a :=
  ⟨fun H _ _ h => have ⟨_, _, h1, h2⟩ := H _ _ h; ⟨_, _, f.mem_val h1, h2⟩,
   fun H _ _ h => have ⟨_, _, h1, h2⟩ := H _ _ (f.mem_val h); ⟨_, _, h1, h2⟩⟩

theorem WShape.HasTypePi.def {b : WShapeFun n} :
    HasTypePi b a r ↔ HasDom b a ∧ ∀ x y, (x, y) ∈ b → y.HasType (.sort r) :=
  and_congr_right' ⟨fun H _ _ h => H _ _ h, fun H _ _ h => H _ _ (b.mem_val h)⟩

theorem WShape.HasTypeLam.def {f : WShapeFun n} {a b} :
    HasTypeLam f a b ↔ HasTypePi b a (fun _ => 1) ∧ HasDom f a ∧
      ∀ x y, (x, y) ∈ f → y.HasType (b.app x) :=
  and_congr_right' <| and_congr_right' ⟨fun H _ _ h => H _ _ h, fun H _ _ h => H _ _ (f.mem_val h)⟩

theorem WShape.CtsTypes.val {t : List (Name × WShape n)} :
    CtsTypes t ↔ Shape.CtsTypes (ctsMap (·.1) t) := by
  simp only [CtsTypes, Shape.CtsTypes, mem_ctsMap]
  exact ⟨fun H _ ⟨p, hp, e⟩ => e ▸ H p hp, fun H p hp => H _ ⟨p, hp, rfl⟩⟩

theorem WShape.HasDom.lift (le : n ≤ m) :
    HasDom (f.lift m) (a.lift m) ↔ HasDom (n := n) f a := by
  simp only [HasDom, Shape.HasDom, WShapeFun.lift_val le, ShapeFun.lift, List.mem_map,
    Prod.mk.injEq, WShape.lift_val le]
  constructor <;> [intro H x y h; rintro H x y ⟨_, h, rfl, rfl⟩]
  · obtain ⟨_, _, ⟨_, h1, rfl, rfl⟩, h2, h3, h4⟩ := H _ _ ⟨_, h, rfl, rfl⟩
    exact ⟨_, _, h1, (Shape.lift_le_lift le).1 h2,
      (Shape.lift_le_lift le).1 h3, (Shape.HasType.lift le).1 h4⟩
  · have ⟨_, _, h1, h2, h3, h4⟩ := H _ _ h
    exact ⟨_, _, ⟨_, h1, rfl, rfl⟩, Shape.lift_mono h2,
      Shape.lift_mono h3, (Shape.HasType.lift le).2 h4⟩

theorem WShape.HasType.toType : HasType (n := n) x (.sort r) → HasType x .type :=
  Shape.HasType.toType

theorem WShape.HasType.isType : HasType m a → a.HasType .type := Shape.HasType.isType

theorem WShape.HasDom.isType (H : WShape.HasDom f a) : a.HasType .type := by
  have ⟨_, h⟩ := f.bot_mem
  have ⟨_, _, _, h2, _, h4⟩ := HasDom.def.1 H _ _ h
  cases le_bot.1 h2; exact h4.isType

theorem WShape.HasType.lift (h : n ≤ n') :
    HasType (m.lift n') (a.lift n') ↔ HasType (n := n) m a := by
  simp only [HasType, lift_val h]; exact Shape.HasType.lift h

theorem WShape.HasTypePi.lift (le : n ≤ m) :
    HasTypePi (b.lift m) (a.lift m) r ↔ HasTypePi (n := n) b a r := by
  simp only [HasTypePi, WShapeFun.lift_val le, WShape.lift_val le]
  exact Shape.HasTypePi.lift le

theorem WShape.HasTypeLam.lift (le : n ≤ m) :
    HasTypeLam (f.lift m) (a.lift m) (b.lift m) ↔
    HasTypeLam (n := n) f a b := by
  simp only [HasTypeLam, WShapeFun.lift_val le, WShape.lift_val le]
  exact Shape.HasTypeLam.lift le

theorem WShape.HasTypePi.app_sort {b : WShapeFun n} (H : HasTypePi b a r) (x : WShape n) :
    (b.app x).HasType (.sort r) :=
  have ⟨_, _, h⟩ := b.app_eq x; (HasTypePi.def.1 H).2 _ _ h

theorem WShape.HasType.forallE_sort_inv {a : WShape n} {b : WShapeFun n}
    (H : HasType (.forallE a b) (.sort r)) : HasTypePi b a r := by
  unfold HasType at H; cases H.unfold with | forallE h => exact h

theorem WShape.HasType.rigid_sort_inv {l : List (WShape n)} {t}
    (H : HasType (.rigid c ls l t) (.sort r)) :
    (r.IsZero → ShapeParams.famProp c ls = true) ∧ CtsTypes t := by
  unfold HasType at H; cases H.unfold with | rigid h1 h2 => exact ⟨h1, CtsTypes.val.2 h2⟩

/-! ### Fitting fields to a telescope -/

@[simp] theorem WShape.Fits.nil {T : WShape n} : Fits [] T := rfl

theorem WShape.Fits.of_raw {fs : List (Shape n)} (wf : ∀ f ∈ fs, f.WF) {T : WShape n} :
    Fits (fs.pmap Subtype.mk wf) T ↔ Shape.Fits fs T.1 := by
  simp only [Fits]; rw [List.map_pmap, List.pmap_eq_map, List.map_id']

theorem WShape.Fits.cons_zero {T : WShape 0} : ¬Fits (f :: fs) T := by
  simp [Fits, Shape.Fits.cons_iff]

theorem WShape.Fits.forallE_iff {a : WShape k} {b : WShapeFun k} {f : WShape (k+1)} :
    Fits (f :: fs) (.forallE a b) ↔ f.HasType (a.lift (k+1)) ∧ Fits fs ((b.lift (k+1)).app f) := by
  simp only [Fits, List.map_cons, Shape.Fits.cons_iff, forallE, Shape.unPi, Option.some.injEq,
    Prod.mk.injEq, HasType, lift_val (Nat.le_succ k), WShapeFun.app,
    WShapeFun.lift_val (Nat.le_succ k)]
  constructor
  · rintro ⟨_, _, ⟨rfl, rfl⟩, h1, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨_, _, ⟨rfl, rfl⟩, h1, h2⟩

theorem WShape.Fits.cons_inv {T : WShape (k+1)} (H : Fits (f :: fs) T) :
    ∃ a b, T = .forallE a b ∧ f.HasType (a.lift (k+1)) ∧ Fits fs ((b.lift (k+1)).app f) := by
  cases T using WShape.casesOn' with
  | forallE a b => exact ⟨a, b, rfl, forallE_iff.1 H⟩
  | _ => simp [Fits, Shape.Fits.cons_iff, Shape.unPi, bot, sort, lam, ctor, rigid, Shape.bot,
      Shape.sort] at H

theorem WShape.Fits.lift (le : n ≤ m) {fs : List (WShape n)} {T : WShape n} :
    Fits (fs.map (.lift m)) (T.lift m) ↔ Fits fs T := by
  simp only [Fits, List.map_map, Function.comp_def, lift_val le]
  have := Shape.Fits.lift le (fs := fs.map (·.1)) (T := T.1)
  simpa [List.map_map, Function.comp_def] using this

theorem WShape.Fits.mono_T_aux
    (ih : ∀ {m a a' : WShape n} {r}, a ≤ a' → a'.HasType (.sort r) → m.HasType a → m.HasType a')
    {fs : List (WShape n)} {T T' : WShape n} (le : T ≤ T') (hT' : T'.HasType .type)
    (H : Fits fs T) : Fits fs T' := by
  induction fs generalizing T T' with
  | nil => exact .nil
  | cons f fs ihf =>
    cases n with
    | zero => exact absurd H cons_zero
    | succ k =>
      obtain ⟨a, b, rfl, h1, h2⟩ := cons_inv H
      obtain ⟨a', b', l1, l2, rfl⟩ := forallE_le.1 le
      have hpi := HasType.forallE_sort_inv hT'
      have hpi' := (HasTypePi.lift (Nat.le_succ k)).2 hpi
      refine forallE_iff.2 ⟨ih (r := fun _ => 1) (lift_mono (Nat.le_succ k) l1) ?_ h1, ?_⟩
      · have := (HasType.lift (Nat.le_succ k)).2 (HasDom.isType (HasTypePi.def.1 hpi).1)
        rwa [lift_type] at this
      · exact ihf (WShapeFun.app_mono_l (WShapeFun.lift_mono (Nat.le_succ k) l2) _)
          (hpi'.app_sort _) h2

theorem WShape.Fits.mono_l_aux
    (ih_l : ∀ {m m' a : WShape n}, m ≤ m' → m' ≤ m → HasType m a → HasType m' a)
    (ih_r : ∀ {m a a' : WShape n} {r}, a ≤ a' → a'.HasType (.sort r) → m.HasType a →
      m.HasType a')
    {fs fs' : List (WShape n)} (h1 : fs.Forall₂ (· ≤ ·) fs') (h2 : fs'.Forall₂ (· ≤ ·) fs)
    {T : WShape n} (hT : T.HasType .type) (H : Fits fs T) : Fits fs' T := by
  induction h1 generalizing T with
  | nil => exact .nil
  | @cons f f' fs fs' l1 _ ihf =>
    cases h2 with | cons l2 h2 =>
    cases n with
    | zero => exact absurd H cons_zero
    | succ k =>
      obtain ⟨a, b, rfl, a1, a2⟩ := cons_inv H
      have hpi := (HasTypePi.lift (Nat.le_succ k)).2 (HasType.forallE_sort_inv hT)
      refine forallE_iff.2 ⟨ih_l l1 l2 a1, ?_⟩
      exact mono_T_aux ih_r (WShapeFun.app_mono_r l1) (hpi.app_sort _)
        (ihf h2 (hpi.app_sort _) a2)

theorem WShape.HasType.mono_r {m a a' : WShape n} (ha : a ≤ a')
    (Ha : HasType a' (.sort r)) (H : HasType m a) : HasType m a' := by
  have ⟨m, mwf⟩ := m; have ⟨a, awf⟩ := a; have ⟨a', awf'⟩ := a'
  simp only [HasType, sort, WShape.LE.def] at *
  cases H.unfold with
  | bot H => exact .bot Ha.toType
  | sort | forallE | rigid => cases Shape.sort_le.1 ha; exact H
  | ctor h1 h2 h3 h4 =>
    obtain ⟨l', t', rfl, -, ht⟩ := Shape.rigid_le.1 ha
    have ⟨T', e', hTT'⟩ := ctorTy?_rel ht h3
    have hct' : Shape.CtsTypes t' := by cases Ha.unfold with | rigid _ h => exact h
    refine .ctor hct' h2 e' ?_
    have wT := awf.2 _ (ctorTy?_mem h3); have wT' := awf'.2 _ (ctorTy?_mem e')
    refine (Fits.of_raw mwf.1 (T := ⟨_, wT'⟩)).1 ?_
    exact Fits.mono_T_aux (fun {_ _ _ _} => WShape.HasType.mono_r) (T := ⟨_, wT⟩) hTT'
      (hct' _ (ctorTy?_mem e')) ((Fits.of_raw mwf.1).2 h4)
  | @lam n _ _ _ H' =>
    obtain ⟨_, _, h1, h2, ⟨⟩⟩ := Shape.forallE_le.1 ha
    let .forallE Ha := Ha.unfold
    have ih := @WShape.HasType.mono_r n
    let rec ih_dom {f : WShapeFun n} {a a' r} (ha : a ≤ a') (Ha : HasType a' (.sort r))
        (H : HasDom (n := n) f a) : HasDom f a' := by
      rw [WShape.HasDom.def] at H ⊢; intro _ _ h
      have ⟨_, _, h1, h2, h3, h4⟩ := H _ _ h
      exact ⟨_, _, h1, h2, h3, ih ha Ha h4⟩
    let rec ih_lam {f : WShapeFun n} {a a' b b'} (Ha : HasTypePi b' a' r)
        (ha : a ≤ a') (hb : b ≤ b') (H : HasTypeLam f a b) : HasTypeLam f a' b' := by
      rw [HasTypeLam.def] at H ⊢
      have ht := (HasTypePi.def.1 Ha).1.isType
      refine ⟨Ha.toType, ih_dom ha ht H.2.1, fun x y h => ?_⟩
      have ⟨_, h1, h2⟩ := b'.app_eq x
      exact .mono_r (WShapeFun.app_mono_l hb _) ((HasTypePi.def.1 Ha).2 _ _ h2) (H.2.2 _ _ h)
    exact .lam (ih_lam (f := ⟨_, mwf.1⟩) (a := ⟨_, awf.1⟩)
      (a' := ⟨_, awf'.1⟩) (b := ⟨_, awf.2⟩) (b' := ⟨_, awf'.2⟩) Ha h1 h2 H')

theorem WShape.HasDom.mono_r {f : WShapeFun n} {a a' r} :
    a ≤ a' → HasType a' (.sort r) → HasDom f a → HasDom f a' := HasType.mono_r.ih_dom HasType.mono_r

theorem WShape.HasTypeLam.mono_r {f : WShapeFun n} {a a' b b'} :
    HasTypePi b' a' r → a ≤ a' → b ≤ b' → HasTypeLam f a b → HasTypeLam f a' b' :=
  HasType.mono_r.ih_lam HasType.mono_r

omit [ShapeParams] in
theorem forall₂_pmap_subtype {P : α → Prop} {R : α → α → Prop} {l l' : List α}
    (wf : ∀ x ∈ l, P x) (wf' : ∀ x ∈ l', P x) (h : List.Forall₂ R l l') :
    List.Forall₂ (fun a b : Subtype P => R a.1 b.1) (l.pmap Subtype.mk wf) (l'.pmap Subtype.mk wf') := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons h (ih _ _)

omit [ShapeParams] in
private theorem find_cycle (R : α → α → Prop)
    (trans : ∀ {x y z}, R x y → R y z → R x z) (l : List α)
    (H : ∀ x ∈ l, ∃ y ∈ l, R x y) : ∀ x ∈ l, ∃ y ∈ l, R x y ∧ R y y := by
  intro x h
  suffices ∀ l₁ l₂, l.Perm (l₁ ++ l₂) → (∀ y ∈ l₂, ∀ z ∈ l, R x z → R y z) →
      ∃ y ∈ l, R x y ∧ R y y from this l [] (by simp) nofun
  intro l₁; generalize eq : l₁.length = i; revert x l₁
  refine i.strongRecOn ?_; rintro i ih x₀ h₀ l₁ rfl l₂ he hl
  have ⟨x', a1, a2⟩ := H x₀ h₀
  obtain hm | hm := List.mem_append.1 (he.mem_iff.1 a1)
  · have ⟨l', hp⟩ := List.perm_cons_of_mem hm
    have he' := he.trans (.append_right _ hp) |>.trans List.perm_middle.symm
    refine have ⟨_, c1, c2, c3⟩ := ih l'.length ?_ _ a1 _ rfl _ he' ?_; ⟨_, c1, trans a2 c2, c3⟩
    · rw [hp.length_eq]; apply Nat.lt_succ_self
    · rintro x' (⟨⟩ | ⟨_, hx⟩) z hz hr <;> [exact hr; exact hl _ hx _ hz (trans a2 hr)]
  · exact ⟨_, a1, a2, hl _ hm _ a1 a2⟩

namespace WShape.HasType.mono_l
variable (ih : ∀ {m m' a : WShape n}, m ≤ m' → m' ≤ m → HasType m a → HasType m' a)
include ih

theorem ih_dom {f f' : WShapeFun n} (hf1 : f ≤ f') (hf2 : f' ≤ f)
    (H : HasDom f a) : HasDom f' a := by
  rw [HasDom.def] at H ⊢; intro x y h
  have ⟨z, h1, ⟨c, c1, c2, c3, _⟩, d, d1, d2, _, d4⟩ := find_cycle ?_ f'.1 ?_ _ h
    (R := fun x y => ∃ z : WShape n, y.1 ≤ z.1 ∧ z.1 ≤ x.1 ∧ x.2 ≤ y.2 ∧ z.HasType a)
  · exact ⟨_, _, f'.mem_val h1, c1.trans c2, c3, ih d2 d1 d4⟩
  · rintro x y z ⟨_, a1, a2, a3, a4⟩ ⟨_, b1, b2, b3, b4⟩
    exact ⟨_, b1, b2.trans (a1.trans a2), a3.trans b3, b4⟩
  · rintro x h
    have ⟨x₁, y₁, a1, a2, a3⟩ := WShapeFun.LE.def'.1 hf2 _ _ (f'.mem_val h)
    have ⟨x₂, y₂, b1, b2, b3, b4⟩ := H _ _ a1
    have ⟨x₃, y₃, c1, c2, c3⟩ := WShapeFun.LE.def'.1 hf1 _ _ b1
    exact ⟨_, c1, _, c2, b2.trans a2, a3.trans (b3.trans c3), b4⟩

theorem ih_pi {b b'} {a a' : WShape n}
    (hb1 : b ≤ b') (hb2 : b' ≤ b) (ha1 : a ≤ a') (ha2 : a' ≤ a)
    (H : HasTypePi b a r) : HasTypePi b' a' r := by
  rw [HasTypePi.def] at H ⊢
  refine ⟨ih_dom ih hb1 hb2 H.1 |>.mono_r ha1 (ih ha1 ha2 H.1.isType), fun x y h => ?_⟩
  have ⟨x₁, y₁, a1, a2, a3⟩ := WShapeFun.LE.def'.1 hb2 _ _ h
  have ⟨x₂, y₂, b1, b2, b3⟩ := WShapeFun.LE.def'.1 hb1 _ _ a1
  have ⟨_, c1, c2⟩ := b.app_eq x
  exact ih (b3.trans <| b'.mem_mono b1 h (b2.trans a2)) a3 (H.2 _ _ a1)

theorem ih_lam {f f' : WShapeFun n} (hf1 : f ≤ f') (hf2 : f' ≤ f)
    (H : HasTypeLam f a b) : HasTypeLam f' a b := by
  rw [HasTypeLam.def] at H ⊢; refine ⟨H.1, ih_dom ih hf1 hf2 H.2.1, fun x y h => ?_⟩
  have ⟨x₁, y₁, a1, a2, a3⟩ := WShapeFun.LE.def'.1 hf2 _ _ h
  have ⟨x₂, y₂, b1, b2, b3⟩ := WShapeFun.LE.def'.1 hf1 _ _ a1
  have ⟨_, c1, c2⟩ := b.app_eq x
  refine .mono_r (b.app_mono_r a2) ((HasTypePi.def.1 H.1).2 _ _ c2) ?_
  exact ih (b3.trans <| f'.mem_mono b1 h (b2.trans a2)) a3 (H.2.2 _ _ a1)

end WShape.HasType.mono_l

theorem WShape.HasType.mono_l {m m' a : WShape n}
    (hm1 : m ≤ m') (hm2 : m' ≤ m) (H : HasType m a) : HasType m' a := by
  have ⟨m, mwf⟩ := m; have ⟨m', mwf'⟩ := m'; have ⟨a, awf⟩ := a
  simp only [HasType, WShape.LE.def] at *
  cases H.unfold with
  | bot => cases Shape.le_bot.1 hm2; exact H
  | sort => cases Shape.sort_le.1 hm1; exact H
  | forallE H' =>
    obtain ⟨_, _, a1, a2, ⟨⟩⟩ := Shape.forallE_le.1 hm1
    have ⟨b1, b2⟩ := Shape.forallE_le_forallE.1 hm2
    exact .forallE <| mono_l.ih_pi mono_l (b := ⟨_, mwf.2⟩) (b' := ⟨_, mwf'.2⟩)
      (a := ⟨_, mwf.1⟩) (a' := ⟨_, mwf'.1⟩) a2 b2 a1 b1 H'
  | lam H' =>
    obtain ⟨_, a1, ⟨⟩⟩ := Shape.lam_le.1 hm1; have b1 := Shape.lam_le_lam.1 hm2
    exact .lam <| mono_l.ih_lam mono_l (f := ⟨_, mwf.1⟩) (f' := ⟨_, mwf'.1⟩)
      (a := ⟨_, awf.1⟩) (b := ⟨_, awf.2⟩) hm1 hm2 H'
  | ctor h1 h2 h3 h4 =>
    cases m' with
    | ctor c' fs' =>
      obtain ⟨rfl, l1⟩ := Shape.LE.def.1 hm1; obtain ⟨-, l2⟩ := Shape.LE.def.1 hm2
      refine .ctor h1 h2 h3 ?_
      have wT := awf.2 _ (ctorTy?_mem h3)
      refine (Fits.of_raw mwf'.1 (T := ⟨_, wT⟩)).1 ?_
      exact Fits.mono_l_aux (fun {_ _ _} => WShape.HasType.mono_l)
        (fun {_ _ _ _} => WShape.HasType.mono_r) (forall₂_pmap_subtype _ _ l1)
        (forall₂_pmap_subtype _ _ l2) (h1 _ (ctorTy?_mem h3)) ((Fits.of_raw mwf.1).2 h4)
    | _ => simp [Shape.LE.def] at hm1
  | rigid h1 h2 =>
    obtain ⟨l', t', rfl, -, ht1⟩ := Shape.rigid_le.1 hm1
    obtain ⟨-, -, -, ht2⟩ := Shape.rigid_le_rigid.1 hm2
    refine .rigid h1 fun p hp => ?_
    have := List.Forall₂.and_mem (List.Forall₂.and ht1 (CtsRel.flip ht2))
    obtain ⟨q, hq, ⟨⟨-, l1⟩, -, l2⟩, hq', -⟩ := List.Forall₂.forall_exists_r this p hp
    exact WShape.HasType.mono_l (m := ⟨_, mwf.2 _ hq'⟩) (m' := ⟨_, mwf'.2 _ hp⟩)
      (a := WShape.type) l1 l2 (h2 _ hq')

theorem WShape.HasDom.mono_l {f f' : WShapeFun n} : f ≤ f' → f' ≤ f →
    HasDom f a → HasDom f' a := WShape.HasType.mono_l.ih_dom WShape.HasType.mono_l
theorem WShape.HasTypePi.mono_l {a a' : WShape n} : b ≤ b' → b' ≤ b → a ≤ a' → a' ≤ a →
    HasTypePi b a r → HasTypePi b' a' r := WShape.HasType.mono_l.ih_pi WShape.HasType.mono_l
theorem WShape.HasTypeLam.mono_l {f f' : WShapeFun n} : f ≤ f' → f' ≤ f →
    HasTypeLam f a b → HasTypeLam f' a b := WShape.HasType.mono_l.ih_lam WShape.HasType.mono_l

theorem WShape.HasDom.iff {f : WShapeFun n} :
    HasDom f a ↔ ∀ x, ∃ x', x' ≤ x ∧ x'.HasType a ∧ f.app x ≤ f.app x' := by
  refine WShape.HasDom.def.trans ⟨fun H x => ?_, fun H x₀ y₀ h₀ => ?_⟩
  · have ⟨x', a1, a2⟩ := WShapeFun.app_eq f x
    have ⟨x₂, y₂, b1, b2, b3, b4⟩ := H _ _ a2
    exact ⟨_, b2.trans a1, b4, .trans b3 (f.app_of_mem b1).2⟩
  · have ⟨z, h1, ⟨c, c1, c2, c3, _⟩, d, d1, d2, _, d4⟩ := find_cycle ?_ f.1 ?_ _ h₀
      (R := fun x y => ∃ z : WShape n, y.1 ≤ z.1 ∧ z.1 ≤ x.1 ∧ x.2 ≤ y.2 ∧ z.HasType a)
    · exact ⟨_, _, f.mem_val h1, c1.trans c2, c3, d4.mono_l d2 d1⟩
    · rintro x y z ⟨_, a1, a2, a3, a4⟩ ⟨_, b1, b2, b3, b4⟩
      exact ⟨_, b1, b2.trans (a1.trans a2), a3.trans b3, b4⟩
    · rintro x h
      have ⟨x', a1, a2, a3⟩ := H ⟨_, (f.2.2 _ h).1⟩
      have ⟨x₁, b1, b2⟩ := f.app_eq x'
      exact ⟨_, b2, _, b1, a1, (f.app_of_mem (f.mem_val h)).2.trans a3, a2⟩

theorem WShape.HasTypePi.iff {b : WShapeFun n} :
    HasTypePi b a rel ↔ HasDom b a ∧ ∀ x, x.HasType a → (b.app x).HasType (.sort rel) := by
  refine WShape.HasTypePi.def.trans <| and_congr_right fun hd =>
    ⟨fun H x h => ?_, fun H x y h => ?_⟩
  · have ⟨_, h1, h2⟩ := b.app_eq x; exact H _ _ h2
  · have ⟨h1, h2⟩ := b.app_of_mem h
    have ⟨x', a1, a2, a3⟩ := HasDom.iff.1 hd x
    exact (H _ a2).mono_l (b.app_mono_r a1 |>.trans h1) (h2.trans a3)

theorem WShape.HasTypePi.iff' {b : WShapeFun n} :
    HasTypePi b a rel ↔ HasDom b a ∧ ∀ x, (b.app x).HasType (.sort rel) := by
  refine WShape.HasTypePi.iff.trans <| and_congr_right fun h1 => ⟨fun H x => ?_, fun H _ _ => H _⟩
  have ⟨x', a1, a2, a3⟩ := HasDom.iff.1 h1 x
  exact (H _ a2).mono_l (WShapeFun.app_mono_r a1) a3

theorem WShape.HasTypeLam.iff {f : WShapeFun n} {a b} :
    HasTypeLam f a b ↔ HasTypePi b a (fun _ => 1) ∧ HasDom f a ∧
      ∀ x, x.HasType a → (f.app x).HasType (b.app x) := by
  refine WShape.HasTypeLam.def.trans <| and_congr_right fun hp => and_congr_right fun hd =>
    ⟨fun H x h => ?_, fun H x y h => ?_⟩
  · have ⟨_, h1, h2⟩ := f.app_eq x
    exact .mono_r (b.app_mono_r h1) ((WShape.HasTypePi.iff.1 hp).2 _ h) <| H _ _ h2
  · have ⟨h1, h2⟩ := f.app_of_mem h
    have ⟨x', a1, a2, a3⟩ := HasDom.iff.1 hd x
    have ⟨x₂, b1, b2, b3⟩ := HasDom.iff.1 hp.1 x
    exact .mono_r (b.app_mono_r a1)
      ((WShape.HasTypePi.iff.1 hp).2 _ b2 |>.mono_l (b.app_mono_r b1) b3)
      ((H _ a2).mono_l (.trans (f.app_mono_r a1) h1) (h2.trans a3))

theorem WShape.HasTypeLam.iff' {b : WShapeFun n} :
    HasTypeLam f a b ↔ HasTypePi b a (fun _ => 1) ∧ HasDom f a ∧ ∀ x, (f.app x).HasType (b.app x) := by
  refine WShape.HasTypeLam.iff.trans <| and_congr_right fun h1 => and_congr_right fun h2 =>
    ⟨fun H x => ?_, fun H _ _ => H _⟩
  have ⟨x', a1, a2, a3⟩ := HasDom.iff.1 h2 x
  have := (H _ a2).mono_l (WShapeFun.app_mono_r a1) a3
  exact ((HasTypePi.iff'.1 h1).2 _).mono_r (WShapeFun.app_mono_r a1) this


inductive WShape.HasTypeU : ∀ {n}, WShape n → WShape n → Prop
  | bot : HasType x .type → HasTypeU .bot x
  | sort : ¬j.IsZero → HasTypeU (.sort r) (.sort j)
  | forallE : HasTypePi (n := n) b a r → HasTypeU (n := n+1) (.forallE a b) (.sort r)
  | lam : HasTypeLam (n := n) f a b → HasTypeU (n := n+1) (.lam' f) (.forallE a b)
  | ctor {l : List (WShape n)} {t : List (Name × WShape n)} {T : WShape n}
    {fs : List (WShape n)} {wf} : CtsTypes t →
    ShapeParams.famProp I ls = false → ctorTy? c t = some T → Fits fs T →
    HasTypeU (n := n+1) (.ctor c fs wf) (.rigid I ls l t)
  | rigid {l : List (WShape n)} {t : List (Name × WShape n)} :
    (r.IsZero → ShapeParams.famProp c ls = true) → CtsTypes t →
    HasTypeU (n := n+1) (.rigid c ls l t) (.sort r)

theorem ctorTy?_ctsAttach {t : List (Name × Shape n)} {H} (h : ctorTy? c t = some T) :
    ∃ hT, ctorTy? c (ctsAttach t H) = some ⟨T, hT⟩ := by
  have := ctorTy?_ctsMap (f := (·.1)) (c := c) (t := ctsAttach t H)
  rw [ctsMap_ctsAttach, h] at this
  cases e : ctorTy? c (ctsAttach t H) with
  | none => rw [e] at this; cases this
  | some T' => rw [e] at this; cases Option.some.inj this; exact ⟨T'.2, rfl⟩

theorem WShape.HasType.unfold {m a : WShape n} (H : HasType m a) : HasTypeU m a := by
  let ⟨m, mwf⟩ := m; let ⟨a, awf⟩ := a
  dsimp only [HasType] at H
  cases H.unfold with
  | bot h => exact .bot h
  | sort h => exact .sort h
  | forallE h => exact .forallE (a := ⟨_, mwf.1⟩) (b := ⟨_, mwf.2⟩) h
  | lam h =>
    have := HasTypeU.lam (f := ⟨_, mwf.1⟩) (a := ⟨_, awf.1⟩) (b := ⟨_, awf.2⟩) h
    rwa [lam', dif_pos (by exact mwf.2)] at this
  | ctor h1 h2 h3 h4 =>
    have ⟨_, e⟩ := ctorTy?_ctsAttach (H := awf.2) h3
    have := HasTypeU.ctor (l := List.pmap Subtype.mk _ awf.1) (wf := (WShape.mk_ctor _ mwf).1)
      (CtsTypes.val.2 (by rwa [ctsMap_ctsAttach])) h2 e ((Fits.of_raw mwf.1).2 h4)
    rwa [(WShape.mk_ctor _ mwf).2, WShape.mk_rigid] at this
  | rigid h1 h2 =>
    have := HasTypeU.rigid (l := List.pmap Subtype.mk _ mwf.1) h1
      (CtsTypes.val.2 (by rwa [ctsMap_ctsAttach (H := mwf.2)]))
    rwa [WShape.mk_rigid] at this

theorem WShape.HasType.unfold_iff {m a : WShape n} : HasType m a ↔ HasTypeU m a := by
  refine ⟨(·.unfold), fun h => ?_⟩
  cases h with
  | bot h => exact .bot h
  | sort h => exact .sort h
  | forallE h => exact .forallE h
  | @lam _ f a b h => unfold lam'; split <;> [exact .lam h; exact .bot (.forallE h.1)]
  | ctor h1 h2 h3 h4 =>
    exact Shape.HasType.ctor (CtsTypes.val.1 h1) h2 (by rw [ctorTy?_ctsMap, h3]; rfl) h4
  | rigid h1 h2 => exact Shape.HasType.rigid h1 (CtsTypes.val.1 h2)

theorem WShape.HasType.bot' : HasType (n := n) x .type → HasType .bot x :=
  (unfold_iff.2 <| .bot ·)
theorem WShape.HasType.sort (h : ¬j.IsZero) : HasType (n := n) (.sort r) (.sort j) :=
  unfold_iff.2 (.sort h)
theorem WShape.HasType.sort_type : HasType (n := n) (.sort r) .type := .sort SLvl.not_isZero_one
theorem WShape.HasType.forallE : HasTypePi (n := n) b a r →
    HasType (n := n+1) (.forallE a b) (.sort r) := (unfold_iff.2 <| .forallE ·)
theorem WShape.HasType.lam : HasTypeLam (n := n) f a b →
    HasType (n := n+1) (.lam' f) (.forallE a b) := (unfold_iff.2 <| .lam ·)
theorem WShape.HasType.rigid {l : List (WShape n)} {t}
    (h1 : r.IsZero → ShapeParams.famProp c ls = true) (h2 : CtsTypes t) :
    HasType (n := n+1) (.rigid c ls l t) (.sort r) := unfold_iff.2 (.rigid h1 h2)
theorem WShape.HasType.rigid_type {l : List (WShape n)} {t} (h : CtsTypes t) :
    HasType (n := n+1) (.rigid c ls l t) .type := .rigid (fun h => absurd h SLvl.not_isZero_one) h
theorem WShape.HasType.ctor {l : List (WShape n)} {t} {T : WShape n} {fs : List (WShape n)} {wf}
    (h1 : CtsTypes t)
    (h2 : ShapeParams.famProp I ls = false) (h3 : ctorTy? c t = some T) (h4 : Fits fs T) :
    HasType (.ctor c fs wf) (.rigid I ls l t) := unfold_iff.2 (.ctor h1 h2 h3 h4)
theorem WShape.HasType.ctor' {l : List (WShape n)} {t} {T : WShape n} {fs : List (WShape n)}
    (h1 : CtsTypes t)
    (h2 : ShapeParams.famProp I ls = false) (h3 : ctorTy? c t = some T) (h4 : Fits fs T) :
    HasType (.ctor' c fs) (.rigid I ls l t) := by
  unfold WShape.ctor'; split <;> [exact .ctor h1 h2 h3 h4; exact bot' (.rigid_type h1)]

theorem WShape.HasTypePi.toType (H : HasTypePi (n := n) b a r) :
    HasTypePi (n := n) b a (fun _ => 1) :=
  ⟨H.1, fun _ _ h' => (H.2 _ _ h').toType⟩

theorem WShape.HasType.lam_isType {f : WShapeFun n} {hf} :
    ¬HasType (WShape.lam f hf) (.sort r) := nofun
theorem WShape.HasType.ctor_isType {c : Name} {l : List (WShape n)} {h} :
    ¬HasType (n := n+1) (WShape.ctor c l h) (.sort r) := nofun
theorem WShape.HasType.sort_not_forallE {a : WShape n} {f : WShapeFun n} :
    ¬HasType (n := n+1) (.sort r) (.forallE a f) := nofun
theorem WShape.HasType.forallE_not_forallE {a a' : WShape n} {f f' : WShapeFun n} :
    ¬HasType (n := n+1) (.forallE a f) (.forallE a' f') := nofun
theorem WShape.HasType.ctor_not_forallE {c l h a} {f : WShapeFun n} :
    ¬HasType (n := n+1) (WShape.ctor c l h) (.forallE a f) := nofun
theorem WShape.HasType.rigid_not_forallE {l : List (WShape n)} {t a} {f : WShapeFun n} :
    ¬HasType (n := n+1) (WShape.rigid c ls l t) (.forallE a f) := nofun
theorem WShape.HasType.sort_not_rigid {l : List (WShape n)} {t} :
    ¬HasType (n := n+1) (.sort r) (WShape.rigid c ls l t) := nofun
theorem WShape.HasType.forallE_not_rigid {a : WShape n} {f : WShapeFun n} {l t} :
    ¬HasType (n := n+1) (.forallE a f) (WShape.rigid c ls l t) := nofun
theorem WShape.HasType.rigid_not_rigid {l l' : List (WShape n)} {t t'} :
    ¬HasType (n := n+1) (WShape.rigid c ls l t) (WShape.rigid c' ls' l' t') := nofun
theorem WShape.HasType.lam_not_rigid {f : WShapeFun n} {hf} {l t} :
    ¬HasType (n := n+1) (WShape.lam f hf) (WShape.rigid c ls l t) := nofun

theorem WShape.HasType.bot : HasType (n := n) x (.sort r) → HasType .bot x := (.bot' ·.toType)

theorem WShape.HasType.bot_r (H : HasType (n := n) x .bot) : x = .bot := by
  cases n <;> cases H.unfold <;> rfl

theorem WShape.HasType.bot_iff : HasType (n := n) .bot x ↔ HasType x .type := ⟨.isType, .bot'⟩

theorem WShape.HasDom.bot_iff {a : WShape n} : HasDom .bot a ↔ a.HasType .type := by
  simp [HasDom.def, WShapeFun.mem_bot, HasType.bot_iff]

theorem WShape.HasDom.bot : a.HasType .type → HasDom .bot a := bot_iff.2

theorem WShape.HasTypeLam.bot {b : WShapeFun n} :
    HasTypeLam .bot a b ↔ HasTypePi b a (fun _ => 1) := by
  simp only [HasTypeLam.def, WShapeFun.mem_bot, and_imp, forall_eq_apply_imp_iff,
    forall_eq, and_iff_left_iff_imp]
  exact fun h => ⟨.bot (HasDom.isType h.1), .bot' ((HasTypePi.iff'.1 h).2 _)⟩

theorem WShape.HasType.forallE_l {a : WShape n} {f : WShapeFun n} :
    HasType (.forallE a f) t ↔ ∃ r, HasTypePi f a r ∧ t = .sort r := by
  simp only [HasType, WShape.forallE, HasTypePi, WShape.sort,
    WShape.ext_iff, Shape.HasType.unfold_iff]
  generalize a.1 = a₁, f.1 = f₁, t.1 = t₁
  refine ⟨fun (.forallE H) => ⟨_, H, rfl⟩, fun ⟨_, H, eq⟩ => eq ▸ .forallE H⟩

theorem WShape.HasType.forallE_inv {m : WShape (n+1)} {a : WShape n} {f : WShapeFun n}
    (H : HasType m (.forallE a f)) : ∃ g, m = .lam' g ∧ HasTypeLam g a f := by
  generalize eq : a.forallE f = a' at H
  cases H.unfold with
  | bot H' =>
    refine ⟨.bot, by simp, ?_⟩; subst eq
    obtain ⟨_, H, ⟨⟩⟩ := HasType.forallE_l.1 H'
    simp [HasTypeLam.def, WShapeFun.mem_bot, HasDom.def]
    have ⟨h1, h2⟩ := HasTypePi.iff.1 H
    exact have := .bot h1.isType; ⟨H, this, .bot (h2 _ this)⟩
  | lam H' => obtain ⟨rfl, rfl⟩ := forallE.inj.1 eq; exact ⟨_, rfl, H'⟩
  | _ => cases congrArg (·.1) eq

/-- Inversion for typing at a rigid type former. -/
theorem WShape.HasType.rigid_inv {m : WShape (n+1)} {l : List (WShape n)} {t}
    (H : HasType m (.rigid I ls l t)) :
    CtsTypes t ∧ (m = .bot ∨ ∃ c fs wf T, m = .ctor c fs wf ∧
      ShapeParams.famProp I ls = false ∧ ctorTy? c t = some T ∧ Fits fs T) := by
  generalize eq : WShape.rigid I ls l t = a' at H
  cases H.unfold with
  | bot H' => subst eq; exact ⟨(rigid_sort_inv H').2, .inl rfl⟩
  | ctor h1 h2 h3 h4 =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := rigid.inj.1 eq
    exact ⟨h1, .inr ⟨_, _, _, _, rfl, h2, h3, h4⟩⟩
  | _ => cases congrArg (·.1) eq

omit [ShapeParams] in
theorem pmap_subtype_val {P : α → Prop} {l : List α} (wf : ∀ x ∈ l, P x) :
    (l.pmap Subtype.mk wf).map (·.1) = l := by rw [List.map_pmap, List.pmap_eq_map, List.map_id']

theorem WShape.map_val_zipWith_join {l l' : List (WShape n)} (h : l.Forall₂ Compat l') :
    (l.zipWith join l').map (·.1) = (l.map (·.1)).zipWith Shape.join (l'.map (·.1)) := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp [join_val h, ih]

/-- Fitting is closed under joins of compatible field lists. -/
theorem WShape.Fits.join_aux
    (ih_j : ∀ {m₁ m₂ a : WShape n}, m₁.Compat m₂ → m₁.HasType a → m₂.HasType a →
      (m₁.join m₂).HasType a)
    {fs₁ fs₂ : List (WShape n)} (hc : fs₁.Forall₂ Compat fs₂)
    {T : WShape n} (hT : T.HasType .type) (h1 : Fits fs₁ T) (h2 : Fits fs₂ T) :
    Fits (fs₁.zipWith WShape.join fs₂) T := by
  induction hc generalizing T with
  | nil => exact .nil
  | @cons f₁ f₂ fs₁ fs₂ hf _ ihf =>
    cases n with
    | zero => exact absurd h1 cons_zero
    | succ k =>
      obtain ⟨a, b, rfl, a1, a2⟩ := cons_inv h1
      obtain ⟨_, _, e, b1, b2⟩ := cons_inv h2
      obtain ⟨rfl, rfl⟩ := forallE.inj.1 e
      have hpi := (HasTypePi.lift (Nat.le_succ k)).2 (HasType.forallE_sort_inv hT)
      have hJ := (WShape.Join.mk hf).le
      rw [List.zipWith_cons_cons]
      refine forallE_iff.2 ⟨ih_j hf a1 b1, ihf (hpi.app_sort _) ?_ ?_⟩
      · exact mono_T_aux (fun {_ _ _ _} => HasType.mono_r) (WShapeFun.app_mono_r hJ.1)
          (hpi.app_sort _) a2
      · exact mono_T_aux (fun {_ _ _ _} => HasType.mono_r) (WShapeFun.app_mono_r hJ.2)
          (hpi.app_sort _) b2

theorem WShape.Fits.zipWith_join_raw {fs₁ fs₂ : List (Shape n)} (wf₁ : ∀ x ∈ fs₁, x.WF)
    (wf₂ : ∀ x ∈ fs₂, x.WF) (hc : List.Forall₂ (fun a b => a.Compat b = true) fs₁ fs₂)
    {T : WShape n}
    (H : Fits (List.zipWith WShape.join (fs₁.pmap Subtype.mk wf₁) (fs₂.pmap Subtype.mk wf₂)) T) :
    Shape.Fits (List.zipWith Shape.join fs₁ fs₂) T.1 := by
  unfold Fits at H
  rw [map_val_zipWith_join (forall₂_pmap_subtype _ _ hc)] at H
  simpa only [List.map_pmap, List.pmap_eq_map, List.map_id'] using H

theorem Shape.CtsTypes.join
    (ih : ∀ {x y : WShape n}, x.Compat y → x.HasType .type → y.HasType .type →
      (x.join y).HasType .type)
    {t t' : List (Name × Shape n)} (wf : ∀ p ∈ t, p.2.WF) (wf' : ∀ p ∈ t', p.2.WF)
    (hc : CtsRel (fun a b => a.Compat b = true) t t') (h1 : CtsTypes t) (h2 : CtsTypes t') :
    CtsTypes (ctsZip Shape.join t t') := by
  induction t generalizing t' with
  | nil => cases hc; intro _ h; cases h
  | cons p t ihc =>
    cases hc with | cons hp hc =>
    simp only [List.forall_mem_cons] at wf wf'
    intro q hq
    simp only [ctsZip_cons_cons, List.mem_cons] at hq
    rcases hq with rfl | hq
    · have := ih (x := ⟨_, wf.1⟩) (y := ⟨_, wf'.1⟩) hp.2 (h1 _ (.head _)) (h2 _ (.head _))
      rwa [WShape.HasType, WShape.join_val (a := ⟨_, wf.1⟩) (b := ⟨_, wf'.1⟩) hp.2] at this
    · exact ihc wf.2 wf'.2 hc (fun p h => h1 p (.tail _ h)) (fun p h => h2 p (.tail _ h)) _ hq

theorem WShape.HasType.join {m₁ m₂ a : WShape n} (hJ : m₁.Compat m₂)
    (h1 : m₁.HasType a) (h2 : m₂.HasType a) : (m₁.join m₂).HasType a := by
  obtain ⟨m₁, wf₁⟩ := m₁; obtain ⟨m₂, wf₂⟩ := m₂; obtain ⟨a, wf'⟩ := a
  simp [HasType, WShape.join_val hJ, Compat] at h1 h2 hJ ⊢
  cases n with
  | zero =>
    cases m₂ with | bot => exact h1 | sort
    cases m₁ with | bot => exact h2 | sort
    simp only [Shape.Compat, decide_eq_true_eq] at hJ
    simpa only [Shape.join, hJ]
  | succ n
  have ih := @join n
  let rec go_dom {a a' : WShape n} {f f' : WShapeFun n}
      (hf : f.Compat f') (ha : a.Compat a')
      (h1 : WShape.HasDom f a) (h2 : WShape.HasDom f' a') :
      WShape.HasDom (f.join f') (a.join a') := by
    rw [WShape.HasDom.iff] at h1 h2 ⊢
    have hJa := WShape.Join.mk ha
    have hJf := WShapeFun.Join.mk hf
    intro x
    have ⟨x₁, a1, a2, a3⟩ := h1 x
    have ⟨x₂, b1, b2, b3⟩ := h2 x
    have hcx := Compat.iff.2 ⟨_, a1, b1⟩; have hjx := WShape.Join.mk hcx
    have ajt := ih ha a2.isType b2.isType
    have := ih hcx (.mono_r hJa.le.1 ajt a2) (.mono_r hJa.le.2 ajt b2)
    refine ⟨_, (hjx _).2 ⟨a1, b1⟩, this, ?_⟩
    refine (hJf.app_l x _).2 ⟨a3.trans ?_, b3.trans ?_⟩
    · exact (WShapeFun.app_mono_r hjx.le.1).trans (hJf.app_l _).le.1
    · exact (WShapeFun.app_mono_r hjx.le.2).trans (hJf.app_l _).le.2
  let rec go_pi {a a' : WShape n} {b b' : WShapeFun n} {r}
      (ha : a.Compat a') (hb : b.Compat b')
      (h1 : WShape.HasTypePi b a r) (h2 : WShape.HasTypePi b' a' r) :
      WShape.HasTypePi (b.join b') (a.join a') r := by
    rw [WShape.HasTypePi.iff'] at h1 h2 ⊢
    have hJa := WShape.Join.mk ha
    have hJb := WShapeFun.Join.mk hb
    refine ⟨go_dom hb ha h1.1 h2.1, fun x => ?_⟩
    have ⟨a1, a2, a3⟩ := Join.iff.1 (hJb.app_l x)
    exact ih a1 (h1.2 _) (h2.2 _) |>.mono_l a2 a3
  let rec go_lam {f f' : WShapeFun n} {a b} (hf : f.Compat f')
      (h1 : WShape.HasTypeLam f a b) (h2 : WShape.HasTypeLam f' a b) :
      WShape.HasTypeLam (f.join f') a b := by
    rw [WShape.HasTypeLam.iff'] at h1 h2 ⊢
    have := Join.iff.1 <| (join_self (x := a)).2 ⟨.rfl, .rfl⟩
    refine ⟨h1.1, go_dom hf .rfl h1.2.1 h2.2.1 |>.mono_r this.2.1 h1.2.1.isType, fun x => ?_⟩
    have hJf := WShapeFun.Join.mk hf
    have ⟨a1, a2, a3⟩ := Join.iff.1 (hJf.app_l x)
    exact ih a1 (h1.2.2 _) (h2.2.2 _) |>.mono_l a2 a3
  cases h1.unfold with
  | bot => exact h2
  | sort =>
    (cases m₂ with | bot => exact h1 | _) <;>
      simp only [Shape.Compat, decide_eq_true_eq, Bool.false_eq_true] at hJ
    simpa only [Shape.join, hJ]
  | forallE h1' =>
    (cases h2.unfold with | bot => exact h1 | forallE h2' | _) <;>
      simp only [Shape.Compat, Bool.false_eq_true, Bool.and_eq_true] at hJ
    have := go_pi (b := ⟨_, wf₁.2⟩) (b' := ⟨_, wf₂.2⟩)
      (a := ⟨_, wf₁.1⟩) (a' := ⟨_, wf₂.1⟩) hJ.1 hJ.2 h1' h2'
    rw [HasTypePi, WShape.join_val (by exact hJ.1), WShapeFun.join_val (by exact hJ.2)] at this
    exact .forallE this
  | lam h1' =>
    (cases h2.unfold with | bot => exact h1 | lam h2' | _) <;> simp only [Shape.Compat] at hJ
    have := go_lam (f := ⟨_, wf₁.1⟩) (f' := ⟨_, wf₂.1⟩)
      (a := ⟨_, wf'.1⟩) (b := ⟨_, wf'.2⟩) hJ h1' h2'
    rw [HasTypeLam, WShapeFun.join_val (by exact hJ)] at this
    exact .lam this
  | ctor h1' h2' h3' h4' =>
    (cases h2.unfold with | bot => exact h1 | ctor k1 k2 k3 k4 | _) <;>
      simp only [Shape.Compat, Bool.and_eq_true, decide_eq_true_eq] at hJ
    obtain ⟨rfl, hc⟩ := hJ
    rw [h3'] at k3; cases k3
    simp only [Shape.join, ↓reduceIte]
    refine .ctor h1' h2' h3' ?_
    have wT := wf'.2 _ (ctorTy?_mem h3')
    have hc' := forall₂_pmap_subtype wf₁.1 wf₂.1 hc
    have := Fits.join_aux (fun {_ _ _} => WShape.HasType.join) hc' (T := ⟨_, wT⟩)
      (h1' _ (ctorTy?_mem h3')) ((Fits.of_raw wf₁.1).2 h4') ((Fits.of_raw wf₂.1).2 k4)
    exact WShape.Fits.zipWith_join_raw _ _ hc this
  | rigid h1' h2' =>
    (cases h2.unfold with | bot => exact h1 | rigid k1 k2 | _) <;>
      simp only [Shape.Compat, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at hJ
    obtain ⟨⟨⟨rfl, rfl⟩, -⟩, ht⟩ := hJ
    simp only [Shape.join, and_self, ↓reduceIte]
    exact .rigid h1' (Shape.CtsTypes.join (fun {_ _} => WShape.HasType.join) wf₁.2 wf₂.2 ht h2' k2)

theorem WShape.HasDom.join {a a' : WShape n} {f f' : WShapeFun n} :
    f.Compat f' → a.Compat a' → HasDom f a → HasDom f' a' →
    HasDom (f.join f') (a.join a') := HasType.join.go_dom _ HasType.join
theorem WShape.HasTypePi.join {a a' : WShape n} {b b' : WShapeFun n} {r} :
    a.Compat a' → b.Compat b' → HasTypePi b a r → HasTypePi b' a' r →
    WShape.HasTypePi (b.join b') (a.join a') r := HasType.join.go_pi _ HasType.join
theorem WShape.HasTypeLam.join {f f' : WShapeFun n} {a b} :
    f.Compat f' → HasTypeLam f a b → HasTypeLam f' a b →
    WShape.HasTypeLam (f.join f') a b := HasType.join.go_lam _ HasType.join

theorem WShape.HasType.join' {m₁ m₂ m a : WShape n} (hJ : m₁.Join m₂ m)
    (h1 : m₁.HasType a) (h2 : m₂.HasType a) : m.HasType a :=
  have ⟨a1, a2, a3⟩ := Join.iff.1 hJ
  h1.join a1 h2 |>.mono_l a2 a3

theorem WShape.HasDom.join' (h1 : HasDom f₁ a₁) (h2 : HasDom f₂ a₂)
    (hJ : WShapeFun.Join f₁ f₂ h') (hJa : WShape.Join a₁ a₂ a') : HasDom h' a' := by
  have ⟨a1, a2, a3⟩ := WShapeFun.Join.iff.1 hJ
  have ⟨b1, b2, b3⟩ := WShape.Join.iff.1 hJa
  have := h1.join a1 b1 h2 |>.mono_l a2 a3
  exact this.mono_r b2 <| this.isType.mono_l b2 b3

def TShape.HasType (x y : TShape) : Prop := (x.2.lift (max x.1 y.1)).HasType (y.2.lift _)

theorem TShape.HasType.def {x y : TShape} (h1 : x.1 ≤ m) (h2 : y.1 ≤ m) :
    x.HasType y ↔ (x.2.lift m).HasType (y.2.lift m) := by
  refine (WShape.HasType.lift (Nat.max_le.2 ⟨h1, h2⟩)).symm.trans ?_
  rw [WShape.lift_lift (.inl (Nat.le_max_left ..)), WShape.lift_lift (.inl (Nat.le_max_right ..))]

theorem WShape.HasType.T_iff {x y : WShape n} : x.T.HasType y.T ↔ x.HasType y := by
  refine (TShape.HasType.def (x := x.T) (y := y.T) (Nat.le_refl _) (Nat.le_refl _)).trans ?_
  simp [WShape.HasType, WShape.lift_self]

theorem WShape.HasType.T {x y : WShape n} : x.HasType y → x.T.HasType y.T := T_iff.2

theorem TShape.HasType.bot_r (H : HasType x .bot) : x ≤ .bot := by
  simp only [TShape.HasType, bot, WShape.lift_bot] at H
  have h := WShape.HasType.bot_r H
  simp only [TShape.LE.def', bot, WShape.lift_bot]
  exact (h : x.2.lift _ = .bot) ▸ WShape.LE.rfl

theorem TShape.HasType.mono_r {m a a' : TShape} (ha : a ≤ a')
    (h1 : HasType a' (.sort r)) (h2 : HasType m a) : HasType m a' := by
  let k := max (max m.1 a.1) a'.1
  have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
  have h1 := (TShape.HasType.def hk.2 (Nat.zero_le _)).1 h1
  have h2 := (TShape.HasType.def hk.1.1 hk.1.2).1 h2
  have ha := (TShape.LE.def hk.1.2 hk.2).1 ha
  exact (TShape.HasType.def hk.1.1 hk.2).2 (h1.mono_r ha h2)

theorem TShape.HasType.bot : HasType x (.sort r) → HasType .bot x := by
  rw [TShape.HasType.def (Nat.le_refl _) (Nat.zero_le _),
    TShape.HasType.def (Nat.zero_le _) (Nat.le_refl _)]
  simp [sort]; exact .bot

theorem TShape.HasType.bot' : HasType x .type → HasType .bot x := .bot

theorem TShape.HasType.sort : HasType (.sort r) .type := by
  simp [HasType, TShape.sort, TShape.type, WShape.lift_sort, WShape.HasType]
  exact WShape.HasType.sort_type

theorem TShape.HasType.join' (hJ : Join m₁ m₂ m)
    (h1 : HasType m₁ a) (h2 : HasType m₂ a) : HasType m a := by
  let k := max (max m₁.1 m₂.1) (max m.1 a.1)
  have hk := Nat.max_le.1 (Nat.le_refl k); simp only [Nat.max_le] at hk
  have h1 := (TShape.HasType.def hk.1.1 hk.2.2).1 h1
  have h2 := (TShape.HasType.def hk.1.2 hk.2.2).1 h2
  have hJ := (TShape.Join.def hk.1.1 hk.1.2 hk.2.1).1 hJ
  exact (TShape.HasType.def hk.2.1 hk.2.2).2 (h1.join' hJ h2)

theorem TShape.HasType.bot_r' (ha : a ≤ .bot) (H : HasType x a) : x ≤ .bot :=
  (mono_r (r := fun _ => 1) ha (.bot' .sort) H).bot_r

nonrec theorem TShape.HasType.isType (H : HasType m a) : a.HasType .type :=
  let k := max m.1 a.1; have hk := Nat.max_le.1 (Nat.le_refl k)
  (TShape.HasType.def hk.2 (Nat.zero_le _)).2 H.isType

inductive LE_Forall {n} : TShape → WShape n → WShapeFun n → Prop where
  | bot : a ≤ .bot → LE_Forall a b f
  | forallE : b'.T ≤ b.T → TShapeFun.LE (n := m) f' f →
    LE_Forall (WShape.T (n := m+1) (.forallE b' f')) b f

theorem TShape.LE.le_forall (ha : a ≤ WShape.T (n := n+1) (.forallE b f)) :
    LE_Forall a b f := by
  by_cases h : a ≤ .bot; · exact .bot h
  obtain ⟨an, aw⟩ := a
  cases an with
  | zero =>
    exfalso; apply h; rw [TShape.le_bot]
    have hle := (TShape.LE.def (Nat.zero_le _) (Nat.le_refl _)).1 ha
    have hle_raw : (aw.lift _).1 ≤ ((WShape.forallE b f).lift _).1 := hle
    rw [WShape.lift_val (Nat.zero_le _), WShape.lift_val (Nat.le_refl _)] at hle_raw
    obtain ⟨val, wf⟩ := aw
    cases val with | bot => rfl | sort r
    simp [Shape.lift, WShape.forallE, Shape.LE.def] at hle_raw
  | succ m =>
    have hle := (TShape.LE.def (Nat.succ_le_succ (Nat.le_max_left m n))
        (Nat.succ_le_succ (Nat.le_max_right m n))).1 ha
    have hle_raw : (aw.lift _).1 ≤ ((WShape.forallE b f).lift _).1 := hle
    rw [WShape.lift_val (Nat.succ_le_succ (Nat.le_max_left m n)),
        WShape.lift_val (Nat.succ_le_succ (Nat.le_max_right m n))] at hle_raw
    simp only [WShape.forallE, Shape.lift] at hle_raw
    obtain ⟨val, wf⟩ := aw
    cases val with
    | bot => exfalso; apply h; rw [TShape.le_bot]; rfl
    | forallE b' f' =>
      simp [Shape.lift, Shape.LE.def] at hle_raw
      let b'w : WShape m := ⟨b', wf.1⟩; let f'w : WShapeFun m := ⟨f', wf.2⟩
      have le₁ := Nat.le_max_left m n; have le₂ := Nat.le_max_right m n
      refine .forallE
        ((TShape.LE.def le₁ le₂).2 (?_ : (b'w.lift _).1 ≤ (b.lift _).1))
        ((TShapeFun.LE.def le₁ le₂).2 (?_ : (f'w.lift _).1.LE (f.lift _).1))
      · rw [WShape.lift_val le₁, WShape.lift_val le₂]; exact hle_raw.1
      · rw [WShapeFun.lift_val le₁, WShapeFun.lift_val le₂]; exact hle_raw.2
    | _ => simp [Shape.lift, Shape.LE.def] at hle_raw

def TShape.HasTypeLam (f : WShapeFun n) (a : WShape m) (b : WShapeFun m) :=
  WShape.HasTypeLam (f.lift (max n m)) (a.lift (max n m)) (b.lift (max n m))

theorem TShape.HasTypeLam.def (le₁ : n ≤ k) (le₂ : m ≤ k) :
    HasTypeLam (n := n) (m := m) f a b ↔
    WShape.HasTypeLam (f.lift k) (a.lift k) (b.lift k) := by
  rw [TShape.HasTypeLam, ← WShape.HasTypeLam.lift (Nat.max_le.2 ⟨le₁, le₂⟩),
    WShapeFun.lift_lift (.inl (Nat.le_max_left ..)), WShape.lift_lift (.inl (Nat.le_max_right ..)),
    WShapeFun.lift_lift (.inl (Nat.le_max_right ..))]

theorem TShape.HasType.ty_forallE_inv
    {x : TShape} (H : x.HasType (WShape.T (n := m+1) (.forallE b f))) :
    x = .bot ∨ ∃ n g, x = WShape.T (n := n+1) (.lam' g) ∧ TShape.HasTypeLam g b f := by
  refine have le₁ := Nat.le_succ_of_le (Nat.le_max_left ..)
    have le₂ := Nat.succ_le_succ (Nat.le_max_right ..)
    have H := (TShape.HasType.def le₁ le₂).1 H; ?_
  rw [WShape.lift_forallE (Nat.le_of_succ_le_succ le₂)] at H
  have ⟨g, hg, htl⟩ := WShape.HasType.forallE_inv H
  obtain ⟨_|n, x⟩ := x
  · unfold WShape.lam' at hg; split at hg
    · obtain ⟨⟨⟩, _⟩ := x <;> cases congrArg (·.1) hg
    · dsimp at le₁; cases (WShape.lift_eq_bot le₁).1 hg; exact .inl rfl
  refine .inr ⟨n, ?_⟩; dsimp at *
  obtain ⟨rfl, h⟩ | ⟨g, rfl, rfl⟩ := WShape.lift_eq_lam' (Nat.le_of_succ_le_succ le₁) hg
  · refine ⟨.bot, by simp, ?_⟩
    rw [HasTypeLam, WShapeFun.lift_bot, ← WShapeFun.lift_bot,
      WShape.HasTypeLam.lift (Nat.le_max_right ..), WShape.HasTypeLam.bot]
    obtain ⟨_, h, _⟩ := WShape.HasType.forallE_l.1 <| WShape.HasType.bot_iff.1 H
    exact (WShape.HasTypePi.lift (Nat.le_of_succ_le_succ le₂)).1 h |>.toType
  · exact ⟨_, rfl, (HasTypeLam.def (by omega) (by omega)).2 htl⟩

theorem TShape.HasType.mono_l {m a : TShape}
    (hm1 : m ≤ m') (hm2 : m' ≤ m) (H : HasType m a) : HasType m' a := by
  let k := max (max m.1 a.1) m'.1
  have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
  have H := (TShape.HasType.def hk.1.1 hk.1.2).1 H
  have hm1 := (TShape.LE.def hk.1.1 hk.2).1 hm1
  have hm2 := (TShape.LE.def hk.2 hk.1.1).1 hm2
  exact (TShape.HasType.def hk.2 hk.1.2).2 (H.mono_l hm1 hm2)

theorem TShape.HasType.sort_T : HasType (WShape.T (n := n) (.sort r)) .type :=
  mono_l TShape.sort_eqv.2 TShape.sort_eqv.1 .sort

theorem TShape.HasType.sort_r {x : WShape n} : x.T.HasType (.sort r) ↔ x.HasType (.sort r) :=
  .trans ⟨mono_r TShape.sort_eqv.2 .sort_T, mono_r TShape.sort_eqv.1 .sort⟩ WShape.HasType.T_iff

theorem TShape.HasType.bot_T (H : HasType x (.sort r)) : HasType (WShape.T (n := n) .bot) x :=
  H.bot.mono_l bot_eqv.2 bot_eqv.1
theorem TShape.HasType.bot_T' (H : HasType x .type) : HasType (WShape.T (n := n) .bot) x := H.bot_T

theorem TShape.HasType.join {m₁ m₂ a : TShape} (hJ : m₁.Compat m₂)
    (h1 : m₁.HasType a) (h2 : m₂.HasType a) : (m₁.join m₂).HasType a := by
  let k := max (max m₁.1 m₂.1) a.1
  have hk := Nat.max_le.1 (Nat.le_refl k); simp only [Nat.max_le] at hk
  have h1 := (TShape.HasType.def hk.1.1 hk.2).1 h1
  have h2 := (TShape.HasType.def hk.1.2 hk.2).1 h2
  have hJ := (TShape.Compat.def hk.1.1 hk.1.2).1 hJ
  have := TShape.lift_join hk.1.1 hk.1.2 ▸ h1.join hJ h2
  exact (TShape.HasType.def (Nat.max_le.2 hk.1) hk.2).1 this

theorem WShape.HasType.proofIrrel (hr : r.IsZero)
    (ha : HasType (n := n) a (.sort r)) (hx : HasType x a) : x = .bot := by
  cases n with
  | zero =>
    cases ha.unfold with
    | bot => exact hx.bot_r
    | sort h => exact absurd hr h
  | succ n
  cases ha.unfold with
  | bot => exact hx.bot_r
  | sort h => exact absurd hr h
  | rigid h1 h2 =>
    obtain ⟨-, rfl | ⟨_, _, _, _, rfl, h3, -⟩⟩ := rigid_inv hx
    · rfl
    · rw [h1 hr] at h3; cases h3
  | @forallE _ b a _ ha
  generalize eq : WShape.forallE .. = t at hx
  cases hx.unfold with | bot => rfl | @lam _ f a' b' hx' => ?_ | _ => cases eq
  obtain ⟨rfl, rfl⟩ : a = a' ∧ b = b' := by
    cases a'; cases b'; cases congrArg (·.1) eq; exact ⟨rfl, rfl⟩
  unfold lam'; split <;> [rename_i hf; rfl]
  obtain ⟨⟨x, y⟩, h1, h2⟩ := hf; have ⟨hx, hy⟩ := f.2.2 _ h1; change (⟨x,hx⟩, ⟨y,hy⟩) ∈ f at h1
  have ⟨x', a1, a2, a3⟩ := WShape.HasDom.iff.1 hx'.2.1 ⟨x, hx⟩
  have hfx := (WShape.HasTypeLam.iff.1 hx').2.2 x' a2
  have hba := (WShape.HasTypePi.iff.1 ha).2 x' a2
  cases h2 <| (f.app_of_mem h1).2.trans <| a3.trans <| le_bot.2 <| proofIrrel hr hba hfx

theorem TShape.HasType.proofIrrel (hr : r.IsZero)
    (ha : HasType a (.sort r)) (hx : HasType x a) : x ≤ .bot := by
  let k := max x.1 a.1; have hk := Nat.max_le.1 (Nat.le_refl k)
  have ha' := (TShape.HasType.def hk.2 (Nat.zero_le _)).1 ha
  have hx' := (TShape.HasType.def hk.1 hk.2).1 hx
  simp [TShape.sort] at ha'
  have := ha'.proofIrrel hr hx'
  rw [TShape.LE.def hk.1 (Nat.zero_le _)]
  simp [TShape.bot, WShape.lift_bot, this]

theorem WShape.HasType.retype (ha : HasType (n := n) a (.sort r))
    (ha' : HasType a' (.sort r')) (le : a ≤ a') : HasType a (.sort r') := by
  cases n with
  | zero =>
    cases ha.unfold with
    | bot => exact .bot .sort_type
    | sort => exact sort_le.1 le ▸ ha'
  | succ n
  cases ha.unfold with
  | bot => exact .bot .sort_type
  | sort => exact sort_le.1 le ▸ ha'
  | rigid _ h2 =>
    obtain ⟨_, _, rfl, -, -⟩ := WShape.rigid_le.1 le
    exact .rigid (rigid_sort_inv ha').1 h2
  | forallE Ha
  obtain ⟨_, _, le₁, le₂, rfl⟩ := WShape.forallE_le.1 le
  have ⟨H1, H2⟩ := HasTypePi.iff'.1 Ha
  obtain ⟨_, Ha', ⟨⟩⟩ := forallE_l.1 ha'
  refine .forallE <| HasTypePi.iff'.2 ⟨H1, fun x => ?_⟩
  exact retype (H2 _) ((HasTypePi.iff'.1 Ha').2 x) (WShapeFun.app_mono_l le₂ _)

theorem TShape.HasType.retype (ha : HasType a (.sort r))
    (ha' : HasType a' (.sort r')) (le : a ≤ a') : HasType a (.sort r') := by
  let k := max a.1 a'.1; have hk := Nat.max_le.1 (Nat.le_refl k)
  have ha := (TShape.HasType.def hk.1 (Nat.zero_le _)).1 ha
  have ha' := (TShape.HasType.def hk.2 (Nat.zero_le _)).1 ha'
  exact (TShape.HasType.def hk.1 (Nat.zero_le _)).2 <| ha.retype ha' le

theorem WShape.HasDom.single :
    HasDom (WShapeFun.single x y) a ↔ x.HasType a ∨ y ≤ .bot ∧ a.HasType .type := by
  simp [HasDom.def, WShapeFun.mem_single]
  refine ⟨fun H => ?_, ?_⟩
  · obtain ⟨x, y, ⟨rfl, rfl⟩ | ⟨h, rfl, rfl⟩, h2, h3, h4⟩ := H _ _ (.inl ⟨rfl, rfl⟩)
    · exact .inl h4
    · exact .inr ⟨h3, h4.isType⟩
  · rintro H x y (⟨rfl, rfl⟩ | ⟨h, rfl, rfl⟩)
    · obtain h | ⟨h1, h2⟩ := H
      · exact ⟨_, _, .inl ⟨rfl, rfl⟩, .rfl, .rfl, h⟩
      · by_cases hx : x ≤ .bot
        · exact ⟨_, _, .inl ⟨rfl, rfl⟩, .rfl, .rfl, le_bot.1 hx ▸ .bot' h2⟩
        · exact ⟨_, _, .inr ⟨hx, rfl, rfl⟩, bot_le, h1, .bot' h2⟩
    · refine ⟨_, _, .inr ⟨h, rfl, rfl⟩, .rfl, .rfl, .bot' ?_⟩
      obtain h | ⟨_, h⟩ := H <;> [exact h.isType; exact h]

theorem WShape.HasDom.mono (le : a ≤ a') (h : a'.HasType .type) (H : HasDom f a) : HasDom f a' :=
  HasDom.def.2 fun x y hm => let ⟨x', y', h1, h2, h3, h4⟩ := HasDom.def.1 H x y hm
    ⟨x', y', h1, h2, h3, .mono_r le h h4⟩

theorem WShape.Fits.mono_T {fs : List (WShape n)} {T T' : WShape n} (le : T ≤ T')
    (hT' : T'.HasType .type) (H : Fits fs T) : Fits fs T' :=
  mono_T_aux (fun {_ _ _ _} => HasType.mono_r) le hT' H

theorem WShape.Fits.mono_l {fs fs' : List (WShape n)} (h1 : fs.Forall₂ (· ≤ ·) fs')
    (h2 : fs'.Forall₂ (· ≤ ·) fs) {T : WShape n} (hT : T.HasType .type) (H : Fits fs T) :
    Fits fs' T :=
  mono_l_aux (fun {_ _ _} => HasType.mono_l) (fun {_ _ _ _} => HasType.mono_r) h1 h2 hT H

theorem WShape.Fits.join {fs₁ fs₂ : List (WShape n)} (hc : fs₁.Forall₂ Compat fs₂)
    {T : WShape n} (hT : T.HasType .type) (h1 : Fits fs₁ T) (h2 : Fits fs₂ T) :
    Fits (fs₁.zipWith WShape.join fs₂) T :=
  join_aux (fun {_ _ _} => HasType.join) hc hT h1 h2

theorem TShape.HasType.rigid {l : List (WShape n)} {t}
    (h1 : r.IsZero → ShapeParams.famProp c ls = true) (h2 : WShape.CtsTypes t) :
    TShape.HasType (WShape.rigid c ls l t).T (.sort r) :=
  TShape.HasType.sort_r.2 (WShape.HasType.rigid h1 h2)

theorem TShape.HasType.ctor {l : List (WShape n)} {t} {T : WShape n} {fs : List (WShape n)} {wf}
    (h1 : WShape.CtsTypes t) (h2 : ShapeParams.famProp I ls = false) (h3 : ctorTy? c t = some T)
    (h4 : WShape.Fits fs T) :
    TShape.HasType (WShape.ctor c fs wf).T (WShape.rigid I ls l t).T :=
  (WShape.HasType.ctor h1 h2 h3 h4).T

theorem TShape.HasType.ctor' {l : List (WShape n)} {t} {T : WShape n} {fs : List (WShape n)}
    (h1 : WShape.CtsTypes t) (h2 : ShapeParams.famProp I ls = false) (h3 : ctorTy? c t = some T)
    (h4 : WShape.Fits fs T) :
    TShape.HasType (WShape.ctor' c fs).T (WShape.rigid I ls l t).T :=
  (WShape.HasType.ctor' h1 h2 h3 h4).T

/-- Elements of a rigid type former that is a proposition at its levels are bottom. -/
theorem WShape.HasType.rigid_prop {l : List (WShape n)} {t} {m : WShape (n+1)}
    (hp : ShapeParams.famProp I ls = true) (H : HasType m (.rigid I ls l t)) : m = .bot := by
  obtain ⟨-, rfl | ⟨_, _, _, _, rfl, h, -⟩⟩ := rigid_inv H
  · rfl
  · rw [hp] at h; cases h

end

end Lean4Lean.ShapeModel
