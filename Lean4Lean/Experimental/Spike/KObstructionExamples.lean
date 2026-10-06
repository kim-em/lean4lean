/-! # Phase 1 spike: the obstruction terms, checked by Lean itself

Source-level Lean (no `Lean4Lean` imports): the terms used in `Spike/README.md` and in the
hypotheses of `Spike.check_of_piAdequacy`, elaborated and kernel-checked as ordinary Lean.
This is evidence about the *intended* theory, which lean4lean's declarative `IsDefEq` is
meant to capture: each `fail_if_success` records that Lean's definitional equality
checker does not identify the stuck term with the candidate Pi type. It is not a proof that
`IsDefEq` cannot derive the equation; that would need a confluence argument, which is
exactly what is unavailable (BASE_OBLIGATIONS_DESIGN.md, section 1).

No `sorry` and no axioms. -/

namespace Lean4Lean.Spike.KObstructionExamples

/-! ## 1. `Eq.rec` with two variable indices

`T` is a type (`T : Type`) whose head, read through the cast, is the Pi type
`R y → R y` — but `R : Q a → Type` while `y : Q b`, so that reduct is ill-typed, and the
checked K-like step does not fire because `a` and `b` are distinct variables. -/
section variables
variable (α : Type) (a b : α) (h : a = b) (Q : α → Type) (R : Q a → Type) (y : Q b)

/-- The cast `h ▸ (fun z => R z → R z) : Q b → Type`. -/
def castFam : Q b → Type :=
  @Eq.rec α a (fun x _ => Q x → Type) (fun z => R z → R z) b h

/-- The stuck type. -/
def T : Type := castFam α a b h Q R y

/-- Iota at the aligned index is literal (`hiota` of `check_of_piAdequacy`). -/
example : castFam α a a rfl Q R = fun z => R z → R z := rfl

/-- K-like reduction fires on a *neutral* major once the indices agree. -/
example (h' : a = a) : castFam α a a h' Q R = fun z => R z → R z := rfl

/-- With distinct indices the cast is stuck: `T` is not definitionally the Pi type obtained
by transporting `y` back (`R (h ▸ y)` would need `h.symm`). -/
example : True := by
  fail_if_success
    have : T α a b h Q R y = (R (h.symm ▸ y) → R (h.symm ▸ y)) := rfl
  trivial

/-- ...and, of course, not the ill-typed read-through reduct either; the only candidate
heads are stuck `Eq.rec` applications. -/
example : True := by
  fail_if_success
    have : ∃ (B : Type) (C : B → Type), T α a b h Q R y = ((x : B) → C x) := ⟨_, _, rfl⟩
  trivial

end variables

/-! ## 2. Indices that no model of the Coquand–Huber kind can tell apart

`f` and `g` are both the identity on `Nat` as functions on finite approximations (each
sends the shape of a numeral, or of a partial numeral `succ (succ ⊥)`, to itself, and
`⊥` to `⊥`), so any shape semantics gives them the same denotation, even one with neutral
atoms for variables: `g` is closed. They are not definitionally equal: `g n` is stuck on
the variable `n`. -/

def f : Nat → Nat := fun n => n
def g : Nat → Nat := fun n => @Nat.rec (fun _ => Nat) 0 (fun _ ih => ih.succ) n

example : f 3 = g 3 := rfl
example : True := by
  fail_if_success
    have : f = g := rfl
  trivial

section fg
variable (h : f = g) (Q : (Nat → Nat) → Type) (R : Q f → Type) (y : Q g)

/-- The stuck type at closed, semantically equal, non-convertible indices. -/
def Tfg : Type := (@Eq.rec (Nat → Nat) f (fun x _ => Q x → Type) (fun z => R z → R z) g h) y

example : True := by
  fail_if_success
    have : ∃ (B : Type) (C : B → Type), Tfg h Q R y = ((x : B) → C x) := ⟨_, _, rfl⟩
  trivial
end fg

/-! ## 3. The singleton family of STRENGTHENING.md without `Eq`: typed origin extraction

The design document (section 2.4) argues that the semantics needs canonical `Eq` to build a
proof of the proof field. That is not so: the family's own recursor extracts the
constructor *origin* of the data field and a proof of the proof field *at the origin*,
with no `Eq` in sight. What `Eq` adds is only the identification of the origin with the
index `v`, which the countermodel shows is not derivable without it. -/
section singleton
variable (C : Type) (F : C → Type) (c : C) (P : F c → Prop) (leftMap : F c → F c)

inductive I : (n : C) → F n → F n → Prop where
  | mk (v : F c) (h : P v) : I c v (leftMap v)

/-- The constructor origin of the data field, extracted by large elimination into the
constant motive `F c`. -/
noncomputable def orig {n : C} {x w : F n} (p : I C F c P leftMap n x w) : F c :=
  I.rec (motive := fun _ _ _ _ => F c) (fun v _ => v) p

/-- A proof of the proof field at the origin, extracted by elimination into `Prop` along a
motive that mentions `orig`. The constructor branch typechecks because
`orig (I.mk v h)` reduces to `v` by iota. -/
theorem origProof {n : C} {x w : F n} (p : I C F c P leftMap n x w) :
    P (orig C F c P leftMap p) :=
  I.rec (motive := fun _ _ _ p => P (orig C F c P leftMap p)) (fun _ h => h) p

variable (K : (v : F c) → P v → Type) (v : F c)

/-- The large eliminator of the countermodel, at an arbitrary major. -/
def SI (p : I C F c P leftMap c v (leftMap v)) : Type :=
  I.rec (motive := fun _ _ _ _ => Type) K p

/-- An `Eq`-free, well-typed reconstruction of the eliminator's value at the origin. -/
def SIrec (p : I C F c P leftMap c v (leftMap v)) : Type :=
  K (orig C F c P leftMap p) (origProof C F c P leftMap p)

/-- At a constructor major the reconstruction agrees with iota... -/
example (q : P v) : SI C F c P leftMap K v (I.mk v q) = SIrec C F c P leftMap K v (I.mk v q) :=
  rfl

/-- ...but at a neutral major it is not a definitional equality (it is an evaluation step a
logical relation may use, not a rule of the theory). -/
example (p : I C F c P leftMap c v (leftMap v)) :
    SI C F c P leftMap K v p = SI C F c P leftMap K v p := by
  fail_if_success
    have : SI C F c P leftMap K v p = SIrec C F c P leftMap K v p := rfl
  rfl

end singleton

end Lean4Lean.Spike.KObstructionExamples
