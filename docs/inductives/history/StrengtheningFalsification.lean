/-!
Run with `lake env lean docs/inductives/history/StrengtheningFalsification.lean`.

Evidence for the falsification study of `VEnv.strengthening_of_canonicalEq`
(`docs/inductives/STRENGTHENING_NOTES.md`). Plain Lean, no lean4lean imports, no
axioms beyond the section variables (which play the role of the opaque
constants and context variables of the object-language examples).

Each example has the same shape as the countermodel of `STRENGTHENING.md`:
a conversion between endpoints that do not mention a binder `q`, derived in the
larger context through a proof that does mention `q`. For each mechanism the
file checks, with Lean's own kernel, the *smaller-context* replacement: a
`q`-free term that plays the role of `q`, built from canonical `Eq` and the
family's own recursor. The replacement chain uses only `rfl` steps that are
instances of `proofIrrel`, iota (native recursor rules, `Eq.rec` iota), K
(which in `VEnv.IsDefEq` is `proofIrrel` followed by `Eq.rec` iota), `appDF`,
`symm` and `trans`. `congrArg`/`Eq.trans` record the congruence/transitivity
chain; this is not a claim that kernel reduction compares the endpoints
directly (it does not: the kernel never turns a neutral non-K proof into a
constructor).

The general construction (section 1) is the one used for singleton eta:
read each data field from its literal index position, cast it along a
*type-level* equation `IdxTy(i') = FieldTy(d')` (an instance of `@Eq (Sort u)`),
and extract each proof field with the family's recursor into `Prop` at the
motive "equations imply the field type at the cast data". In the constructor
branch every equation is between definitionally equal types, so the casts
compute by K; at the major the equations are supplied by `rfl`.
-/

namespace StrengtheningFalsification

/-! ## 0. The countermodel itself, with canonical `Eq` (type-cast form) -/
section countermodel
variable (C : Type) (F : C → Type) (c : C) (P : F c → Prop)
  (leftMap rightMap : F c → F c)

inductive I : (n : C) → F n → F n → Prop where
  | mk (v : F c) (h : P v) : I c v (leftMap v)

inductive J : (n : C) → F n → F n → Prop where
  | mk (v : F c) (h : P v) : J c v (rightMap v)

/-- Extraction by a type-level equation (the generic scheme of section 1). -/
theorem extractI {n : C} {x w : F n} (p : I C F c P leftMap n x w)
    (e : F n = F c) : P (cast e x) :=
  I.rec (motive := fun n x _ _ => (e : F n = F c) → P (cast e x))
    (fun _ h _ => h) p e

theorem extractJ {n : C} {x w : F n} (p : J C F c P rightMap n x w)
    (e : F n = F c) : P (cast e x) :=
  J.rec (motive := fun n x _ _ => (e : F n = F c) → P (cast e x))
    (fun _ h _ => h) p e

variable (K : (v : F c) → P v → Type) (v : F c)

/-- Singleton eta: the major is (by proof irrelevance) its constructor form
with the data field read from the index and the proof field extracted. -/
example (p : I C F c P leftMap c v (leftMap v)) :
    p = I.mk v (extractI C F c P leftMap p rfl) := rfl

noncomputable def SI (p : I C F c P leftMap c v (leftMap v)) : Type :=
  I.rec (motive := fun _ _ _ _ => Type) K p

noncomputable def SJ (r : J C F c P rightMap c v (rightMap v)) : Type :=
  J.rec (motive := fun _ _ _ _ => Type) K r

/-- The smaller-context derivation of `SI ≡ SJ`: no `q`. -/
theorem SI_eq_SJ (p : I C F c P leftMap c v (leftMap v))
    (r : J C F c P rightMap c v (rightMap v)) :
    SI C F c P leftMap K v p = SJ C F c P rightMap K v r :=
  calc SI C F c P leftMap K v p
      = SI C F c P leftMap K v (I.mk v (extractI C F c P leftMap p rfl)) :=
        congrArg (SI C F c P leftMap K v) rfl
    _ = K v (extractI C F c P leftMap p rfl) := rfl
    _ = K v (extractJ C F c P rightMap r rfl) := rfl
    _ = SJ C F c P rightMap K v (J.mk v (extractJ C F c P rightMap r rfl)) := rfl
    _ = SJ C F c P rightMap K v r := congrArg (SJ C F c P rightMap K v) rfl
end countermodel

/-! ## 1. Dependent three-index family, proof fields depending on earlier proof fields

Data fields `x`, `y` sit at index positions 1 and 2, whose generic types
`G a` and `H a x` differ from the field types `G g0` and `H g0 x`.  Both casts
are along type-level equations; the second equation is heterogeneous in its
data (`x : G a` against `cast e₁ x : G g0`) but is still an `Eq` between two
types in `Type`. -/
section threeIndex
variable (A : Type) (G : A → Type) (g0 : A) (H : (a : A) → G a → Type)
  (P : (x : G g0) → H g0 x → Prop) (Q : (x : G g0) → (y : H g0 x) → P x y → Prop)

inductive D3 : (a : A) → (x : G a) → H a x → Prop where
  | mk (x : G g0) (y : H g0 x) (h : P x y) (h₂ : Q x y h) : D3 g0 x y

theorem D3.ext₁ {a : A} {x : G a} {y : H a x} (p : D3 A G g0 H P Q a x y)
    (e₁ : G a = G g0) (e₂ : H a x = H g0 (cast e₁ x)) : P (cast e₁ x) (cast e₂ y) :=
  D3.rec (motive := fun a x y _ => (e₁ : G a = G g0) → (e₂ : H a x = H g0 (cast e₁ x)) →
      P (cast e₁ x) (cast e₂ y))
    (fun _ _ h _ _ _ => h) p e₁ e₂

/-- The second proof field: its type mentions the first proof field, which the
motive takes as an argument `z` (any proof will do, by irrelevance). -/
theorem D3.ext₂ {a : A} {x : G a} {y : H a x} (p : D3 A G g0 H P Q a x y)
    (e₁ : G a = G g0) (e₂ : H a x = H g0 (cast e₁ x)) (z : P (cast e₁ x) (cast e₂ y)) :
    Q (cast e₁ x) (cast e₂ y) z :=
  D3.rec (motive := fun a x y _ => (e₁ : G a = G g0) → (e₂ : H a x = H g0 (cast e₁ x)) →
      (z : P (cast e₁ x) (cast e₂ y)) → Q (cast e₁ x) (cast e₂ y) z)
    (fun _ _ _ h₂ _ _ _ => h₂) p e₁ e₂ z

example (x : G g0) (y : H g0 x) (p : D3 A G g0 H P Q g0 x y) :
    p = D3.mk x y (D3.ext₁ A G g0 H P Q p rfl rfl)
      (D3.ext₂ A G g0 H P Q p rfl rfl (D3.ext₁ A G g0 H P Q p rfl rfl)) := rfl

example (K : (x : G g0) → (y : H g0 x) → (h : P x y) → Q x y h → Type)
    (x : G g0) (y : H g0 x) (p : D3 A G g0 H P Q g0 x y) :
    D3.rec (motive := fun _ _ _ _ => Type) K p =
      K x y (D3.ext₁ A G g0 H P Q p rfl rfl)
        (D3.ext₂ A G g0 H P Q p rfl rfl (D3.ext₁ A G g0 H P Q p rfl rfl)) :=
  congrArg (fun t => D3.rec (motive := fun _ _ _ _ => Type) K t)
    (show p = D3.mk x y _ _ from rfl)
end threeIndex

/-! ## 2. A proof field occurring as an index, a non-injective index map, and
an index pattern before the data position -/
section proofIndex
variable (X : Type) (R : X → Prop) (f : X → X) (B : X → Type) (b0 : X)

/-- `h` (a proof) is an index; `f x` is a non-injective pattern before the data
position of `y`, whose generic type `B a` differs from its field type `B (f x)`. -/
inductive PI : (a : X) → B a → (x : X) → R x → Prop where
  | mk (x : X) (y : B (f x)) (h : R x) (k : R (f x)) : PI (f x) y x h

theorem PI.extK {a : X} {y : B a} {x : X} {h : R x} (p : PI X R f B a y x h)
    (e : B a = B (f x)) : R (f x) :=
  PI.rec (motive := fun a _ x _ _ => (e : B a = B (f x)) → R (f x))
    (fun _ _ _ k _ => k) p e

example (x : X) (y : B (f x)) (h : R x) (p : PI X R f B (f x) y x h) :
    p = PI.mk x y h (PI.extK X R f B p rfl) := rfl
end proofIndex

/-! ## 3. Universe-polymorphic family, specialized to `Prop`

`Sort u`-valued families instantiated at `u = 0` are proof families; Lean's
criterion is syntactic and level-independent (the field `a : α : Sort u` counts as
data because `u` is not syntactically zero, so it must be an index), so the same
extraction applies. -/
section poly
universe u v
variable (α : Sort u) (S : α → Prop)

set_option bootstrap.inductiveCheckResultingUniverse false in
/-- The leading `Unit` index only prevents Lean from promoting `a` to a parameter. -/
inductive PolyS : Unit → α → Sort u where
  | mk (a : α) (h : S a) : PolyS () a

theorem PolyS.ext {β : Prop} {T : β → Prop} {a : β} (p : PolyS.{0} β T () a) : T a :=
  PolyS.rec (motive := fun _ a _ => T a) (fun _ h => h) p

example {β : Prop} {T : β → Prop} (a : β) (p : PolyS.{0} β T () a) :
    p = PolyS.mk a (PolyS.ext p) := rfl
end poly

/-! ## 4. Recursive singleton (`Acc`): no `Eq` needed -/
section acc
variable (α : Sort u) (r : α → α → Prop)

theorem accExt {x : α} (p : Acc r x) : ∀ y, r y x → Acc r y :=
  Acc.rec (motive := fun x _ => ∀ y, r y x → Acc r y) (fun _ h _ => h) p

example (x : α) (p : Acc r x) : p = Acc.intro x (accExt α r p) := rfl

/-- The larger-context conversion `Acc.rec F p ≡ F x h (fun y hy => Acc.rec F (h y hy))`
for a removed `h` holds in the smaller context with `accExt p` for `h`. -/
example (M : α → Sort v) (F : (x : α) → (∀ y, r y x → Acc r y) → (∀ y, r y x → M y) → M x)
    (x : α) (p : Acc r x) :
    Acc.rec (motive := fun x _ => M x) F p =
      F x (accExt α r p) (fun y hy => Acc.rec (motive := fun x _ => M x) F (accExt α r p y hy)) :=
  congrArg (fun t => Acc.rec (motive := fun x _ => M x) F t)
    (show p = Acc.intro x (accExt α r p) from rfl)
end acc

/-! ## 5. Nested singleton: a proof field that is itself a singleton major -/
section nested
variable (X : Type) (T : X → Prop)

/-- Leading `Unit` indices prevent promotion of `x` to a parameter. -/
inductive Inner : Unit → X → Prop where
  | mk (x : X) (t : T x) : Inner () x

inductive Outer : Unit → X → Prop where
  | mk (x : X) (i : Inner X T () x) : Outer () x

theorem Outer.ext {x : X} (p : Outer X T () x) : Inner X T () x :=
  Outer.rec (motive := fun _ x _ => Inner X T () x) (fun _ i => i) p

theorem Inner.ext {x : X} (p : Inner X T () x) : T x :=
  Inner.rec (motive := fun _ x _ => T x) (fun _ t => t) p

noncomputable def SO (K : (x : X) → T x → Type) {x : X} (p : Outer X T () x) : Type :=
  Outer.rec (motive := fun _ _ _ => Type)
    (fun _ i => Inner.rec (motive := fun _ _ _ => Type) K i) p

example (K : (x : X) → T x → Type) (x : X) (p : Outer X T () x) :
    SO X T K p = K x (Inner.ext X T (Outer.ext X T p)) :=
  congrArg (SO X T K)
    (show p = Outer.mk x (Inner.mk x (Inner.ext X T (Outer.ext X T p))) from rfl)
end nested

/-! ## 6. `Quot` over a proposition

`Quot.{0} r : Prop`, so a variable `x : Quot r` is proof-irrelevantly equal to
`Quot.mk r a` for any `a : α` in the larger context, and `Quot.lift f h x` then
computes to `f a`.  In the smaller context the witness `a` is extracted by
`Quot.lift id`; its compatibility proof needs `Eq` (which `Quot.lift`'s own type
already mentions), via proof irrelevance at `α`. -/
section quotProp
variable (α : Prop) (r : α → α → Prop)

theorem quotExt (x : Quot r) : α := Quot.lift (fun a => a) (fun _ _ _ => rfl) x

example (x : Quot r) : x = Quot.mk r (quotExt α r x) := rfl

example (β : Sort v) (f : α → β) (h : ∀ a b, r a b → f a = f b) (x : Quot r) (q : α) :
    Quot.lift f h x = f q :=
  calc Quot.lift f h x = Quot.lift f h (Quot.mk r (quotExt α r x)) :=
        congrArg (Quot.lift f h) (show x = Quot.mk r (quotExt α r x) from rfl)
    _ = f (quotExt α r x) := rfl
    _ = f q := rfl
end quotProp

/-! ## 7. K-like families: zero fields, nothing to extract

The K step on a neutral major needs only the index check, a conversion between
terms of the redex (strengthened recursively). -/
section kLike
variable (α : Sort u) (a : α) (M : (b : α) → HEq a b → Sort v) (m : M a HEq.rfl)

example (h : HEq a a) : HEq.rec (motive := fun {β} _ _ => β = α → Sort v) (fun _ => PUnit) h rfl =
    PUnit := rfl
example (h : a = a) (M : (b : α) → a = b → Sort v) (m : M a rfl) :
    (Eq.rec (motive := M) m h : M a h) = m := rfl
end kLike

/-! ## 8. Removed data binders (study item (iv))

The removed binder `d : D` inhabits `P v` only through a context function
`out : D → P v`.  Every iota step in the larger-context chain fires on a major
that is a subterm of a term of the chain; when the endpoints are `d`-free, the
majors that the canonical certificate fires on are subterms of reducts of the
endpoints, hence `d`-free and present in the smaller context, and the proof is
extracted from the major itself.  `out` is never needed. -/
section dataBinder
variable (C : Type) (F : C → Type) (c : C) (P : F c → Prop)
  (leftMap rightMap : F c → F c) (K : (v : F c) → P v → Type) (v : F c)
  (D : Type) (out : D → P v)

-- Larger context `Γ, d : D`: the chain through `out d`.
example (p : I C F c P leftMap c v (leftMap v)) (r : J C F c P rightMap c v (rightMap v))
    (d : D) : SI C F c P leftMap K v p = SJ C F c P rightMap K v r :=
  calc SI C F c P leftMap K v p
      = SI C F c P leftMap K v (I.mk v (out d)) := congrArg (SI C F c P leftMap K v) rfl
    _ = SJ C F c P rightMap K v (J.mk v (out d)) := rfl
    _ = SJ C F c P rightMap K v r := congrArg (SJ C F c P rightMap K v) rfl

-- Smaller context: `SI_eq_SJ` above, with no `d` and no `out`.

/-- Majors abstracted by a binder inside the endpoints are context variables of
the conversion's own subderivation, so extraction is available there too. -/
example :
    (fun p => SI C F c P leftMap K v p) = (fun p => K v (extractI C F c P leftMap p rfl)) :=
  funext fun p => congrArg (SI C F c P leftMap K v)
    (show p = I.mk v (extractI C F c P leftMap p rfl) from rfl)
end dataBinder

end StrengtheningFalsification
