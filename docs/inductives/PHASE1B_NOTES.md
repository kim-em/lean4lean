# Phase 1b notes: the injectivity half of `VEnv.WF.headInversion`

Branch `agent/verify-inductives-headinj` (worktree `lean4lean-e3`). Standing goal:
`docs/inductives/GOAL.md`. Background: `docs/inductives/PHASE1_SPIKE.md` (the obstruction),
`docs/inductives/PHASE1B_ASTRA_REVIEW.md` (second-opinion review of the candidate routes),
`docs/inductives/BASE_OBLIGATIONS_DESIGN.md`. The separation half is Phase 1a, branch
`agent/verify-inductives-headinv` (`docs/inductives/PHASE1_NOTES.md` there).

Mission: prove the fields `forallE_forallE`, the argument part of `rigid_rigid`,
`former_args` and `proj_fieldType` of `VEnv.HeadInversion` for every `VEnv.WF` environment,
as `theorem VEnv.WF.headInjectivity` in `Lean4Lean/Theory/Typing/HeadInjectivity/`.

Claims are tagged **[Lean]** (proved, no `sorry`), **[paper]** (argued here in full) or
**[plan]** (not yet carried out).

## 0. Summary of the design

1. **No logical relation, no adequacy, no reduction.** The spike's obstruction is against
   *adequacy*: a relation that sends a semantically Pi-shaped type to a syntactic Pi reduct.
   Bare injectivity needs no such thing. It follows from **soundness of a glued model**: a
   model in the style of the shape model (Carneiro's domain, Phase 1a) in which every value
   that a type former builds records the *declarative equivalence classes* of its components
   (the class of a Pi domain, of each codomain instance, of each argument of a rigid type
   former). If `Pi A B` and `Pi A' B'` are linked by a chain of derivable equalities, soundness
   makes their values equal, and the recorded domain classes give `A ~ A'` declaratively
   (section 3). Nothing has to reduce, so nothing has to be cast.
2. **Eliminators on proof majors read through, filtered by type.** A K-like `Eq.rec` or a
   singleton recursor on a proof major is interpreted as its iota result, read from the index
   values, restricted to the approximations that are typed at the eliminator's actual result
   type. In the spike's witness `T` the read-through result has domain class "class of
   `R y`", which is not a typed class (`R y` is ill-typed), so the filter removes it and `T`
   denotes bottom (section 4.1). Read-through that stays typed (a constant motive) gives a
   stuck term a Pi value; this is harmless because soundness is only claimed for derivable
   equalities.
3. **No canonical `Eq` is needed.** Proof fields of a singleton constructor are read as the
   class of *all* proofs of the field's type at the read-through data; when that class is
   empty (the countermodel family `I` in a context with no proof of `P v`), every
   approximation that mentions it is untyped and filtered away (section 4.2). Decision:
   `headInjectivity` takes `env.WF` only.
4. **`proj_fieldType` is syntactic once Pi and rigid injectivity hold up to chains.** It is
   proved by an induction on the strong typing derivation of the first field type: the
   unused, untypable earlier projections never occur in the field type, so the induction
   never visits them; the leaves are aligned by uniqueness for strong sub-derivations
   (section 5). No strengthening is needed.
5. The work splits into a **syntactic layer** (chain-level injectivity ⟹ uniqueness ⟹ the four
   fields, including `proj_fieldType`; independent of any model) and a **semantic layer**
   (the glued model and its soundness ⟹ chain-level injectivity).

## 1. Routes examined, and why they were not adopted

* **(A) cast-pushing reduction inside the relation.** Adopting it requires component
  transports for Pi endpoints of arbitrary motives (Astra point 3: whole-type transport does
  not give domain/codomain transports; OTT adds equality projections for that purpose). The
  concrete failure: motive `M x _ := Nat.rec (Q x → Type) (fun _ _ => Bool → Type) (x 0)` with
  indices `f`, `g` (extensionally equal, not convertible). Both endpoints reduce to Pis with
  domains `Q f`, `Q g`; the generic motive is stuck, so no `Eq.rec` motive produces the
  transport `Q g → Q f` from the syntax, and a fresh cast term former would put the reducts
  outside `VExpr`, so the relation's declarative clauses would need a conservativity theorem
  for an extended judgment. Not adopted: route G below does not need any reduct at all.
* **(B) neutral eliminators.** Astra point 2 is right: for `h : a = a`, congruence, proof
  irrelevance and iota equate a neutral-major eliminator with its canonical result, so a
  neutral-only relation misses a derivable equation; checking the index declaratively
  reintroduces the obstruction. More precisely, any adequacy argument whose reduction checks
  `Γ ⊢ a ≡ b` needs *reflection* (declaratively equal, self-related ⟹ related), and reflection
  at a Pi shape is Pi injectivity itself. The answer to the mission's question (B) is: the
  theory cannot derive `T ≡ Pi`, and the obstruction is indeed an artefact of the adequacy
  statement; the right statement is soundness of a glued model, which has no demand on `T`.
* **(C) type-level-only relation with singleton eta.** Same defect as (B) at type level, and
  singleton eta needs a constructor reconstruction at the actual indices, which the
  countermodel shows is not always typable.
* **(G) glued model, adopted.** Sections 2-4. Astra's recommendation "keep Carneiro's finite
  shape architecture with enriched codes" is adopted for the domain; its recommendation to
  keep a fundamental lemma over a `TyRel`/`TmRel` relation is not, because the relation's only
  role was to produce declarative component equalities, and the glued values carry those
  directly. Astra point 6 (`Definitional Inversion, Without Normalisation`, arXiv 2607.13662):
  the paper is not available offline here; its title and the review's description (inversion
  from a semantic argument without normalisation, proof-relevant identity treated apart from
  strict propositions) match the present design in spirit. The combined K/singleton case is
  handled here by the typed read-through of section 4, which the review notes the paper does
  not cover.

## 2. The glued model

Fix `env`, the universe-parameter count `U`, and a *target context* `Δ` with
`OnCtx Δ (env.IsType U)`. All classes below are classes of `VExpr`s in `Δ`.

### 2.1 Classes

* Type links: `TyLink Δ A B := ∃ u, Δ ⊢ A ≡ B : sort u`. Type class:
  `TyCls Δ A := {B | EqvGen (TyLink Δ) A B}`. For a typed `A`, `B ∈ TyCls Δ A` iff `A = B` or
  `TypeChain Δ A B`.
* Element links at a set of types `D`: `ElLink Δ D a b := ∃ X ∈ D, Δ ⊢ a ≡ b : X`. Element
  class: `ElCls Δ D a := {b | EqvGen (ElLink Δ D) a b}`.
* **Collapse lemma** [plan, Lean, elementary]: if `D = TyCls Δ X₀`, `Δ ⊢ a : X` with `X ∈ D`,
  and `b ∈ ElCls Δ D a`, then `Δ ⊢ a ≡ b : X₀`. Each link is at some `X' ∈ D`, transported to
  `X₀` along the chain (`TypeChain.defeqDF`), and links at one type compose by `trans`.
  This is why classes are *typed*: an untyped `EqvGen IsDefEqU` class would only give
  chains of `IsDefEqU` links at unrelated types, which cannot be composed without uniqueness.
* A class `c` is *typed at* a type class `D` if `c = ElCls Δ D x` for some `x` with
  `Δ ⊢ x : X`, `X ∈ D`. Junk classes (of ill-typed terms, or empty) are not typed.

### 2.2 Shapes

Finite approximations, Carneiro's domain with these constructors (a *glued value* is a pair
`(c, s)` of a class and a shape):

* `bot`;
* `sort ℓ`, `ℓ : List Nat → Nat` the evaluation of the level (equal iff `≈`);
* `pi (dom : Set VExpr × Shape) (cod : finite table (Set VExpr × Shape) ↦ (Set VExpr × Shape))`:
  the domain's type class and shape; each entry maps a glued argument to the codomain
  instance's type class and shape;
* `lam (D : Set VExpr) (tab : finite table (Set VExpr × Shape) ↦ Shape)`: `D` is the domain's
  type class, keys are glued arguments; `lam D` with an all-bottom table is identified with
  `bot` (Carneiro's `lam'`), which validates `eta` at stuck functions;
* `rigid c ls (args : List (Set VExpr × Shape))` (plus, as in Phase 1a, the constructor
  telescopes of a family, for structural element typing);
* `ctor c (fields : List (Set VExpr × Shape))` for constructors of families without
  structure eta, and `sctor c (fields : List Shape)` for structure constructors (no classes;
  all-bottom collapses to `bot`, validating `structEta` and `unitLike` at stuck majors).

Order, compatibility and joins are Carneiro's, with classes compared by equality (flat).
Shape typing extends Phase 1a's (`ShapeParams`): `lam D tab` is typed at `pi (C, a) cod` only
if `D = C`; a glued value `(c, s)` is typed at a glued type `(C, a)` if `c` is typed at `C`
and `s` at `a`; elements of a proposition (a type shape typed at `sort 0`) are `bot`.

### 2.3 Valuations and interpretation

A valuation `ρ` assigns a glued value to each variable of `Γ`. The class of a subterm `t` of
`Γ` under `ρ` is the union, over substitutions `σ` choosing a representative of each
variable's class, of the appropriate class of `σ t` in `Δ` (`TyCls` in type positions,
`ElCls D` in argument positions with `D` supplied by the function value). *Typed* valuations
come from a typed substitution `Δ ⊢ σ : Γ`, each class the class of `σ x` at `TyCls (σ A_x)`
and each shape typed at the interpretation of `A_x`.

`Interp ρ m t` ("`m` approximates `t` under `ρ`") is an inductive predicate, as
`LE_Interp`/Phase 1a `Interp`, downward closed, with these glued clauses:

* `forallE A B`: `pi ((class of A), a) cod` with `a` approximating `A` and, for every typed key
  `k = (c, x)`, `cod k = (class of B under ρ.push k, b)` with `b` approximating `B` under
  `ρ.push k`;
* `lam A t`: `lam (class of A) tab`, `tab k` approximating `t` under `ρ.push k` for typed keys;
* `app f a`: from a `lam D tab` approximation of `f`, look up the key `(ElCls D (σ a), x)` with
  `x` approximating `a` (classes from syntax, shapes from semantics);
* constants: Phase 1a's spine machine: rigid heads produce `rigid c ls args` (argument classes
  at the domain classes of the head's type), constructors `ctor`/`sctor`, rule-headed
  constants match their rules (definitions, native iota, `Quot.lift`, schema equations);
* eliminators on proof majors (mode C): read-through, data fields read from the index values,
  proof fields with class "all proofs of the field type at the read-through data", the result
  **restricted to approximations typed at an approximation of the eliminator's result type**
  (the typing filter of every head);
* `proj S i e`: the `i`-th field shape of a `ctor`/`sctor` approximation of `e`, else `bot`.

### 2.4 Soundness

**Theorem (soundness)** [plan]: for every strong derivation `Γ ⊢ t ≡ t' : A`
(`IsDefEqStrong`) and every typed valuation `ρ` of `Γ` into `Δ`:
`∀ m, Interp ρ m t ↔ Interp ρ m t'`, and every approximation of `t` is below one typed at an
approximation of `A` (the typing invariant, proved simultaneously).

Proof: induction on the strong derivation, uniformly over all typed valuations. The class
components need only declarative facts (each derivable equality, substituted by `σ`, links
the two classes); the shape components follow Carneiro's/Phase 1a's proofs. The cases where
classes matter:

* `appDF`: the argument's classes on both sides are `ElCls D (σ a)`, `ElCls D (σ a')` with `D`
  the domain class of the function value, equal to `TyCls (σ A)` by the typing invariant at
  `f : Pi A B`; `σ a ≡ σ a' : σ A` links them.
* `beta`: substitution lemma (classes of `σ (t[a])` are those of `t` under
  `ρ.push (class of σ a, x)`), structural.
* `defeqDF`: the typing invariant transfers along `A ≡ B` because soundness at `A ≡ B`
  makes their interpretations equal.
* K-like/singleton iota: in a derivable instance the index subderivations make the index
  values equal, so the restriction filter is vacuous (the minor's approximations are typed at
  `M ctorIdx (ctor ..)`, whose interpretation equals that of `M is h`).

Well-founded measures: the strong derivation for soundness (uniform in valuations, so
the substitution generality is free); `Interp` is inductive (least fixed point: divergent
definitions denote `bot`); class invariance under change of representatives is by induction
on `Interp` derivations; no normalisation measure anywhere.

## 3. Chain-level injectivity from soundness

Apply soundness at the identity valuation (`σ = id`, shapes `bot`), and at the weakening
valuation `Γ → A :: Γ` (`σ = lift`, the new variable's class the class of `bvar 0`).

* **Pi** [paper]: the shape `pi ((TyCls A), bot) [((ElCls (TyCls A) (bvar 0)), bot) ↦ ((TyCls B), bot)]`
  (at the weakening valuation, in `Δ = A :: Γ`) approximates `Pi A B`. A chain to `Pi A' B'`
  makes it approximate `Pi A' B'` too, so `TyCls A = TyCls A'` and `TyCls B = TyCls B'` in
  `A :: Γ`: `TypeChain Γ A A'` and `TypeChain (A :: Γ) B B'`.
* **Sort**: equal `sort` shapes give `u ≈ v`.
* **Rigid**: equal `rigid c ls args` shapes give `c = c'`, `ls ≈ ls'`, and equal argument
  classes; the collapse lemma turns each into `args_i ≡ args'_i` at the domain of the head's
  type instantiated by the left arguments (`SpineArgsEq` when the type is a syntactic
  telescope; `IsDefEqU` in general).
* The separation fields follow from distinct shape heads (the model also delivers Phase 1a).

These are the hypotheses of the syntactic layer (section 5): a structure
`HeadInjectivityCore env` with `sort_sort`, `forallE_forallE_chain`, `rigid_rigid`,
`former_args`.

## 4. The three hardest cases

### 4.1 K-like `Eq.rec` into `Sort` at a proof major (the spike's `T`)

`Γ := α, a b : α, h : a = b, Q : α → Type, R : Q a → Type, y : Q b`,
`T := Eq.rec (motive := fun x _ => Q x → Type) (fun z => R z → R z) b h y`.
Read-through gives `T` the approximations of `(fun z => R z → R z)` applied to the key
`(class of y, bot)`, filtered by typing at the interpretation of `M b h = Q b → Type`.
The minor's `lam` approximations have domain class `TyCls (Q a)`, the target Pi has domain
class `TyCls (Q b)`; `Q a` and `Q b` are not chain-equal [belief], so no non-bottom
`lam` approximation is typed at the target, and `Eq.rec .. b h` denotes `bot` as a function;
`T` denotes `bot`. Even without that belief, the inner Pi's domain class would be the class
of `R y`, which is not a typed class. When the motive is constant
(`M x _ := Type → Type`, `m := fun X => X → X`), `T' := Eq.rec m b h Nat` keeps its Pi
approximation (typed); nothing is required of it, since `T'` is never derivably equal to a
Pi [belief], and if it were, soundness would be consistent with that.

### 4.2 The countermodel's singleton family `I` (no `Eq`)

`I.rec (motive := fun .. => Type) K n x w p` with `p : I ..` a variable: read-through reads
the data fields from the indices and gives the proof field the class of all proofs of
`P v` in `Δ`. In a `Δ` with no proof, that class is empty, not typed; approximations of the
minor's body that record it (for example the domain class of a Pi mentioning the proof) are
filtered out; approximations that do not mention it survive. In `Δ, q : P v` the class is
the class of `q`, and the derivable iota instance is validated. Soundness never compares the
two contexts (valuations are not Kripke), so the countermodel's failure of strengthening is
irrelevant to the model. No `Eq` and no `orig`/`toOrigin` transports are needed.

### 4.3 `proj_fieldType` with an untypable unused data slot

See section 5. The model is not involved.

## 5. The syntactic layer

**Structure** `HeadInjectivityCore env` [plan, Lean]: `sort_sort`; `forallE_forallE_chain`
(`TypeChain (Pi A B) (Pi A' B') → TypeChain A A' ∧ TypeChain (A :: Γ) B B'`); `rigid_rigid`
and `former_args` as in `HeadInversion`.

**Uniqueness up to chains** (`uniq_chain'`) by induction on the first strong typing, as
`HasTypeStrong.uniq_chain` in `UniqueTyping.lean`, using the core; the `app` case uses
`TypeChain.instN` on the codomain chain instead of a single link. The `proj` case:

**Lemma C** (field-type congruence): let `F` be the selected field's type in the constructor
telescope, `σ₁ σ₂` the two instantiations (parameters `ps₁`/`ps₂`, earlier fields
`proj S j sm₁`/`proj S j sm₂`, levels `ls₁ ≈ ls₂`). By induction on the *strong derivation of
`F[σ₁] : sort l₁`* (a strong sub-derivation of the `proj` typing), with the claim
"`F'[σ₁] ≡ F'[σ₂] : T` for the subterm `F'` and the type `T` of the current sub-derivation":
congruence at `app`/`lam`/`forallE`/`proj`/`const`/`sort`/`elim` nodes (each with the
sub-derivation's own types, so no type alignment is needed), `defeq` nodes by `defeqDF`.
At a variable leaf the claim is aligned by uniqueness *for that sub-derivation* (the
induction hypothesis of `uniq_chain'`, applicable because the leaf's derivation is a strong
sub-derivation of the outer typing): parameters are related at their telescope domains by
`former_args` on the chained major types; occurring earlier projections are typed, and are
related by `projDF` (their majors related along the chain from `uniq_chain'` on the major).
Unused earlier slots do not occur in `F`, so no derivation of `F[σ₁]` visits them.

Then `TypeChain.collapse` (as in `UniqueTyping.lean`) turns chains into single links, giving
`forallE_forallE` and the other fields exactly as stated in `HeadInversion`.

## 6. Decisions

* D1. Route G (glued model, soundness only). Rationale: sections 0-1.
* D2. `HasCanonicalEq` is not assumed. Rationale: section 4.2.
* D3. The syntactic layer (section 5) is built first, against `HeadInjectivityCore`; it is a
  plain hypothesis of an intermediate theorem, never a field of the final statement.
* D4. Files: `Lean4Lean/Theory/Typing/HeadInjectivity/` (syntactic layer, model, statement);
  scratch exploration in `Lean4Lean/Experimental/Injectivity/Scratch/`. Imports: only the
  uniqueness-free base (`Lemmas`, `Strong`, `EnvLemmas`, `ProjectionRigidity`, `HeadInversion`'s
  chain lemmas); never `UniqueTyping`, `Injectivity`, `ChurchRosser`, `FullReduction`,
  `HeadReduction`.
* D5. The glued model duplicates Phase 1a's model with classes added; if both land, Phase 1a's
  model is the glued model with classes forgotten, and the separation half can be taken from
  either. Recorded so the two branches can be merged into one model.

## 7. Second review of route G (Astra, /tmp transcript summarised here)

Astra found no counterexample to chain-level injectivity and judged the syntactic layer
(section 5) viable; it raised the following points, all adopted:

* R1 (`Box`): with `structure Box where A : Type`, `Box.rec (motive := fun _ => Type)
  (fun A => A → A) (Box.mk X) ≡ X → X`, but `Box.mk X` has the all-bottom `sctor`, i.e.
  `bot`. So **iota for an eta structure must not match the major's shape**: it reads every
  field as the glued value `(class of proj S j major, field shape or bot)`, the class taken
  from the major's syntax (representative-independent because the projections of a
  structure with large elimination are typable: either the result level is never zero, or
  all fields are proofs, section 2.3). Adopted.
* R2: function and codomain tables need an explicit "absent entry" (an absent key means no
  information), and the "for every typed key" clause must keep `Interp` positive: key typing
  is an independent predicate (class typing is declarative, shape typing structural), as in
  Carneiro's prototype. Adopted.
* R3: the typing filter needs a **reconstruction lemma**: in a derivable iota or K instance,
  every approximation of the minor extends to one typed at the target type, because the
  source and target result types have equal interpretations by the index subderivations. The
  filtered denotation is the downward closure of the typed raw read-through approximations.
  Adopted as an explicit lemma.
* R4: an empty proof-field class does not give a typed valuation, so read-through at an
  uninhabited proof field yields `bot` (no typed key exists). Section 4.2 is corrected
  accordingly: such read-throughs stay bottom; soundness only needs the derivable case,
  where the class is the class of the actual proof field.
* R5 (extraction): the Pi observation at the weakening valuation only gives the domain
  classes in `A :: Γ`, which would need inverse weakening. Use two observations: the domain
  class at the identity valuation (`Δ = Γ`) gives `TypeChain Γ A A'`; then the codomain at
  the weakening valuation with the fresh-variable key (typed at both lifted domains by the
  first chain) gives `TypeChain (A :: Γ) B B'`. Adopted (section 3 is to be read this way).
* R6: representative invariance of classes is a purely syntactic lemma for anchored
  (coherently typed) valuations, proved before soundness; argument classes at a semantic
  domain `D` need the typing invariant identifying `D` with the syntactic domain class.
  Adopted.
* R7 (Lemma C): ordinary induction exposes uniqueness only for immediate premises, so the
  induction carries the conjunction (uniqueness, occurrence congruence) for every strong
  derivation; non-template premises are kept as typing evidence. Adopted (this is the
  motive used in `HeadInjectivity/Uniqueness.lean`).
* R8: abstract schema permission (`CaseSchema.lean`) never authorises singleton elimination
  into `Type` from a source whose level may be zero, so mode-C read-through concerns native
  recursors (and canonical `Eq.rec`) only.

## 8. Coordination with Phase 1a

The glued model contains Phase 1a's model (forget the classes). Building the model once,
with classes, would deliver both halves. The Phase 1a worker was not reachable from this
branch (no registered endpoint), so this is recorded here and in the final report. This
branch builds its own model under `HeadInjectivity/Model/`, following Phase 1a's design
(`PHASE1_NOTES.md` on `agent/verify-inductives-headinv`) wherever classes are irrelevant.

## 9. The model, revised: observations instead of shapes (decision D6)

D6. The model is built from **atomic observations** (an intersection-type / filter model
glued with classes) instead of Carneiro's depth-indexed shapes with joins. Rationale: the
only obligation is soundness (no logical relation indexed by depth), and with atomic
observations a term's denotation is a *set* of observations, so directedness and joins
are free (a "join" is a union), the read-through filter is a property of single
observations (typedness against a finite list of type observations), and the
reconstruction lemma R3 becomes trivial (equal type denotations give equal witness lists).
Soundness is stated up to the subsumption preorder `≼` (key enlargement), which replaces
Carneiro's downward closure.

### 9.1 Definitions (target context `Δ` fixed; `env`, `U` fixed)

* Classes: `TyLink A B := ∃ u, Δ ⊢ A ≡ B : sort u`, `TyCls A := EqvGen-class of A`;
  `ElLink D a b := ∃ X ∈ D, Δ ⊢ a ≡ b : X`, `ElCls D a := EqvGen-class`.
  `TypedTyCls D := ∃ A u, Δ ⊢ A : sort u ∧ D = TyCls A`;
  `TypedElCls D c := ∃ a X, X ∈ D ∧ Δ ⊢ a : X ∧ c = ElCls D a`.
* Observations:
  ```
  inductive Ob
    | sort (ℓ : List Nat → Nat)              -- the value is `sort l`, ℓ = l.eval
    | piDom (D : Set VExpr)                  -- a Pi type with domain type class D
    | piDomOb (o : Ob)                       -- ... whose domain has observation o
    | piCod (c : Set VExpr) (C : Set VExpr)  -- codomain instance at argument class c has type class C
    | piCodOb (c : Set VExpr) (K : List Ob) (o : Ob)  -- ... at argument (c, ⊇K) has observation o
    | app (D c : Set VExpr) (K : List Ob) (o : Ob)    -- a function with domain class D:
                                             --   applied to an argument of class c with
                                             --   observations ⊇ K, the result has o
    | rigid (n : Name) (ℓs : List (List Nat → Nat)) (nargs : Nat)
    | rigidArg (i : Nat) (c : Set VExpr)
    | rigidArgOb (i : Nat) (o : Ob)
    -- (later: constructor, field and quotient observations)
  ```
* Subsumption `o ≼ o'` (`o'` is weaker): structural, with keys compared contravariantly:
  `app D c K o ≼ app D c K' o'` iff `K ⊑ K'` and `o ≼ o'`, where `K ⊑ K'` iff
  `∀ k ∈ K, ∃ k' ∈ K', k' ≼ k`; likewise for `piCodOb`; congruence for `piDomOb`,
  `rigidArgOb`; reflexive on the other atoms. `↑S := {o' | ∃ o ∈ S, o ≼ o'}`.
* Valuations `ρ : List (Set VExpr × Set Ob)`; representatives `Reps ρ := {σ | ∀ i < ρ.length,
  σ i ∈ (ρ[i]).1}`; `clsOf ρ D t := ⋃_{σ ∈ Reps ρ} ElCls D (t.subst σ)`,
  `tyClsOf ρ t := ⋃_{σ ∈ Reps ρ} TyCls (t.subst σ)`.
* Typed observations `TypedOb (c : Set VExpr) (o : Ob) (τs : List Ob)` ("an observation `o`
  of a value of class `c`, typed at the type observations `τs`"), by recursion on `o`:
  sorts at `sort (ℓ+1)`; `piDom D` at some `sort` with `TypedTyCls D`; `piDomOb o` at some
  `sort` with `o` typed at some sort; `piCodOb c K o` at `sort ℓ` with `o` typed at some
  `sort ℓ'`, `ℓ = 0 → ℓ' = 0`; `app D c K o` at `τs ∋ piDom D` with `TypedElCls D c`, every
  `k ∈ K` typed (class `c`) at a list of observations `τ` with `piDomOb τ ∈ τs`, and `o`
  typed, at class `ElCls C (u x)` (`u ∈` the function's class, `x ∈ c`, `piCod c C ∈ τs`),
  at a list of observations `τ` with `piCodOb c K' τ ∈ τs`, `K' ⊑ K`; rigid observations at
  some `sort`. Consequence (proof irrelevance): nothing is typed at a list of observations
  of a type all of whose observations are typed at `sort 0`.
* `Obs ρ t o` (inductive; every occurrence of `Obs` positive):
  * `bvar`: `o ∈ (ρ[i]).2`;
  * `sort`: `.sort l.eval`;
  * `forallE A B`: `piDom (tyClsOf ρ A)`; `piDomOb o` for `Obs ρ A o`; for every typed key
    `(c, K)` at `A` (`TypedElCls (tyClsOf ρ A) c` and every `k ∈ K` typed with class `c` at
    some list of observations of `A`): `piCod c (tyClsOf ((c,K)::ρ) B)` and `piCodOb c K o`
    for `Obs ((c,K)::ρ) B o`;
  * `lam A t`: `app (tyClsOf ρ A) c K o` for every typed key `(c, K)` at `A` and
    `Obs ((c,K)::ρ) t o`;
  * `app f a`: `o` whenever `Obs ρ f (app D c K o)`, `c = clsOf ρ D a`, and
    `∀ k ∈ K, ∃ k', Obs ρ a k' ∧ k' ≼ k`;
  * `const c ls` (core: rule-free environments): the rigid spine observations
    `app D₁ c₁ K₁ (… (rigid c (ls.map eval) n | rigidArg i cᵢ | rigidArgOb i k, k ∈ Kᵢ))`,
    **filtered**: kept only if `TypedOb (class of const c ls) o τs` for a list `τs` of
    observations of `ci.type.instL ls` (closed, empty valuation).
* Typed valuation for `Γ`: an anchor `σ` with `Ctx.SubstEq env U Δ σ σ Γ`, each class the
  class of `σ i` at `TyCls ((A_i).subst σ)`, each observation of `ρ[i]` typed (with that
  class) at a list of observations of `A_i` under the tail valuation.

### 9.2 Soundness and the three lemmas it rests on

`theorem sound`: for `IsDefEqStrong U Γ t t' A` and every typed valuation `ρ` of `Γ`:
`Obs ρ t ⊆ ↑Obs ρ t'`, `Obs ρ t' ⊆ ↑Obs ρ t`, and every observation of `t` (and `t'`) is
typed (class `clsOf ρ (tyClsOf ρ A) t`) at a list of observations of `A`.

* **Class lemma** (syntactic, R6): for anchored typed `ρ` and typed `t`,
  `clsOf ρ D t = ElCls D (t.subst σ)` and `tyClsOf ρ t = TyCls (t.subst σ)` (anchor `σ`),
  by `IsDefEq.substDF` and the collapse lemma.
* **Monotonicity and compactness**: `Obs` is monotone in the observation sets of `ρ`, and
  every derivation uses finitely many of them.
* **Substitution**: `Obs ρ (t.inst a) = Obs ((clsOf ρ D a, Obs ρ a) :: ρ) t` for typed
  `t`, `a` (classes by the class lemma).

Core cases: `appDF` (the argument classes agree because the typing invariant forces
`D = tyClsOf ρ A`), `lamDF`/`forallEDF` (IH at the typed valuation `(c,K)::ρ`, anchored by a
member of `c`), `beta` (compactness, monotonicity, substitution), `eta` (typing invariant:
the observations of `f : Pi A B` are `app (tyClsOf A) c K o` with typed keys; `≼` absorbs key
enlargement), `proofIrrel` (the consequence above), `defeqDF` (equal type denotations
transfer the typing witnesses), `sortDF`/`constDF` (levels only through `eval`).

### 9.3 Milestones

* M0 classes and the class lemma; M1 observations, `≼`, `TypedOb`; M2 `Obs` and soundness for
  rule-free environments (`env.defeqs`, `env.projections`, `env.eliminators` empty), with the
  extraction giving `HeadInjectivityCore` there; M3 definitions (delta) and `Quot`; M4 native
  inductives (constructor/field observations, iota in modes AB and C, projections, structure
  eta, unit-like); M5 abstract eliminators (`elimDF`, `elimIota`).

### 9.4 Design of M3-M5 (rules, constructors, projections, eliminators)

Every computation rule of a WF environment is a definition `const c ls ≡ value`, the
quotient rule, or a restored native recursor equation (`WF'.nativeRegistry`,
`NativeRegistryOfWF.lean`); abstract eliminators reduce by their schema's generic case
equations. All of them have one **pattern shape** (`PatRule`): `lhs = wrapLams doms
(mkApps head args)`, `rhs = wrapLams doms body`, where each argument is a bound variable
(parameters, motives, minors), an ignored term (indices, and the constructor's own repeated
parameters), and, for recursors, a last argument `mkApps (const ctor ls') (ignored ++ field
variables)` (the major pattern; for `Quot.lift` it is `Quot.mk α r a`). Definitions are the
degenerate case with no arguments. A syntactic lemma per rule family shows the shape
(restoration only replaces auxiliary heads by specialised source heads in ignored positions
and in the major's head).

* One generic **rule clause**: `Obs ρ (const c ls) (app D₁ c₁ K₁ (… o))` when a stored rule
  for `c` matches the keys: bound variables take their keys directly (first occurrence wins),
  ignored positions are skipped, and the field keys come from the major key by mode:
  * mode AB (major family not a proposition at the occurrence's levels, not an eta
    structure): the major key contains `ctorHead ctor` and the field classes/observations;
  * eta structure (review R1): the field key `j` is `(class of proj S j major, {o | fieldOb j o
    ∈ K_major})`, whatever the major's observations;
  * mode C (major family a proposition at the levels, large elimination): the major is
    ignored; a data field is read from the index key at a position where the constructor's
    index is that field variable; a proof field gets `(class of all proofs of its type, ∅)`.
  and `o` is an observation of `body` under the valuation built from those keys, the whole
  chain **filtered** by `TypedOb` against observations of the head's type. Divergent
  definitions denote nothing (inductive least fixed point).
* Constructor observations: a rigid constant whose type's syntactic result is headed by a
  family `I` and which is applied as an element (not a type former) produces
  `ctorHead c ℓs n`, `ctorArg i cᵢ`, `ctorArgOb i o` (non-eta families, `Quot.mk`), or only
  `fieldOb j ks o` (eta structures: `j` a field, `ks` the observation keys of the earlier
  fields, no classes: they are the classes of the projections). Typing follows Phase 1a: the
  family's type observations carry the observations of each constructor's type instantiated
  at the type's parameter keys (`ctorTele`), and element observations are typed against those
  (precise dependent field typing, needed by proof irrelevance and eta under projections);
  no element observation is typed at a family that is a proposition at its levels, and none
  but `fieldOb` at an eta structure.
* `proj S j e`: the field observations of `e` (`fieldOb j _ o` or `ctorArgOb (nparams + j) o`).
* Soundness of `extra`/`elimIota`: the rule clause on the instantiated lhs recovers exactly
  the keys of the rhs (constructor observations of `mkApps ctor (ps ++ fs)` carry the field
  keys; in mode C the index positions are the field variables themselves and a proof field's
  key is the class of all its proofs with no observations); the filter is vacuous because both
  sides are typed at the same instantiated type. `projIota` reads the field back;
  `structEta`/`unitLike` hold because eta-structure values have only `fieldOb` observations
  (typing invariant) and `S.mk ps (proj e i)` reproduces them. `elimDF`/`constDF`: level
  invariance.

## 10. Status

* [Lean] Syntactic layer done: `HeadInjectivity/{Core,Congruence,FieldType,Uniqueness,Fields}.lean`,
  `theorem VEnv.HeadInjectivityCore.toHeadInjectivity (henv : env.WF) (core :
  env.HeadInjectivityCore) : env.HeadInjectivity` (no sorry; axioms propext, Classical.choice,
  Quot.sound). `proj_fieldType` (hardest case 3) is proved there from the core by the
  conjunction induction of section 5; no strengthening, no `HasCanonicalEq`.
  `TypeChain`/`SpineArgsEq` moved to `Typing/TypeChain.lean` (D7: the injectivity
  development must not import `HeadInversion.lean`).
* [Lean] Semantic layer M0-M2 (rule-free environments): `HeadInjectivity/Model/{Classes,Obs,
  Interp,Sound,Extract}.lean`. `theorem Model.sound (henv : env.Ordered) (hΔ : OnCtx Δ
  (env.IsType U)) (hnr : env.NoRules) (H : env.IsDefEqStrong U Γ t t' T) : SoundAt env U Δ Γ t
  t' T` and `theorem VEnv.WF.headInjectivityCore_of_noRules (henv : env.WF) (hnr :
  env.NoRules) : env.HeadInjectivityCore` (no sorry; axioms propext, Classical.choice,
  Quot.sound). Imports only the uniqueness-free base.
* [plan] M3-M5 (section 9.3).

### 10.1 Deviations of the M0-M2 formalisation from section 9.1

* **Valuations are anchored** (`Interp.lean`): a valuation is an anchor substitution `σ`
  (from `Γ` into `Δ`) together with observation sets `S : Nat → Ob → Prop`; classes are
  computed from the anchor (`TyCls Δ (A.subst σ)`, `ElCls Δ D (a.subst σ)`), and a key
  `(c, K)` extends the anchor by a representative `x ∈ c`. Reason: with classes taken as
  unions over representatives, the substitution lemma (`Obs ρ (t.inst a)` against the
  extended valuation) holds only when the domain class `D` of every `app` observation met
  inside `t` is the type class of the argument, which is the typing invariant, i.e.
  soundness itself. With anchors the substitution lemma (`Obs.subst_iff`, `Obs.inst_iff`)
  is syntactic. The union-over-representatives classes are still defined (`clsOf`,
  `tyClsOf`) and agree with the anchored ones at anchored typed valuations
  (`clsOf_anchored`, `tyClsOf_anchored`).
* **Soundness relates two related anchors** (`SoundAt`): for `Ctx.SubstEq Δ σ σ' Γ` and
  shared observation sets, `Obs σ S t ⊆ ↑Obs σ' S t'` and back, plus the typing invariant
  for both sides. Reason: `beta` must replace the key's representative by the actual
  argument (they are only definitionally equal), which is representative invariance; with
  two anchors in the motive it is an instance of the induction hypothesis. Variables read
  their observations from `S`, never from the anchor, so the `bvar` case is trivial.
* `TyCls`/`ElCls` are `A = B ∨ TransGen link` rather than `EqvGen` (equivalent: links are
  symmetric). `TypedOb` has no value-class parameter and `rigidArgOb` is omitted (only the
  key typing of `rigidArgOb` needed the value class; M2 does not need `rigidArgOb`).
  `piCod c C` carries no key list. `Covers K' K` ("every key of `K` is subsumed by one of
  `K'`") is the notes' `K ⊑ K'`. `Ob.Le` has a `refl` constructor and compares key lists
  through an explicit choice function (no nested inductive occurrence); transitivity is
  proved jointly as pre- and post-composition.
* The constant clause's filter reads the observations of `ci.type.instL ls` at the fixed
  valuation `(id, ∅)` (the type is closed; `Obs.closed_iff` shows the valuation is
  irrelevant there), so the structural lemmas need no closedness. No separate level
  invariance lemma: `constDF` uses the induction hypothesis of its `[]` type premise, and
  `sortDF`/`constDF` compare levels only through `VLevel.eval`.
* Extraction (`Extract.lean`): `former_args` reads the domain classes of the left spine
  observation off the syntactic telescope (`tele_spine`): the spine observation passes the
  constant's filter, so it is typed at observations of `wrapForalls doms (sort w)`, whose
  `piDom`/`piCodOb` observations force each key's domain class to be the class of the
  instantiated telescope domain.

(updated as the work proceeds)

* [Lean] Rule pattern shape (9.4) done: `HeadInjectivity/Rules/{PatShape,Coverage}.lean`
  define `PatArgs`/`VDefEq.PatShape` and prove `VEnv.WF.defeq_patShape` (every installed
  rule is a definition `const c ls ≡ closed value` or `PatShape (const c ls)`; also
  `defeq_patShape_const`) and `VEnv.WF.genericEquation_patShape` (generic case equations,
  head `elim block owner (param 0 :: genericLevels)`), both from the general
  `Instance.equation_patShape` (any head mode, any restoration whose heads consume at most
  the common parameters and do not rename the recursor head). Rule origin is recomputed by
  `VEnv.WF'.defeq_origin` because `NativeRegistryOfWF` transitively imports `ChurchRosser`
  and `HeadInversion`. No sorry; axioms propext, Classical.choice, Quot.sound.
