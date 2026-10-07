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
* [Lean] Stage A1 (section 10.2): `theorem VEnv.WF.headInjectivityCore_of_defsOnly (henv :
  env.WF) (hdo : env.DefsOnly) : env.HeadInjectivityCore` (every rule a definition's delta
  rule, no projections, no eliminators), via `Model.sound (henv : env.Ordered) (hΔ) (hdo :
  env.DefsOnly) (hdr : env.DefRules)` and the stage-independent extraction
  `VEnv.WF.headInjectivityCore_of_sound (henv : env.WF) (hs : Model.SoundEnv env)`.
  `VEnv.WF.defRules` (`Rules/Definitions.lean`): delta rules are unique per constant,
  exclude every other rule headed by it, and carry the constant's type. Axioms propext,
  Classical.choice, Quot.sound.
* [Lean] Stage A2: `theorem VEnv.WF.headInjectivityCore_of_defsQuot (henv : env.WF) (hdq :
  env.DefsQuot) : env.HeadInjectivityCore` (every rule a delta rule or the quotient rule, the
  quotient constants those of `addQuot`, no projections, no eliminators). The quotient rule
  is an instance of the generic pattern-rule theorem `Model.sound_pat`
  (`Model/RuleSound.lean`), which is stated for any rule with a constructor major given its
  syntactic facts (pattern, binder coverage, `HeadFam`, rule uniqueness per head and
  constructor, propositional major-only fields in mode C); `Model/QuotRule.lean` proves
  those facts for `quotDefEq` (both modes occur: `Quot` at a level that is identically zero
  is a proposition). Infrastructure: `Model/Tele.lean` (typed key telescopes), `Model/HTS.lean`
  (semantic typing derivations, the spine lemma), `Model/RuleLemmas.lean`.
* [Lean] Stages B and D (D11 implemented): `theorem VEnv.WF.headInjectivityCore_of_projElimFree
  (henv : env.WF) (hB : env.ProjElimFree) : env.HeadInjectivityCore` (`Model/Staged.lean`),
  where `ProjElimFree` is: no projections and no eliminators. Every native recursor rule is
  covered: ordinary and nested compilations, every elimination mode (data families,
  elimination into `Prop`, singleton large elimination and K-like rules). It subsumes
  `DefsQuot`. Axioms propext, Classical.choice, Quot.sound. Structure:
  - `RuleValid` now has explicit binders (implicit ones were instantiated eagerly by `exact`).
  - `Rules/NativeOrdinary.lean`: for `auxiliaries = []` the restoration is `{}`; the pattern
    decomposition of `g.equation index` (`eqDoms`, `eqLead`, `eqMs`, `eqFs`), coverage, the
    recursor type `wrapForalls (g.recDoms owner) RH` with its major domain
    `mkApps (const family g.levels) _`, recursor-name and constructor injectivity, the
    installed constructor's family (`CompilationData.ordinary_ctor`), and
    `expanded.typeConstants = source.typeConstants`.
  - `Model/NativeSem.lean`: `family_sort` (observation chains of a type soundly equal to a
    telescope ending in `Sort l` end in `l`), `motive_tele_empty`/`rhs_empty_motive` (a rule
    whose type is a telescope over a motive into `Prop` has a right-hand side without
    observations), `sound_pat_empty`.
  - `Model/NativeRule.lean`: `FamSort env I l`, `HeadExcl`, `ProofBinder`, `native_uniq`,
    `native_C_absurd` (mode C is impossible when the family sort is never zero), and
    `RuleValid.native`, split on `Instance.Admissible.elimination`: never-zero families via
    `sound_pat` with a contradictory `hC`; small elimination via `sound_pat_empty`; singleton
    elimination via `sound_pat` in mode C. `RuleValid.quot` takes `QuotConsts` and uniqueness
    per head instead of `DefsQuot`.
  - `Model/Singleton.lean`: `proofBinder_of` (a binder typed at `Sort 0` in an earlier
    environment with valid rules is a `ProofBinder`) and `singleton_field_typing` (the field
    typings of `SingletonElimination`, weakened past the motives and minors and the later
    fields, type the equation's field binders at `Sort 0` in the environment in which the
    block's rules are typed).
  - `Model/Staged.lean`: `Model.famSort` proves `FamSort` for an ordinary family from
    `RestoresFamily.type` (Finding 1 resolved for ordinary families): the derivation lives in
    the environment with the family headers added to the environment before the declaration,
    which is ordered and whose rules are valid by the induction hypothesis, so `Model.sound`
    applies to it in the model of the final environment. `VEnv.WF'.ruleValid` is the D11
    induction over the declaration history; it carries `HeadsClosed envF env` (no later
    declaration of `envF` adds a rule headed by a constant of `env`), which gives uniqueness
    per head for the compilation that actually installed the rule. (A first version used
    `Rules/Batches.lean`, `VEnv.WF.sameHead`, whose batch witness need not be the installing
    compilation; it is kept but no longer used.)
  - Nested compilations: `Rules/NativeNested.lean` (restored equations and recursor types,
    restored-name injectivity, `CompilationData.ctor_origin`, `family_origin`,
    `nested_families` (at least two families, so singleton elimination does not occur),
    `CertifiedSpecializations.mem`) and `Model/NestedRule.lean` (`RuleValid.nested`,
    `famSort_container`: `FamSort` of a container family from the container's own
    compilation, in the environment before the nested declaration). `Model/FamSort.lean`:
    `famSort_of`, `FamSort` from a family's declared shape in any earlier environment.
* [plan] Stages B-E (section 10.2). Handoff for stage B (native recursors, mode AB): each
  compilation equation must be shown to satisfy the hypotheses of `Model.sound_pat`:
  pattern and coverage (`Instance.equation_patShape_strong`), `df.uvars = g.uvars` for
  `hlsP`, `HeadFam` (the installed recursor's type is the restored `Instance.recursorType`,
  a telescope of `majorOffset + 1` domains whose last is an application of the restored
  family head; see `NativeRecursorData.recursorType_major` and
  `NativeRecursorRegistered.family_head_rigid` in `Typing/NativeMajorFamily.lean`, which
  cannot be imported (it imports `ProjectionLemmas` → `Injectivity`) and must be re-derived),
  the constructor's family (`WF.native_constructor_result_rigid`), uniqueness per head and
  constructor (`NativeRecursorRegistered.constructor_index_unique` pattern, plus head
  freshness as in `Rules/Definitions.lean`), and the exclusion of mode C (stage B hypothesis).
  Pitfall: `lead.length = majorOffset` needs `ctor.indices.length = family.indices.length`.

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

### 10.2 Design of M3-M5 at the observation level (written before stage A)

This section fixes every extension of `Ob`, `TypedOb` and `Obs` needed by the remaining
stages, so that later stages add proofs, not observations. Tags as in the rest of the file.

**Stages** (each ends in a committed theorem under an honest intermediate hypothesis):
A1 every rule is a definition, no projections, no eliminators; A2 + the quotient rule;
B + native recursors in mode AB on families without projections; C + projections (`proj`,
`projIota`, `structEta`, `unitLike`, eta-structure iota by projections, review R1);
D + mode C (proposition families with large elimination: K-like and singleton); E + abstract
eliminators (`elimDF`, `elimIota`); then the general `VEnv.WF.headInjectivityCore`.

**D8 (level-saturated classes).** `TyCls`/`ElCls` are closed under `LvEq` (terms that differ
only by `≈`-equivalent levels; reflexive on every term, closed under substitution). For a
typed term this adds nothing (`EqUpToLevels.defeq`), so the collapse lemma and the anchored
class lemma are unchanged in content. Gain: `Obs` is invariant under `LvEq` *structurally*
(`Obs.lvEq`, induction on `Obs`), which is exactly what `constDF` at a defined constant or a
rule-headed constant needs (the observations of `value.instL ls` and `value.instL ls'`), and
which cannot come from the induction hypotheses of `constDF` (its premises say nothing about
the value). Rejected alternative: a level-invariance component in the soundness motive (it
fails at the same `constDF` leaf).

**D9 (semantic typing derivations in the motive).** The rule cases need soundness of
*sub-derivations* of the rule's typing premises (the arguments of the left spine, the major's
constructor spine, the constant types whose rigid observations type constructor
observations). `IsDefEqStrong`'s induction gives only immediate premises. So the soundness
motive becomes `SoundAt Γ t t' T ∧ HTS Γ t T ∧ HTS Γ t' T`, where `HTS` ("semantically
typed") mirrors `HasTypeStrong` (bvar, sort, const (with `HTS [] (ci.type.instL ls) (sort u)`),
elim, app, proj, lam, forallE, conv), every `IsDefEqStrong` premise of `HasTypeStrong`
being replaced by the premise together with its `SoundAt`, and every typing premise by
`HTS` together with its `SoundAt`. Each case of the soundness induction builds `HTS` for both
sides from the premises exactly as `IsDefEqStrong.hasType'` builds `HasTypeStrong`. The
**spine lemma** (generalising `Extract.spine_typed`, by induction on `HTS`, no global
soundness): for `HTS Γ (mkApps h args) T` with `h` a constant (or `elim`) head, a typed
valuation and type observations `τs ⊆ Obs T`, there are keys of the arguments (any key lists
`K_i ⊆ Obs args_i` containing given finite demands) whose domain classes are `TyCls (A_i σ)`
for the derivation's domains `A_i` (with `HTS Γ args_i A_i`), such that every `o` typed at `τs`
gives `wrap keys o` typed at observations of the head's type, and conversely type
observations of the head's instantiated codomain are covered by those of `T` (both
directions of `Ob.Sub`, from the `conv` nodes). For a bare variable argument the `HTS`
derivation is `bvar` followed by `conv`s, so its domain class is the class of its context
type (the fact that keeps representatives of rule variables inside their own type's class).
Through `lam` nodes the lemma reads the body of a rule's left-hand side.

**Observations** (`Ob`, final list): the M2 atoms `sort piDom piDomOb piCod piCodOb app
rigid rigidArg`, and
* `rigidArgOb (i : Nat) (o : Ob)`: the `i`-th argument of a rigid spine has `o` (pins the
  parameter keys recorded by field observations to the type, stage C);
* `ctorHead (c : Name) (ℓs) (n : Nat)`, `ctorArg (i : Nat) (cls)`, `ctorArgOb (i : Nat)
  (pre : List Key) (o : Ob)`: a constructor application of `c` at levels `ℓs` to `n`
  arguments, the class of argument `i`, an observation of argument `i` (with the keys of the
  earlier arguments, for stage C typing). Produced for constructors of families that are not
  eta structures, and for `Quot.mk`;
* `fieldOb (j : Nat) (pre : List Key) (o : Ob)`: field `j` of an eta-structure value has `o`;
  `pre` holds the parameter keys and the earlier fields' observation lists (no field classes:
  the class of field `j` is always the class of `proj S j e`, review R1).
`Ob.Le`: `rigidArgOb`, `ctorArgOb`, `fieldOb` are covariant in `o`; `pre` is an annotation,
compared by equality.

**Typing** (`TypedOb`): `rigid n ℓs m` needs `.sort ℓ ∈ τs` and `RigidSort n ℓs m ℓ` (if `n`'s
type is syntactically an `m`-telescope ending in `sort w`, then `ℓ = w` evaluated at `ℓs`);
`rigidArg`, `rigidArgOb` at some sort. Constructor observations need an indicator
`rigid I ℓs' m ∈ τs` with `CtorOf c I` and `NonProp I ℓs' m` (the family's declared sort at
`ℓs'` is not identically zero); with `RigidSort` this gives `TypedOb.not_prop` (proof
irrelevance) for constructor observations. Constructor observations are not typed at eta
structures, `fieldOb` only at eta structures (for `structEta`/`unitLike`). The *values* inside
constructor observations need no typing of their own in stages A2-B: the rule clause binds
fields from them and soundness compares those bindings with the actual (typed) valuation
by `≼` and monotonicity. Stage C needs precise typing of `fieldOb` (projection typing
invariant with dependent fields), which depends on the value's class (the class of
`proj S i e`); [plan] `TypedOb` then gains the value class (the original 9.1 parameter),
with the result class of an `app` observation read from `piCod`.

**Constant clauses** of `Obs (const n ls)`:
* rigid (M2) now requires `env.Rigid n`;
* constructor: `CtorOf n I` (and `n` not an eta-structure constructor, or `n = Quot.mk`):
  chains `wrap keys r`, `r ∈ {ctorHead n ℓs keys.length, ctorArg i cᵢ, ctorArgOb i
  keys[:i] k (k ∈ Kᵢ)}`, filtered by typing at observations of `n`'s type, as the rigid clause;
  eta-structure constructors: `r = fieldOb j pre k` (`k` in the key of field `j`). A constructor
  is also rigid, so it keeps its rigid chains (used only when the spine is a type);
* delta: `env.defeqs df`, `df.lhs = const n (params df.uvars)`: every observation of
  `df.rhs.instL ls` (closed; valuation `(id, ∅)`), filtered by typing at `ci.type.instL ls`;
* rule (stages A2-E): `df` a stored rule (or generic equation) with `PatShape` at `const n
  (params)` (or the `elim` head): `wrapLams doms (mkApps head args)`, `PatArgs`. A chain
  `wrap keys o` with `keys.length = args.length` is admitted when there is an anchor `τ` and
  observation sets `S'` for the rule binders such that, for each binder `x`:
  - if `bvar x` occurs bare in the leading arguments, at the first such position `i`:
    `τ x ∈ cᵢ`, `cᵢ` a typed class at `TyCls (A_x.subst τ)` (`A_x` the binder's type in the
    rule context), `S' x = Kᵢ`;
  - otherwise `x` is the `j`-th field variable of the major, and by the mode of `(df, ls)`:
    AB: the major key holds `ctorHead ctor ℓs n` with `n = |ms| + |fs|`, `ctorArg (|ms|+j) c`
    with `τ x ∈ c` typed at `TyCls (A_x.subst τ)`, and `S' x = {k | ctorArgOb (|ms|+j) _ k ∈ K}`;
    eta (stage C): `τ x` in the class of `proj S j m` for a member `m` of the major's class,
    `S' x = {k | fieldOb j _ k ∈ K}`; C (stage D): `τ x` any term typed at `A_x.subst τ` with
    `A_x.subst τ : sort 0`, `S' x = ∅` (data fields of a singleton are bare index variables,
    so they are bound by the first rule);
  and `o ∈ Obs τ S' body`; the chain is filtered by typing at observations of the head's
  type at `ls`. The mode of `(df, ls)` is a declarative predicate from the rule's compilation
  data (the major's family at `ls` is a proposition: mode C; an eta structure: eta; else AB),
  with a uniqueness lemma; mode C fires only for proposition families, and never by
  inspecting the major key (monotonicity). Divergent definitions denote nothing.
* `elim b o ls` (stage E): the rule clause over the schema's generic equations; no rigid
  clause (eliminators are never rigid).
* `proj S j e` (stage C): `k` whenever `e` has `fieldOb j _ k` or `ctorArgOb (np + j) _ k`.

**Soundness of the rule cases.** `extra`/`elimIota` at a pattern rule: the left side's
observations are `lam`-chains over the rule binders of chains of the head; right-to-left,
an observation `o` of the body at the binder valuation `v` is typed at the body type (typing
invariant of the right side), the spine lemma on the left side's `HTS` gives keys whose
classes are the binder classes (bare variables) and whose major key carries the constructor
observations (spine lemma on the major's `HTS`; the family indicator in the major's type
comes from the spine lemma on the family spine inside the head's type, through the `HTS`
of the constant's type), and the chain is typed; the clause holds with `τ = v`. Left to
right, the clause's rule is the given one (rule uniqueness per head and constructor;
definitions exclude pattern rules for the same head), and the body at `(τ, S')` is compared
with the body at `v` by the body's `SoundAt` (from the `HTS` of the right side's `lam` nodes:
`τ x ≡ v x` at `A_x` by the class condition and the collapse lemma) and `Obs.mono_le`
(`S' x` is covered by the actual observations). Definitions: the delta clause, both
directions, with `Obs.lvEq` for `constDF`. `projIota` reads the field back; `structEta`/
`unitLike` use that eta-structure values have only `fieldOb` observations; `projDF` is
congruence; `elimDF`/`constDF` level invariance through eval and `Obs.lvEq`.

**Extraction**: `rigid_rigid`/`former_args` are stated for `env.Rigid` heads, whose
observations are the rigid ones only (the constructor clause adds no `rigid`/`rigidArg`
observations, the delta and rule clauses need a rule headed by the constant).

### 10.3 Findings at the start of stage B, and redesigns D10, D11

Finding 1 (non-syntactic family types). `VInductDecl.TypeShape` (Theory/InductiveShape.lean)
only requires a family's type to be *definitionally* equal to a telescope ending in a sort;
the stored type need not be syntactically `wrapForalls ds (sort w)`. The M1/A2 predicates
`RigidSort`, `NonProp`, `MajorSort` read the sort syntactically, so for such a family the
constructor indicator `NonProp` is false, constructor observations are never typed, the
rule clause never fires in mode AB, and `extra` at its iota rules is unsound in the model.
Constructor types, by contrast, are syntactic (`RawCtorShape`), and generated recursor
types are syntactic (`Instance.recursorType`, preserved by restoration).

Finding 2 (declarative versus semantic propositions). Inside the soundness induction the
model only knows the *derivation* sorts of types (the sorts in the `HTS` derivations of the
premises). Facts established when a block was compiled (a family's result level, the
propositional typing of a singleton's proof fields, small elimination for multi-constructor
propositions) are derivations in an earlier environment and are not sub-derivations of the
current node. Relating the two needs sort uniqueness, i.e. the result being proved. Where it
is needed: (a) mode C at a singleton with proof fields (the right-to-left direction must show
that the actual lambda keys of proof fields have no observations), (b) relating the semantic
sort of the major's family to the elimination restriction recorded at compilation. Not
needed: K-like rules (no fields), the quotient (its field's type is a binder whose own type
is the syntactic `Sort u`), and every mode AB rule.

D10 (rigid observations carry their sort; semantic modes) [Lean, superseding the `RigidSort`/`NonProp`/`MajorSort` parts of 10.2]. `Ob.rigid n ℓs m s`
records the sort `s` of the rigid spine, typed exactly at `.sort s` (no `RigidSort`); the
constructor indicator becomes `rigid I ℓs m s ∈ τs ∧ CtorFam c I ∧ s ≠ 0`, which gives proof
irrelevance with no syntactic reading of family types. The rule clause decides mode C by a
positive semantic condition: the head is the only rule head of its kind (a declarative
condition on `env.defeqs`) and the major domain of the head's type at the clause's key prefix
has a rigid observation of sort zero (an `Obs` premise, monotone and level invariant). Mode AB
needs no mode condition (constructor observations in the major key exist only for
non-propositions). In the soundness proof the two modes are separated by the derivation sort
of the major domain (spine lemma P2). Extraction no longer needs `RigidSort`. In Lean: the
rule clause carries `mC = true → (single rule for the head)` and `mC = true → Obs id ∅
(head type) (piCodChain lkeys (piDomOb (rigid I ℓs m 0)))`; `Model.sound_pat` takes the head's
major family data explicitly and a hypothesis `hC` giving, from that zero-sort observation,
single-rule-ness and the propositional typing of the major-only fields (`QuotRule.lean`
proves it for the quotient from `Quot`'s syntactic type, `quot_C_level`).

D11 (staged soundness) [plan]. Soundness is proved by induction along the declaration
history: a predicate `RuleValid env' df` collects the *semantic* facts of a rule that come
from its compilation (field types of a singleton's proof fields have only sort-zero type
observations; the semantic sort of the major family equals the recorded result level), and
`RuleValid env' df` for the rules added by one declaration is proved from the soundness, in
the model of the final environment `env'`, of the derivations of the environment before that
declaration (they are derivations of `env'` by monotonicity, and their rule cases only involve
earlier rules, whose validity is the induction hypothesis). `Model.sound` then takes
`∀ df ∈ E.defeqs, RuleValid env' df` for derivations of a prefix `E ≤ env'`.

D11, refined (the plan being implemented). `RuleValid env df` is the statement of the
`extra` case of soundness for the rule `df` in the model of `env`: for every target context,
context `Γ` and well-formed levels `ls` with `ls.length = df.uvars`, if the typing premises of
`extra` (`df.type`, `df.lhs`, `df.rhs` at `ls`, in `[]` and in `Γ`) are sound and semantically
typed, then `df.lhs.instL ls ≡ df.rhs.instL ls` is sound. `Model.sound` is restated for
derivations of any environment `E ≤ env` whose rules are valid in the model of `env`; its
`extra` case is the hypothesis. Validity is proved per rule kind: delta rules (the A1
argument), the quotient rule (`sound_pat` with the quotient facts), native rules (`sound_pat`
with the compilation facts; the semantic facts — the major family's semantic sort is its
recorded result level, small elimination empties the right-hand side, a singleton's proof
fields have only sort-zero type observations — come from the soundness, in the model of `env`,
of derivations of the environment preceding the rule's declaration). The final theorem proves
validity of every rule by induction on the `VEnv.WF'` derivation, calling `Model.sound` on the
earlier environments.

Note for the native mode-C/AB split: in `pat_rhs_sub` the split is on the derivation sort `u`
of the major domain of the head's type. A data family needs `u ≠ 0`, which only the semantic
link to the recorded result level gives (the family's own type need not be syntactic); a
proposition with several constructors has small elimination, whose right-hand sides have no
observations (the motive's binder type is syntactically `... → Sort target` with
`target ≈ 0`, so `chain_terminal_sort` types every observation of the motive application at
`[sort 0]`); a proposition with one constructor and large elimination is the singleton case.
`sound_pat`'s hypothesis `hC` must accordingly be weakened to "single rule and proof fields, or
the right-hand side has no observations, or contradiction".

### 10.4 Plan for stage E (abstract eliminators), as being implemented

Case schemas are per-family views without induction hypotheses, and their permission is
`ProjectionAdmissible` (source sort never zero, or target `≈ 0`): no singleton elimination,
so the eliminator rule clause needs mode AB only (mode C is contradictory by `FamSort`, and
with a zero target the right-hand side has no observations). Eliminator heads are never
rigid and have no delta or constructor observations: their only observations are chains of
the eliminator rule clause.

* E1 `HTS`: an `elim` constructor (head type `type.instL ls` from `schema.genericType`, with
  its `HTS`/`SD`), `other` excluding eliminator spines; the spine lemma generalized to heads
  that are constants or eliminators (`HTS.spine` for constants is kept as a corollary).
* E2 `Obs`: a constructor `elimRule` for `.elim b o ls`: a generic equation `df` of a registered
  schema for owner `o`, pattern-shaped with head `.elim b o lsP`, chains `wrap (lkeys ++ [major
  key]) p` filtered by typing at `type.instL ls`, mode AB binding (`RuleBind … false …`), the
  major key containing the constructor head; structural lemmas extended.
* E3 `Model.sound`: `elimDF` by level invariance (as `constDF`); `elimIota` from a validity
  hypothesis for generic equations (`ElimRuleValid`, the analogue of `RuleValid`).
* E4 `pat_lhs_sub`/`pat_rhs_sub`/`sound_pat` for eliminator heads (mode AB only).
* E5 syntax of generic equations (`CaseSchema.Generates` facts in
  `Inductive/CaseReductionLemmas.lean`), the generic type's major domain, uniqueness per
  `(block, owner)` (schemas are registered under fresh keys).
* E6 the D11 induction's `inductEliminators` step; `FamSort` for the schema's families from the
  certified compilation.

[Lean] Stage E is complete: `theorem VEnv.WF.headInjectivityCore_of_projFree (henv : env.WF)
(hB : env.ProjFree) : env.HeadInjectivityCore` (`Model/Staged.lean`); `ProjFree` is the absence
of projections only. Axioms propext, Classical.choice, Quot.sound. Pieces: `HTS.elim` and
`HTS.spineH` (E1); `Obs.elimRule` (E2); `ElimValid`/`ElimsValid` and the `elimDF`/`elimIota`
cases of `Model.sound` (E3); `Model/ElimRuleSound.lean` (E4); `Model/ElimRule.lean`
(`ElimValid.of_certified`, from the restored abstract equations of the owner's view, E5);
the `inductEliminators` step of `WF'.ruleValid`, which now proves validity of the rules and of
the eliminator rules of every environment of the history (E6). Design changes made on the
way: `HTS.elim` types the head in the derivation's context (`elimDF` has no closed-context
premise and context strengthening is unavailable), so the spine lemma returns the head's type
derivation in `[]` or in the derivation's context and `major_indicator_gen` reads the family
indicator at a typed valuation of that context; `IsCtor` now also holds for constructors of
generated case rules (`IsCaseCtor`), since a block registered for case analysis need not have
installed native rules (structures installed by `inductProjections`), and constructor
observations are what the eliminator rule clause binds fields from; `ElimValid` carries
`RuleClosed`; `C_absurd_gen` takes never-zero at the instantiated levels; `HeadsClosed.of_decl`
separates the downward preservation of `HeadsClosed`.

Remaining: stage C (projections: `projDF`, `projIota`, `structEta`, `unitLike`), see 10.2.

### 10.5 Stage C (projections): analysis and plan (handoff)

Stage C is the only remaining stage: `projDF`, `projIota`, `structEta`, `unitLike`
(`Model.sound` still assumes `∀ n p, ¬ E.projections n p`). It needs a redesign of the
observation model, not only new proofs. The analysis:

1. `structEta` (`mk ps (proj 0 e) … ≡ e` for every `e : S ps`, `nindices = 0`) and `unitLike`
   force the observations of values of a projection-registered family to be determined by their
   fields: a variable `x : S ps` may carry any typed observation set, in particular none, so the
   constructor spine `mk ps (proj e)…` must not have `ctorHead`/`ctorArg` observations. Plan
   (as in 10.2): constructors of projection-registered families (`IsProjCtor env c`: some
   `env.projections S info` with `info.ctorName = c`) produce only
   `fieldOb S ℓs j pre k` chains (field `j` has observation `k`; `ℓs` the evaluated levels, `pre`
   the parameter keys), and `TypedOb.fieldOb` types it at a rigid `S ℓs` observation of non-zero
   sort whose `rigidArg i`/`rigidArgOb i` observations agree with `pre` (parameter classes and
   observations; no `Obs` needed). `Ob.fieldOb` must be changed accordingly (it exists, unused).
2. `proj S j e` observes `k` when `e` has `fieldOb S ℓs j pre k`, filtered by typing at the
   `j`-th field domain of `info.ctorType.instL ls` (`ls.map eval = ℓs`) under the valuation
   sending the parameters to anchors of the classes in `pre` (with their observation lists) and
   the earlier fields `i < j` to `proj S i (e.subst σ)` with observation sets
   `Obs σ S (proj S i e)` (positive occurrences of `Obs`, as in the rule clause). This keeps
   `TypedOb` free of value classes. The typing invariant for `projDF` then needs the semantic
   invariance of the constructor type at related valuations: `SoundAt` of
   `info.ctorType.instL ls` (closed), a semantic fact of the kind of `FamSort`, proved at the
   `induct`/`inductProjections` step from the soundness of the constructor's typing derivation
   in the earlier environment (D11), together with the identification of `info` with the
   installed constructor (re-derive from `VInductDecl.projectionEntries`; the existing
   `ProjectionShape`/`ProjectionProgramTyping` lemmas import forbidden modules).
3. The rule clauses (native `rule` and `elimRule`) need a third binding mode, eta: for a
   major of a projection-registered family the fields are bound from the `fieldOb`
   observations of the major key, the anchor of field `j` in the class of `proj S j m` for `m` in
   the major's class (review R1); no `ctorHead` is required (unit-like structures have none).
   `RuleBind`, `pat_lhs_sub`/`pat_rhs_sub` and their eliminator versions gain this case;
   `RuleValid.native`/`nested`/`ElimValid.of_certified` select it when the constructor is a
   projection constructor.
4. Soundness cases: `projDF` (congruence; typing by item 2), `projIota` (both directions as for
   a pattern rule with the virtual head `proj S j`; the right-to-left direction types the field's
   observation at the field domain via the constructor spine keys), `structEta` (both sides have
   the same `fieldOb` observations: the spine's field keys are the observations of
   `proj S j e`), `unitLike` (no observations on either side). `HTS` needs a `proj` constructor
   carrying the premises of `HasTypeStrong.proj` (currently `proj` terms are `HTS.other`).

Estimated size: comparable to stages B, D and E together. The D11 induction (`WF'.ruleValid`)
and `HeadsClosed` need no change of structure: projections are registered by `induct`
(with the block) and by `inductProjections`, and the semantic projection facts are proved at
those steps from the induction hypothesis, like `FamSort`.

### 10.6 Stage C: why the plan of 10.5 is incomplete, and redesign D12

Findings (stage C agent, before any Lean change):

1. **Typing of field observations is not a property of single observations.** The type of
   field `j` depends on the *observations* of the earlier fields (e.g. `x : B b` with `B` a
   parameter function, or `if b then Nat → Nat else Bool`). With field-local observations
   `fieldOb j k` (which `structEta` forces: a variable `e : S ps` has an arbitrary finite typed
   observation set, and `mk ps (proj 0 e) …` must reproduce it from its projections), the
   typing of `k` needs the whole observation set of the value. 10.5 puts that typing in a
   filter of the `proj` clause; but then `structEta` (right to left) needs every field
   observation of an arbitrary typed `e` to pass the filter, which is again a set-level
   property, and the filter needs the *parameters' observation sets*, which `proj S j e` does
   not know (parameters are not arguments of `proj`). Recording parameter keys or earlier-field
   contexts in the observation fails `structEta` left to right (the reconstruction combines
   field observations of different observations of `e`; atomic `≼` has no conjunction).
2. **Claim world versus anchor world.** A valuation's observation sets may "claim" things its
   anchors do not satisfy (`x : Option Unit` anchored at `none` with the claim `ctorHead some`).
   Rule clauses then compute in the claim world. For non-projection families this is harmless,
   because every typing condition that mentions a class (Pi domains) is read from the type at
   the actual anchors. For structures it is not: `proj 1 (Option.rec d f x)` with
   `structure T where (A : Type) (g : A → Nat)` gets `g`'s observation from the claim world
   (domain class `Bool`) while its declared type `proj 0 t → Nat` has the anchor-world domain
   class. Concretely, the typing invariant of `projDF` is false unless field typing is checked
   *against the value's own class* in the rule clause filters.
3. **Projections of constructor spines are not declaratively linked to the fields** without
   typing facts for the projections (`proj i (mk ps fs) ≡ fs_i` needs `proj i (mk ps fs)` typed,
   i.e. the field types typed, i.e. the parameters typed along the constructor telescope). In a
   never-zero structure these facts are derivable, the parameter typing coming from the model
   (the rigid observation of `S ls ps` is typed at the family's type, whose observations are
   those of its normalized telescope by the soundness of `TypeShape` in an earlier environment).

Design D12 (being implemented):

* `TypedOb` gains the **value class** `cv` (the original 9.1 parameter): `TypedOb cv o τs`.
  `app` results are typed at `appCls cv c C` (`piCod c C ∈ τs`), keys at their own class `c`.
  `TypedAt σ S t T o` uses `cv := ElCls (TyCls (T.subst σ)) (t.subst σ)`.
* Field observations `fieldOb S j L k` (field `j` has `k`; `L` lists observations of the earlier
  fields, the typing context), compared by `≼` ignoring `L`. Typed only at a rigid `S`
  observation of never-zero sort, at the *type observations* `fieldTy S j FL τ` / `fieldDom S j FL D`
  of the family application (the field domain's observations at the parameters of the type's
  spine and at earlier fields keyed by `FL`), where `FL`'s classes are the projections
  `projCls S i cv D_i` of the value class, and the context's own observations are typed
  (so typing is inherited by the canonical witnesses below).
* **Backing** `Bk`: an observation set contains, with `fieldOb S j L k`, the canonical witnesses
  `fieldOb S i (L.take i) y` (`y ∈ L[i]`), hereditarily through `app` (same key), `fieldOb`
  (same context) and `ctorArgOb`. `Bk` is structural (keys in clauses are required backed;
  filters keep witnesses because a typed field observation types its witnesses), so
  `Obs σ S t` is backed for backed valuations. Finite key lists are closed under witnesses
  (witnesses are smaller observations).
* `proj S j e` observes `k` iff `e` has `fieldOb S j _ k`: no filter. `projDF` is congruence; its
  typing uses `Bk` (contexts are actual) and the projection lemmas (anchors `proj i w`).
* Constructors of projection-registered families produce only `fieldOb` chains (and their rigid
  chains); rule clauses on such families use the eta binding mode (fields bound from `fieldOb`
  observations, anchored at `proj j m`), which subsumes mode C for them.

### 10.7 Stage C completion plan (2026-10-07, resumed lead)

State at resumption: D12 infrastructure in place (`fieldOb`/`fieldTy`/`fieldDom`, backing,
`projCtor`/`famTy`/`famDom`/`proj` clauses, `proj_obs_typed`, `tele_wind`, `tele_compact`,
`spine_tele`, `ctor_projCls`, `paramBridge`, `familyTele_data`, `ctorTypePiSD`), `HTS.proj`.
Remaining, with the decisions taken (recorded as D15-D17 in `PHASE1_NOTES.md`):

1. **Projection validity (D15).** `Model.ProjValid env S info` (`Model/ProjValid.lean`): static
   facts (`ProjStatic`, proved for WF environments) and soundness, in the model of `env`, of the
   types environment of the entry's origin (`ProjOriginAt`). `Model.sound` takes
   `∀ n p, E.projections n p → ProjValid env n p` instead of excluding projections; the D11
   history induction proves it at the step that registers the entry (its types environment is
   earlier in the history).
2. **Field observations of constructor spines** (`ctor_field_obs`): for a never-zero entry, every
   observation `k` of field `j` of a semantically typed spine `mk ps fs` gives an observation
   `fieldOb S j L k` of the spine. Built from `spine_tele`, `tele_compact` and `tele_wind`; the
   family-header observations of the codomain come from the soundness of the recorded header
   conversion (`familyTele_data`, `paramBridge`).
3. **Soundness cases.** `projDF`: congruence plus `proj_obs_typed`. `projIota`: left to right by
   inversion of the spine's observations (only the `projCtor` clause produces `fieldOb`), right to
   left by `ctor_field_obs` (never-zero) or proof irrelevance (the guard's `fl ≈ 0`). `structEta`:
   typed observations at a projection family are field observations; left to right by inversion,
   right to left by `ctor_field_obs` on `mk ps (proj e)`. `unitLike`: no typed observations.
4. **Rules whose major family is projection-registered (D16).** Constructor spines of such
   families have no `ctorHead`/`ctorArg` observations (structure eta forbids them), so the rule
   clause gains a binding mode for them: a field variable at major position `q ≥ nparams` not
   occurring in the leading arguments is anchored in the class of `proj S (q - nparams) m`
   (`m` in the major key's class) with the observations `{k | fieldOb S (q - nparams) _ k ∈ Km}`,
   when the entry is never zero at the constructor's levels; the proof binding (any term of a
   propositional type, no observations) is allowed in every mode. The rule is identified by the
   family of the head type's major domain (a syntactic clause premise) instead of a `ctorHead`
   observation. Native rules: never-zero families use the projection binding, small elimination
   empties the right-hand side, singleton elimination uses the proof binding (`ProofBinder`).
   Generic case equations: never-zero or small (case permission).
5. **History induction** (`WF'.ruleValid` extended to projections), `ProjFree` dropped,
   `VEnv.WF.headInjectivity` and `VEnv.WF.headInversion` proved.
