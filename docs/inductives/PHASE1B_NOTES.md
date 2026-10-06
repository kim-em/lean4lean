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

## 7. Status

(updated as the work proceeds)
