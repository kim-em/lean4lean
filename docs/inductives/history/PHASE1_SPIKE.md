# Phase 1 spike: can the shape logical relation deliver `VEnv.WF.headInversion`?

Branch `agent/verify-inductives-headinv`. Context: `docs/inductives/BASE_OBLIGATIONS_DESIGN.md`
(sections 2, 4 Phase 1, 5), `Lean4Lean/Theory/Typing/HeadInversion.lean`, and Carneiro's
prototype `Lean4Lean/Experimental/{SExpr,ShapeLogRel,ShapeLogRelAdequacy,UniqueTyping}.lean`.
The prototype files are not modified.

Claims are tagged:
**[Lean]** proved in a file of this directory, no `sorry`, axioms `propext` and `Quot.sound`
only; **[paper]** argued here in full; **[belief]** a non-derivability claim about
`IsDefEq` that would need a confluence argument (unavailable, design section 1) and is
supported only by Lean's own checker (`KObstructionExamples.lean`).

## 0. Verdict

1. **The Phase 1 plan as designed does not work, with or without `HasCanonicalEq`.** The
   plan glues typed checks into the weak-head reduction of the logical relation (K-like
   `Eq.rec` fires iff the indices are declaratively equal; singleton iota fires after a
   declarative index check and builds proof fields from `Eq` extraction). Two facts kill it:
   * **Read-through is forced** [Lean: `HeadModel.readThrough`]. Any sound model that is
     compositional in application, and in which proofs are uninformative, interprets an
     eliminator on a proof major as its iota result whenever the model cannot tell the
     index from the aligned one. No continuous model can tell them apart in general:
     distinct variables under the bottom valuation, `fun n => n` against its recursive
     eta-expansion (closed, extensionally equal), or two self-looping definitions (both
     bottom).
   * **Pi-adequacy then forces the check** [Lean: `check_of_piAdequacy`]. If the logical
     relation sends a Pi-shaped type to a weak-head reduct that is a Pi with a typable
     domain (what Carneiro's `LRS.TyDefEq` at a `forallE` shape says, and what
     `forallE_forallE` needs), and the only reduction step out of the stuck eliminator
     requires the declarative index check, then the check is derivable. For `Eq.rec` this
     is equality reflection for a hypothesis `h : a = b` [belief: false].
   `HasCanonicalEq` does not help: canonical `Eq` is itself the paradigm instance. The
   obstruction is present in every environment with `Eq`, and in `Eq`-free environments
   with the countermodel's family `I`.
2. **The glued-check plan has a second, independent defect**: even when the check holds,
   the reduct is typed at a different instance of the motive, and the relation needs the
   two instances related. That needs "declaratively equal indices are related by the
   logical relation" (*reflection*), for check derivations that are not subderivations of
   the derivation being interpreted. The fundamental lemma is an induction on derivations,
   so this is circular; the obvious stratifications fail (section 3.3).
3. **The separation half of `HeadInversion` needs no logical relation at all**
   [Lean: `HeadModel.separation`]. `sort_sort`, `sort_forallE`, `sort_rigid`,
   `forallE_rigid` and the head/level part of `rigid_rigid` (`c = c'`, `ls ≈ ls'`) follow
   from any sound, head-classifying model. A shape model with read-through Prop
   eliminators is a plausible instance in every WF environment (no `Eq` hypothesis).
4. **The injectivity half** (`forallE_forallE`, the arguments of `rigid_rigid`,
   `former_args`, `proj_fieldType`) needs adequacy. The only repair of the obstruction I
   found is to replace checked steps by an **observational, cast-pushing evaluation**
   (in the style of Observational Type Theory) as the reduction under the logical
   relation: unsound for `IsDefEq` (which the relation does not need, section 1.4), typed,
   deterministic, and congruence-compatible. It avoids reflection because casts compute on
   the canonical forms of *both* endpoint types separately. It needs no `Eq`: the
   transports it builds come from the eliminator's own recursor [Lean: `orig`,
   `origProof`, `toOrigin`, `fromOrigin` in `KObstructionExamples.lean`]. This is new
   research with no prototype and no precedent for proof-irrelevant K plus impredicative
   `Prop`.
5. **Go/no-go**: no-go for Phase 1 as designed. If the semantic route is kept, split it:
   Phase 1a (sound shape model, separation half, low-to-medium risk, 6k-9k lines) and
   Phase 1b (cast-pushing logical relation, injectivity half, high risk, 11k-19k lines,
   with `proj_fieldType` carrying an extra open sub-obligation, section 6).

## 1. The prototype

### 1.1 What the shapes are

`Shape n` (ShapeLogRel.lean:45) is a finite approximation of depth `n`: `bot`, `sort rel`
(`rel` is only "not identically level zero"), `forallE dom table`, `lam table`,
`ctor name args`, `indTy`. Tables are finite lists of argument/result pairs; well-formed
tables (`ShapeFun.WF`) are closed under joins of compatible keys and monotone. `WShape` adds
well-formedness, `TShape` hides the depth. Shapes form a Scott-domain-like order with
compatibility and joins (`WShape.join_prop`, 1557). `HasType` (2486) types shapes:
Prop-typed shapes have only `bot` elements (`WShape.HasType.proofIrrel`, 3211), and
`indTy : sort r` only for `r = true`, so **inductive propositions get the `bot` shape**.

Two consequences matter below. Every inductive type collapses to the one shape `indTy`,
so the prototype cannot separate distinct rigid heads (`rigid_rigid`'s `c = c'`) and its
relation at `indTy` is `True`. Sort shapes forget the level, so `sort_inv` gets `u = v`
from adequacy (the relation demands reduction to the *same* `sort u`), not from the model.

### 1.2 Interpretation, soundness, relation, adequacy

* `LE_Interp ρ m M` (3333): "`m` approximates `M` under valuation `ρ`", downward closed.
  Constants go through `LE_Interp.Const` (3323): `bot`, `lam` tables, `ctor`, `indTy`,
  and `pat` for a registered pattern, matched on the **shapes** of the arguments
  (`LE_Interp.Matches`, 3308). **Pattern checks (`Pattern.Check`) are ignored**: the
  semantics of a checked pattern is read-through by construction.
* Soundness `LE_Interp.sound` (5261): a derivation `Γ ⊢ M ≡ N : A` gives equal
  approximation sets and typed approximations under every valuation fitting `Γ`.
* `LogRel Γ n` (5271), built by recursion on the depth (`LR0`, `LRS`, `LR`, 5896). It is
  **non-Kripke** (arguments live in the same `Γ`). At `sort` shapes: both sides reduce to
  the same `sort u`. At a `forallE` type shape (`LRS.ValTyPi2`, 5388): both sides reduce
  to Pi types with declaratively equal domains and codomains and pointwise related
  instances. At function-element shapes: observational (`LRS.LamDefEq`). At `lam`, `ctor`,
  `indTy` *type* shapes and at `bot`: `True`.
* Adequacy `LR.adequacy` (ShapeLogRelAdequacy.lean:139): a derivation, an approximation of
  the left side and of the type give relatedness under every related substitution
  (`LR.SubstWF`, 6066). Corollaries `forallE_inv`, `sort_inv`, `sort_forallE_inv` (450-473)
  use `σ = id`, `ρ = Valuation.nil` and the fact that `sort`/`forallE` are weak-head
  normal.

### 1.3 Sorries and the axiom

Live counts differ from the design document's "9". `ShapeLogRel.lean`'s seven `sorry`
tokens are all inside the block comment at 1665-1722 (dead code). `ShapeLogRelAdequacy.lean`
has one: the **`const` case of `LR.adequacy` (154)**. `SExpr.lean` has 32 `sorry` tokens in
about 28 declarations and the axiom `Params.extra_pat` (614). On the adequacy path:

| Item | Content | Nature |
|---|---|---|
| `IsDefEq.strong`, `IsDefEqStrong.defeq` (679-680) | strong form with typing premises; the strong `const` rule needs `ctor_ty` (688) | routine but large; `ctor_ty` is a formation property |
| `IsDefEq.subst`, `Ctx.SubstEq.lift` (787, 798) | substitution | routine (VExpr analogues exist) |
| `IsDefEq.defeqDF_l'` (825) | context conversion | routine (`IsDefEq.defeqDFC` exists for VExpr) |
| `WHRed.determ`, `extra` cases (987-997) | determinism of pattern steps | essential, needs `pat_uniq`; port of `WHRed.determ` (HeadReduction.lean) |
| `LR.adequacy`, `const` (Adequacy:154) | realizability of pattern-interpreted constants | **essential; false for checked patterns** (section 3) |
| axiom `Params.extra_pat` | every stored rule is an instance of a registered pattern whose checks hold in every context | a registry property; the VExpr analogue is the pattern registry built by `NativeRegistryOfWF`/`CanonicalRegistryOfWF` |

The rest (`InferType*`, `ParRed`, `NormalEq`, `CRDefEq`, `HasTypeStratifiedS`,
`Ctx.Subst.*`, `WHRedS.defeq`) is off the adequacy path.

**The prototype does not build on this branch.** `SExpr.lean` has non-exhaustive matches
at lines 19, 153, 161 and 536 because `VExpr` gained `elim` and `proj` and `Pattern` gained
`elim` and `Check.nonzero`. So the CI step "Build Lean4Lean.Experimental" fails here.
The repair is three or four match arms; it was not made because the prototype is upstream
work. The spike files therefore import only the uniqueness-free base.

### 1.4 Reduction soundness is not used

The relation and adequacy use weak-head reduction only syntactically: determinism
(`WHRedS.determ`, `determ_l`), "sorts and Pi types are normal" (`WHNF.sort`,
`WHNF.forallE`), closure under application, and the beta step. `WHRedS.defeq` (sorried) is
never used by `LR` or `LR.adequacy`. All declarative content of the relation (Pi domains
equal, typing of domains) is carried by its own clauses and established from derivations.
So the reduction under the relation **may be unsound for `IsDefEq`**, provided it is
deterministic, leaves canonical heads alone, and produces typed reducts whose declarative
relations follow from those of the redex. Section 4 uses this freedom.

## 2. Extension design for (a)-(d)

The target calculus is `VEnv.IsDefEq` (Basic.lean): 19 rules, including `elimDF`,
`elimIota`, `projDF`, `projIota`, `structEta`, `unitLike`, levels with `≈`, and no
`trans'` (chains are `TypeChain`).

### 2.1 Domain changes (needed for any route)

* Sort shapes carry the level's evaluation (`sort (l : List Nat → Nat)`), so equal sorts
  give `≈` in the model (needed for `sort_sort` without adequacy).
* `indTy` becomes `rigid c lvls args`: the family or opaque-constant name, evaluated
  levels and argument shapes. Prop-valued type formers get rigid shapes too, typed at the
  Prop sort; their elements stay `bot`. Without this, `rigid_rigid` and `former_args` say
  nothing about `Eq a b ≡ Eq a' b'`.
* Function tables and the rest of the domain are reused.

### 2.2 (a) `extra` rules: definitions and iota as stored `VDefEq`s

Definitions are patterns with a fixed right-hand side; the prototype's `Const.pat` handles
them. Iota for **Type-valued** families has non-linear pattern positions (the indices of
the constructor's result type, repeated parameters), but the major is a constructor with a
visible shape, and typing makes the index positions agree. The relation must remember that
agreement, because a step that ignores the index positions produces a reduct typed at
`motive (ctorIndices) (ctor ..)` instead of `motive idx (ctor ..)`. The fix is standard:
the relation at a data shape of an indexed family records that the constructor's own
indices are related to the type's indices ("Forded" data relation, as for `Id` in
reducibility proofs). Then the reduction can match only the major and stay unchecked, and
the adequacy `const` case gets the index relatedness from the major. Abstract eliminators
(`elimDF`, `elimIota`) are the same with the schema's generic equations in place of
patterns. Cost: section 7.

### 2.3 (b) canonical `Eq` with K, (c) singleton large elimination

Both are eliminators on a **proof** major. Proof irrelevance forces every proof to the
`bot` shape, so the model cannot see the major and must decide from the indices alone.
This is where the plan breaks (section 3). Section 4 gives the only repair found.

### 2.4 (d) projections, structure eta, unit-like

* Model: `proj S i e` denotes the `i`-th argument shape of `e`'s constructor shape, `bot`
  otherwise. Structure constructors with all-`bot` arguments collapse to `bot` (the
  prototype already does this for `etaCtor`, `Shape.ctor'`, 817), which validates
  `structEta`; with zero fields every element is `bot`, which validates `unitLike`.
  `projIota` needs the `projDF` guard: a data projection out of a structure whose
  universe may be zero would read a field out of a `bot` (proof) shape, so the guard is
  what keeps the model sound, exactly as the design document says.
* Relation: observational at structure shapes (related iff all typable projections are
  related), as in reducibility proofs with eta for records; reduction to a constructor is
  not demanded (a variable of structure type may have a non-`bot` shape through its
  projections).
* `proj_fieldType` is discussed in section 6.

## 3. The obstruction

### 3.1 Read-through is forced

`HeadModel.readThrough` [Lean]. Let `F` be the eliminator spine up to its last index and
major, `hiota : Γ ⊢ F a r ≡ m` the iota instance at the aligned index `a` and canonical
major `r`. If the model gives `b` the denotation of `a` and the major `h` the denotation
of `r` (proof irrelevance forces the latter), then `F b h` denotes `m`. For the shape
semantics the hypotheses hold as follows [paper]: compositionality is
`LE_Interp.bot`/`LE_Interp.app`, which see an argument only through its approximation
set; under `Valuation.nil` every variable denotes `{bot}`; `Eq.refl a` is a proof and
denotes `{bot}`. Indices with equal denotations but no derivable conversion:

* two distinct variables `a b : α` under the bottom valuation (the corollaries use exactly
  this valuation);
* `fun n => n` and `fun n => Nat.rec 0 (fun _ ih => succ ih) n`: closed, equal as functions
  on all finite approximations, not convertible [belief; `KObstructionExamples.lean` shows
  Lean's checker rejects `f = g := rfl`]. This survives adding neutral atoms for variables;
* two definitions `T₁ := T₁`, `T₂ := T₂` (admitted by `VDecl.mutualDef`): both bottom in
  any semantics where divergence is bottom, which is the point of the shape approach.

The forcing does **not** say the model must read through when the indices have *different*
denotations. A sound and monotone choice is "read through up to the common information":
`x` approximates `F b h` iff some `s` approximates both `a` and `b`, `x` approximates `m`,
and `x` is typed at the motive at `s`. This avoids the ill-typed shapes that plain
read-through produces under a semantically false hypothesis such as `h : 0 = 1`, keeps
joins (join the witnesses `s`), and needs no meets [paper, not formalized].

### 3.2 Pi-adequacy forces the index check

`check_of_piAdequacy` [Lean]. Instance with `Eq` (`KObstructionExamples.lean`, section 1):

```
Γ := α : Type, a b : α, h : a = b, Q : α → Type, R : Q a → Type, y : Q b, y' : Q a
T := (@Eq.rec α a (fun x _ => Q x → Type) (fun z => R z → R z) b h) y   -- T : Type
```

By read-through `T` denotes the denotation of `(fun z => R z → R z) y'`, a Pi shape. A
Pi-adequacy theorem demands `T ⤳* ∀ (_ : B), C` with `B` typable. A checked K step needs
`Γ ⊢ a ≡ b`. So **any** Phase 1 that proves `forallE_forallE` through Carneiro-style
adequacy with checked steps proves `Γ ⊢ a ≡ b` from `h : a = b` [Lean, given the
interfaces]; with the `f`/`g` indices it proves `f ≡ g` [belief: both false]. An
unchecked step (`Eq.rec .. b h ⤳ m` always) gives the reduct `R y → R y`, whose domain is
ill-typed (`R : Q a → Type`, `y : Q b`) unless `Q a ≡ Q b` [belief: false]. The relation at
Pi type shapes needs that domain typable, so the unchecked step fails too.

`check_of_adequacy_at` [Lean] is the same skeleton for data and rigid shapes: whenever the
relation demands reduction to some canonical form and the stuck eliminator can only step
through the check.

The countermodel family `I` (STRENGTHENING.md) gives the same result in an `Eq`-free
environment: `I.rec (motive := fun _ _ _ _ => Type) K n x w p` with `n : C` a variable reads
through to `K x _` (opaque `C`, `F` make `n` and `c`, `w` and `leftMap x` indistinguishable),
while the checked singleton step needs `n ≡ c` and the unchecked one types `K x _` with
`x : F n` against `K : (v : F c) → ...`.

### 3.3 Reflection, and why the obvious repairs do not close

Even for redexes whose check *does* hold, a checked step `E := Eq.rec α a M m b h ⤳ m`
leaves `m : M a rfl` where the relation is indexed by `M b h`. Converting needs
`TyDefEq (M a rfl) (M b h)`, which needs `a` and `b` related by the relation, not merely
`Γ ⊢ a ≡ b`. Call "`Γ ⊢ a ≡ b`, both sides self-related, implies related" **reflection**.

* In a congruence derivation (`E_b ≡ E_a` from a subderivation `b ≡ a`) the induction
  hypothesis supplies the relatedness. In the reflexive case (adequacy of the *typing* of
  `E_b`) the check derivation is not a subderivation, so the induction on derivations has
  nothing to offer.
* Making stuck eliminators neutral (no K step) does not help: the congruence case then
  relates a neutral `E_b` to `E_a ⤳ m`, a canonical form, and transitivity through
  neutrals loses the component information `forallE_forallE` needs.
* Making the check "related by the relation" instead of declarative makes reduction and
  relation mutually recursive across unrelated shapes (index shape versus result shape).
  The relation's level recursion does not order them, and with a neutral disjunct the
  definition is not monotone in the reduction.
* Induction on shape depth (outer) and derivations (inner) fails because the
  application and lambda cases of `LR.adequacy` already use the hypothesis at *higher*
  depths (they lift to `max` depths).
* Induction on derivation size fails because substitution does not preserve size.
* Storing the index equation in the relation of the *major* (how reducibility proofs
  handle `J` and `K` on `rfl`) is impossible for a proof major: its shape is `bot`. Storing
  it in the relation at the proposition `Eq a b` makes every hypothesis `h : a = b` of the
  base context an obligation "`a` and `b` related"; with `a ≢ b` of equal non-`bot` shape
  (`f`, `g`, or `P₁ → Nat`, `P₂ → Nat`) that obligation is false. Restricting it to the
  case `Γ ⊢ a ≡ b` and proving validity of contexts by induction on their length reduces
  it to **strengthening** of `Γ, h ⊢ a ≡ b` to `Γ` [paper]: exactly the open problem
  `strengthening_of_canonicalEq`, and false in general without `Eq`.

So the glued-check design either proves equality reflection or needs strengthening inside
Phase 1. Both are worse than the obligation Phase 1 was meant to discharge.

## 4. The repair: observational cast-pushing evaluation

Section 1.4 allows the relation's reduction to be unsound. Treat every eliminator on a
proof major (`Eq.rec`, singleton recursors) at a motive `M` as a **cast** from
`M (ctor form)` to `M (actual index, major)` and evaluate casts by the canonical forms of
the two endpoint types, computed separately:

* both endpoints sorts with `≈` levels: the cast is the identity (the reduct is the minor,
  typed at a convertible sort);
* both Pi: `cast f ⤳ fun x => cast_cod (f (cast_dom⁻¹ x))`, the inverse cast built by the
  same eliminator (for `Eq`, along `Eq.symm h`; for a singleton family, along
  `fromOrigin`/`toOrigin`);
* both the same rigid family: data stays a canonical "cast of a constructor"; eliminators
  on such data commute with the cast (`rec .. (cast t) ⤳ cast (rec .. t)`);
* different heads, or a neutral endpoint: stuck. The model then has no common information
  above `bot` (section 3.1), so adequacy demands nothing.

For `T` above this gives `T ⤳* R (Eq.symm h ▸ y) → R (Eq.symm h ▸ y)` with a typable
domain (the term elaborates; `KObstructionExamples.lean` shows it is not convertible to
`T`, which is fine). Why reflection disappears: the cast step needs only the self-related
canonical forms of `M a rfl` and `M b h` (from the motive's induction hypothesis), and the
adequacy of a cast is proved by induction on the *type* shape (domains and codomains are
strictly smaller), as in normalization proofs for Observational Type Theory. The K rule of
`IsDefEq` (proof irrelevance plus iota, with a subderivation `a ≡ b`) then needs "a cast
along related types is related to the identity", again by induction on the type shape,
with the relatedness supplied by the subderivation.

No `Eq` is needed: `orig p` and `origProof p` (`KObstructionExamples.lean`, section 3) are
the data origin and a proof of the proof field at the origin, extracted by the family's own
recursor, and `toOrigin`/`fromOrigin` are typed transports in both directions for an
arbitrary family over the index telescope. The design document's claim that the semantics
needs canonical `Eq` to "see" the proof field conflated the origin with the index `v`;
identifying those is what the countermodel shows underivable, and the relation does not
need it.

Open obligations of this route, none attempted:

1. Determinism of the cast-pushing evaluation and that canonical heads do not step.
2. Typedness of every reduct (transports for every case, including the commuting
   conversions and dependent codomains via the eliminator's motive).
3. "Cast along related types is related to the identity" (the K rule's adequacy).
4. Adequacy of the `const`/eliminator case for Type-valued families with the Forded data
   relation (section 2.2), and of the schema-based `elimIota`.
5. Termination is not available (Abel and Coquand), so every lemma must be "adequate at
   non-`bot` shapes" rather than "normalizing".

There is no precedent combining casts computed this way with definitional proof
irrelevance, K-like reduction on neutral majors and impredicative `Prop`. Risk: high.

## 5. Separation from soundness alone

`HeadModel` [Lean] asks for a denotation `den U Γ e`, soundness for `IsDefEq` in
well-formed contexts, and head classes: sorts to `sort u.eval`, Pi to `pi`, sort-typed rigid
applications to `rigid c (ls.map (·.eval))`. `HeadModel.separation` derives `HeadSeparation`:

```lean
structure HeadSeparation (env : VEnv) : Prop where
  sort_sort : ∀ {U Γ u v}, OnCtx Γ (env.IsType U) →
    env.TypeChain U Γ (.sort u) (.sort v) → u ≈ v
  sort_forallE : ∀ {U Γ u A B}, OnCtx Γ (env.IsType U) →
    ¬env.TypeChain U Γ (.sort u) (.forallE A B)
  sort_rigid : ∀ {U Γ c u ls args}, OnCtx Γ (env.IsType U) → env.Rigid c →
    ¬env.TypeChain U Γ (.sort u) (.mkApps (.const c ls) args)
  forallE_rigid : ∀ {U Γ c A B ls args}, OnCtx Γ (env.IsType U) → env.Rigid c →
    ¬env.TypeChain U Γ (.forallE A B) (.mkApps (.const c ls) args)
  rigid_heads : ∀ {U Γ c c' ls ls' args args'}, OnCtx Γ (env.IsType U) →
    env.Rigid c → env.Rigid c' →
    env.TypeChain U Γ (.mkApps (.const c ls) args) (.mkApps (.const c' ls') args') →
    c = c' ∧ List.Forall₂ (· ≈ ·) ls ls'

theorem HeadModel.separation (M : HeadModel env) : HeadSeparation env
theorem HeadInversion.toHeadSeparation (h : env.HeadInversion) : HeadSeparation env
```

The read-through obstruction does not touch this half: a sound model may read through
freely. The intended instance is the prototype's domain with the changes of section 2.1,
read-through (up to common information) for Prop eliminators, and the model clauses of
section 2.4. It needs no `Eq`. What this half already buys downstream (design section 4,
step 3): `IsDefEqU.rigidApp_forallE_inv`, `rigidApp_ne`, `sort_rigidApp_inv`,
`sort_forallE_inv`, hence `VConstructorShape.saturated_of_hasType` and the FullReduction
`:693` `etaL` and `:863` cases, once uniqueness is available (they convert `IsDefEqU` to a
chain through `uniq`, which needs the injectivity half). So separation alone does not
unblock the cone.

## 6. `proj_fieldType`

Beyond needing adequacy, it has a sub-obligation the semantic route does not obviously
discharge. Take a structure whose result level may be zero and a data field `j` before
the selected field `i` (for example `S.{u} (α : Sort u) : Sort u := (x : α) (h : T α)`).
`proj S j e` is untypable under the `projDF` guard, yet `fieldType i` instantiates the
telescope binder of `j` with it. If `j` does not occur in `i`'s type the field types
compare by congruence only if the telescope body's derivation can be instantiated with
the unused slot left out: strengthening of the closed constructor telescope away from a
data binder (whose sort may be zero, so the binder may be a proof). The relation needs a
typed substitution for every slot (`LR.SubstWF` carries `Γ₀ ⊢ x ≡ x' : A`), so it inherits
the problem. If `j` does occur, the field type is untypable and the field is vacuous.

## 7. Per-rule cost

Measured on the prototype (lines of the `LE_Interp.strongSound` case / the `LR.adequacy`
case), then estimated for the new rules on `VExpr` (soundness / adequacy, including the
rule's share of new domain, interpretation and relation clauses).

| Rule | Prototype | New, model | New, relation (cast route) |
|---|---|---|---|
| `bvar` | 9 / 12 | 20 | 20 |
| `symm`, `trans` | 2 / 4 | 5 | 10 |
| heterogeneous `trans'` (here: chains) | 5 / 13 | 20 | 40 |
| `sortDF` (levels `≈`) | 6 / 13 | 100 | 100 |
| `constDF` (with `instL`, `≈`) | 7 / `sorry` | 300 | 1000-2000 |
| `appDF` | 10 / 87 | 15 | 100 |
| `lamDF` | 15 / 74 | 20 | 80 |
| `forallEDF` | 13 / 63 | 20 | 70 |
| `defeqDF` | 7 / 11 | 10 | 15 |
| `beta` | 29 / 5 | 30 | 10 |
| `eta` | 61 / 22 | 60 | 25 |
| `proofIrrel` | 8 / 7 | 10 | 10 |
| `extra` | 25 + axiom / 9 + axiom | 300 (registry instead of axiom) | 100 |
| `elimDF`, `elimIota` | absent | 1000-2000 (schemas) | 1500-3000 |
| Prop eliminators (Eq, K, singleton) | absent | 300-600 (read-through) | 3000-6000 (cast calculus) |
| `projDF`, `projIota` | absent | 300-500 | 500-1000 |
| `structEta`, `unitLike` | absent | 150-300 | 300-600 |

Shared infrastructure, measured: domain 3.3k lines (ShapeLogRel 1-3280), interpretation
1.0k (3282-4322), soundness helpers and `StrongSound` 0.9k (4323-5262), relation 0.8k
(5265-6100), adequacy 0.5k, syntax 1.3k with about 8 essential `sorry`s.

| Part | Lines | Risk |
|---|---|---|
| Repair and port to `VExpr` (or repair `SExpr` and translate) | 1.5k-3k | low |
| 1a. Model: domain changes, interpretation, soundness for 19 rules, `HeadModel` instance | 6k-9k | medium (read-through up to common information; schema eliminators) |
| 1b. Cast-pushing evaluation, relation with Forded data and casts, adequacy, corollaries | 11k-19k | high (no precedent; section 4) |
| `proj_fieldType` unused-slot obligation | unknown | open (section 6) |
| **Phase 1 total** | **19k-31k** | 1a medium, 1b high |

## 8. Answers to the spike questions

* **For all WF environments or only under `HasCanonicalEq`?** The design's version: under
  neither, because canonical `Eq` instantiates the obstruction. The cast-pushing version,
  if it works, would work for all WF environments: its transports come from each
  eliminator's own recursor, not from `Eq`. The separation half works for all WF
  environments.
* **Fields at risk.** `forallE_forallE`, the argument part of `rigid_rigid`, `former_args`
  (all need adequacy through the obstruction) and `proj_fieldType` (adequacy plus section
  6). Safe given a model: `sort_sort`, `sort_forallE`, `sort_rigid`, `forallE_rigid`,
  `rigid_rigid`'s `c = c'` and `ls ≈ ls'`.
* **Does the semantics need to carry syntax?** Not for soundness (read-through is sound).
  For adequacy, carrying syntax in the *checks* is what fails; the repair keeps the model
  syntax-free and moves all the work into the relation's evaluation.

## 9. Files

* `HeadModel.lean`: `HeadClass`, `HeadModel`, `HeadSeparation`, `HeadModel.den_chain`,
  `HeadModel.separation`, `HeadInversion.toHeadSeparation`. No `sorry`.
* `ReadThrough.lean`: `HeadModel.Compositional`, `HeadModel.readThrough`, `PiAdequacy`,
  `check_of_piAdequacy`, `check_of_adequacy_at`. No `sorry`.
* `KObstructionExamples.lean`: plain Lean, no lean4lean imports. The stuck terms
  `T`, `Tfg`, `SI`; the iota and K-like computations by `rfl`; `fail_if_success` records of
  non-convertibility; `orig`, `origProof`, `toOrigin`, `fromOrigin`. No `sorry`.

There are **no spike `sorry`s**: the shape-of-proof role was taken by interfaces
(`HeadModel`, `PiAdequacy`) whose fields are the obligations:

| Interface field | Obligation |
|---|---|
| `HeadModel.sound` | soundness of a head-classifying model for all 19 `IsDefEq` rules (Phase 1a) |
| `HeadModel.head_sort`, `head_forallE`, `head_rigid` | the model's head classes (section 2.1) |
| `HeadModel.Compositional.app` | compositionality in application (true of `LE_Interp`) |
| `PiAdequacy.adequate` | what the relation must provide at Pi type shapes (Phase 1b) |
