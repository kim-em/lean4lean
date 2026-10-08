# Removing canonical choice: plan (2026-10-08)

Branch `agent/verify-inductives-strengthening` (worktree `lean4lean-strength`), off
`agent/verify-inductives` at 3157713b. Goal: `addDecl.WF_of_canonicalEq (wf) (heq) (decl) (hdecl)`
without `hch : ∀ safety, (ves.venv safety).HasCanonicalChoice`.

## 1. Where `hch` is used, exactly

One place: the projection-walk corner. `inferProj` (Lean4Lean/TypeChecker.lean) walks the
instantiated constructor telescope of a structure; at a field binder whose body has no loose bound
variable (a *non-dependent* field) it continues with the body without substituting anything
(`instantiateProjectionFields`). The verification (`instantiateProjectionFields.WF_all`,
Verify/TypeChecker/Projection.lean) carries `c.TrExprS type R` along the walk; at a non-dependent
field whose projection is untypable (a data field of a `Prop` structure) it needs the body's
translation *without* the binder: `TrExprS (D :: Δ) body body'` with `body` closed must give
`TrExprS Δ body b₀`, `body' = b₀.lift`. Today this is `projectionWalkCorner_choice`
(Verify/Typing/ProjectionCorner.lean): inhabit `D` with `Classical.choice` and substitute.

Two facts about the data flow, both read off the code:

* The walked `type` Exprs are, literally, the stored constructor type `C` of the structure with its
  universe parameters instantiated, its parameter binders instantiated by the major's arguments, and
  its *dependent* field binders instantiated by `.proj S k struct`. Constructor types are syntactic
  `forallE` spines (`checkConstructors.loopCtor` matches `.forallE` without `whnf`), and `whnf` of a
  `forallE` returns it unchanged.
* The verification's `TrExprS Δ type R` at every walk step is obtained *only* by transporting the
  environment's `TrExprS [] C T₀` (constructor constant, `CheckingEnv`) along level instantiation,
  weakening into `Δ`, and substitution of typed terms (parameters, typable projections).

So the corner is a strengthening statement about the constructor's own telescope, transported. It
does not need strengthening of an arbitrary derivation in `Δ`.

## 2. Architecture: a frame lemma for the executable, not declarative strengthening

The constructor type `C` was checked when the inductive was added: every installation path runs the
core checker on it in the *empty* local context with a fresh state (`AddInductive.checkClosedType`
= `withCheckLCtx {} (checkType C)` on the ordinary path; `TypeChecker.M.run … (lctx := {})
(checkType ctor.type)` in `validateRestoredConstructorParameters.run` on the nested path).
`inferForall.loop` opens one free variable per binder (`withLocalDecl`) and checks each later
domain, and finally the result, in the local context containing all earlier binders.

**Observation.** The core checker consults the local context only by `find?` at free variables
that occur in its inputs (or in the declarations of such variables), by `mkForall`/`mkLambda` over
the binders it opened itself, and inside error values. A free variable `g` of a non-dependent
binder never occurs in any later domain, in the result, or in any cache entry (the state is fresh
at the check, and the caches are scope-local since E1). Hence every sub-run after `g` is opened is,
*as a run of the executable*, the same run as in the local context without `g`'s declaration.
The *existing* verification, applied to that ghost-free run in the context without `g` (a
legitimate `VContext`), yields the translations of the later domains and of the result in the
smaller context. Assembling them gives the translation of the telescope with `g`'s binder deleted.
This is exactly the comment already in `Inductive/Add.lean` (`Context.checkLCtx`): "a checker run
only consults free variables reachable from its inputs", now proved.

No declarative strengthening, no confluence, no termination measure is involved: the strengthened
judgement is *re-derived* by the verified checker's own soundness proof in the smaller context.
Canonical `Eq` is not needed either.

### 2.1 Components

**(F) Frame lemma for the core checker** (new file `Verify/TypeChecker/Frame.lean`; pure statement
about the executable, independent of the typing verification).

* `GF G e` (ghost-free): `FVarsIn (fun fv => ¬ G fv) e` (reuses every existing `FVarsIn`
  preservation lemma), lifted to `Option Expr`, arrays, pairs, `Level` (trivial), results of each
  function.
* `GFState G s`: every *value* of `inferTypeI`, `inferTypeC`, `whnfCoreCache`, `whnfCache`,
  `unfold` is ghost-free. (`eqvManager` and `failure` only answer booleans; no condition.)
* `GhostRel G ctx₁ ctx₂`: the two `TypeChecker.Context`s agree on every field except `lctx`;
  `ctx₁.lctx.find? fv = ctx₂.lctx.find? fv` for every `fv` with `¬ G fv`; every declaration of
  `ctx₂.lctx` at a non-ghost has ghost-free type and value.
* `Reserved G s`: every ghost is reserved by `s.ngen` (so freshly generated ids are never ghosts).
* Statement, for every executable function `f` of `TypeChecker.lean` (`Inner` namespace), of
  `Quot.lean`, `Inductive/Reduce.lean` (and the pure `EquivManager`, `Level`, `Instantiate`):
  `GhostRel G ctx₁ ctx₂ → GF inputs → GFState G s → Reserved G s →
   f … ctx₁ s = .ok (a, s') → f … ctx₂ s = .ok (a, s') ∧ GF a ∧ GFState G s'`,
  with `RecM` functions quantified over methods `m` that satisfy the same property; the fuel
  fixpoint `Methods.withFuel` satisfies it by induction on fuel.
* Failure values are irrelevant (they mention `getLCtx` only on the error path, and the checker
  never catches exceptions: `grep catch` finds nothing).

**(G) Ghost verification of the telescope check** (new file
`Verify/TypeChecker/GhostTelescope.lean`). From a successful core run of `checkType C` in the empty
context with fresh state, conclude `TelTr venv Us [] C T₀` (below), by an induction that mirrors
`inferForall.loop.WF` with an extra ghost set: a kept binder extends the `MLCtx` as now; a
non-dependent binder may be *ghosted* (its fvar goes into the actual `lctx` and the loop's fvar
array but not into the `MLCtx`); every domain/result sub-run in the ghosted actual context is
transferred by (F) to the ghost-free context and verified there by the existing
`inferType.WF'`/`ensureSortCore.WF`.

**(T) Telescope-closed translation** (new file `Verify/Typing/TelescopeTranslation.lean`):

```lean
inductive TelTr (env : VEnv) (Us : List Name) : VLCtx → Expr → VExpr → Prop
  | mk : TrExprS env Us Δ e e' →
    (∀ {n d b bi d' b'}, e = .forallE n d b bi → e' = .forallE d' b' →
      TelTr env Us ((none, .vlam d') :: Δ) b b') →                      -- keep the binder
    (∀ {n d b bi d' b' b₀}, e = .forallE n d b bi → e' = .forallE d' b' →
      b = b₀.liftLooseBVars' 0 1 →                                       -- binder unused
      ∃ b₀', b' = b₀'.lift ∧ TelTr env Us Δ b₀ b₀') →                    -- delete the binder
    TelTr env Us Δ e e'
```

(possibly with an `mdata` clause if any installation path admits `mdata` in a spine). Transport
lemmas: `TelTr.mono` (environment extension), `TelTr.instL_lequiv` (universe instantiation,
mirroring `TrExprS.instL_lequiv`), `TelTr.weakFV`/`weakBV` (into `Δ`), `TelTr.instN` (substitution
of a typed term for a kept binder; deletion commutes with substitution at other binders),
`TelTr.toTrExprS`.

**(C) The walk carries `TelTr`.** `instantiateProjectionParameters.WF_all` and
`instantiateProjectionFields.WF_all` take and maintain `TelTr Δ type R` instead of
`TrExprS Δ type R`. At a non-dependent field the delete branch of `TelTr` *is* the corner (no case
split on the projection's typability any more); at a dependent field `TelTr.instN` with the typed
projection, as now. `whnf` on the syntactic spine returns its input (`Methods.WF` gets a field
`whnf_forallE_self` if needed, discharged at the fuel fixpoint by the first match arm of `whnf'`).

**(I) Environment invariant.** A new field of `VEnvs.WF` (and of `CheckingEnv.Valid`/`VContext`,
replacing `canonicalChoice`): every visible constructor constant's source type `C` and translated
type `T₀` satisfy `TelTr venv ci.levelParams [] C T₀`. Monotone under every non-inductive
declaration (`TelTr.mono`); for an inductive declaration, each new constructor's `TelTr` comes from
(G) applied to its `checkType` run (ordinary and nested paths; primitive/bootstrap constructors
either go through the same run or are checked directly). This is a checker invariant like the
existing `inductiveProvenance`/`constructorSemantics` fields: proved preserved by `addDecl`, not a
hypothesis about the input; it is not a conjecture hidden in a field.

**(R) Removal.** Delete `hch` from `addDecl.WF`, `addDecl.WF_of_canonicalEq` and all callers;
`VContext.canonicalChoice` and `CheckingEnv.ValidCore.canonicalChoice` go; the choice-based corner
files stay as standalone theory (or are deleted if unused) and `Tests/CanonicalChoice.lean` stays.

## 3. Why the previously failing pieces do not arise

The four obstacles of the declarative attempts (STRENGTHENING_NOTES.md Part 3, Astra reviews 2-3,
CORNER_ASTRA_REVIEW.md) were all about transforming an *arbitrary* derivation under the binder:

* *own-mode lam/forallE domain premises*, *eta-domain choice*, *proof-irrelevance leaves with
  independently synthesized types*: these are conversion steps inside a derivation in the larger
  context that would need re-deriving in the smaller one. Here nothing is transformed: the
  smaller-context derivations are produced afresh by the verified checker from runs that never
  mention the removed variable. Whatever conversions the checker performs (its `isDefEq` calls,
  eta, proof irrelevance, unit-like, lazy delta) are performed identically in the smaller context,
  and their soundness there is the existing verification.
* *delta/quotDelta K and singleton alignment checks*: same; the checker's reductions are run, not
  replayed through a derivation.

What makes this possible is provenance (Astra's point 1 of CORNER_ASTRA_REVIEW.md: "translations
produced by this particular telescope walk admit certificates whose dependencies are controlled"):
the only translation the corner ever strengthens is a transport of a constructor type that the
checker itself accepted, and the acceptance run is the controlled certificate.

The general declarative statement (`Γ, A ⊢ e : B` with `e`, `B` free of the variable implies
`Γ ⊢ e : B`) remains open; nothing here proves or needs it. This route does not prove the corner
for an arbitrary well-formed `VEnv` (an environment not built by the checker carries no `TelTr`
invariant); `addDecl.WF_of_canonicalEq` quantifies over `ves.WF env`, whose new field every
checker-built environment satisfies by the preservation proof.

## 4. Risks

* (F) must cover every `lctx` read. Inventory (TypeChecker.lean): `inferFVar` (`find?` at an input
  fvar), `whnfFVar`/`isLetFVar` (`find?` at an input fvar, returns the let value), `mkForall`/
  `mkLambda` over the function's own fresh binders (`mkBindingList_congr` exists), `withLocalDecl`/
  `withLetDecl` (insert on both sides; the new id is not a ghost by `Reserved`), `getLCtx` in
  `throw` only. `Quot.lean`/`Inductive/Reduce.lean` receive `whnf`/`inferType`/`isDefEq` as
  arguments.
* (G) needs, at a ghost binder, `VState.WF` of the state in the ghost-free context; it is the state
  of the context before the binder with the name generator advanced (the existing `withLocalDecl`
  verification has the needed lemma), and `GFState` holds because all cached Exprs are reserved by
  the name generator before the fresh id.
* (I) touches every inductive installation path; the survey of paths is the first subtask.

## 5. Work split

1. (T) definition and transport lemmas; (C) walk refactor against a `TelTr` source hypothesis.
2. (F) frame lemma.
3. (G) ghost telescope verification (against the statement of (F)).
4. (I) invariant plumbing and (R) removal; survey of constructor installation paths first.
