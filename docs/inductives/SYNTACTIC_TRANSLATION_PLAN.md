# Separating syntactic translation from typed admissibility

This is the migration plan for replacing the typed translation relation `TrExprS`
(`Lean4Lean/Verify/Typing/Expr.lean`) by a syntactic translation plus a typed layer, following
BIG IDEA 2 of the checker review. Step 0 (the prototype) was done on
`agent/verify-inductives-syntr`; steps 1 to 4 (the foundation) are done on
`agent/verify-inductives-trsyn`, steps 5 and 6 on `agent/verify-inductives-trsyn2` (section 3
records what each did and where it departed from the plan); step 7 is not recommended and not
done. Sections 1 and 2 describe the prototype as it was written
(base `b8fb81be`); current numbers are in section 3.

## 1. What the prototype establishes

New files, none used by the verification at the time (no audit roots change). After steps 1 to
4 the layout is: `Syntactic/Context.lean` (847 lines) and `Syntactic/Levels.lean` (262) below
`Basic.lean` (353), `Transport.lean` (506), `Typed.lean` (434) and `TypedAPI.lean` (238), all
below `Typing/Lemmas.lean`, which imports them; `Strengthening.lean` and `Consumers.lean` are
still demonstrations above the verification. At the prototype:

| file | lines | content |
|---|---|---|
| `Verify/Typing/Syntactic/Basic.lean` | 353 | `TrSyn`, `trSyn?`, graph, uniqueness, erasure, scoping, totality |
| `Verify/Typing/Syntactic/Transport.lean` | 586 | weakening, substitution, abstraction, level instantiation, `eqv`, transport, raw shapes, restriction |
| `Verify/Typing/Syntactic/Typed.lean` | 193 | `TrResidual`, `TrTyped`, `TrExprS.iff_typed`, transport of the typed layer |
| `Verify/Typing/Syntactic/Strengthening.lean` | 99 | the strengthening boundary, `TelWF`, `TelTrN.iff_syn_telWF` |
| `Verify/Typing/Syntactic/Consumers.lean` | 205 | quotient initialization, projection telescopes, iota rules |
| `Tests/SyntacticTranslation.lean` | 46 | `#guard`s on `trSyn?` |

### 1.1 The syntactic translation

`TrSyn Us Δ e e'` is `TrExprS` with every typing premise removed and **without the
environment**. It is the graph of a total-on-scoped-input function:

- `TrSyn.iff_eval : TrSyn Us Δ e e' ↔ trSyn? Us Δ e = some e'`, so `TrSyn.unique` is
  `Option.some.inj` and translations of concrete terms are computed by `rfl`
  (the four quotient types, `Consumers.lean`);
- `TrSyn.exists_iff : (∃ e', TrSyn Us Δ e e') ↔ Closed e Δ.bvars ∧ FVarsIn (· ∈ Δ.fvars) e ∧ e.levelParamsIn Us`;
- `TrExprS.toTrSyn` (erasure).

Decision: no environment parameter. The task anticipated constant lookups for universe arity,
projection owners and literal encodings; none is needed. Constant presence and arity follow
from the typing of the result (`VExpr.WF.const_inv`); a projection is translated to the
primitive `.proj s i e'` without resolving `s`; literals are encoded by `Literal.toConstructor`
/ `VExpr.trLiteral`, which do not depend on the environment. A consequence is that `TrSyn` is
trivially monotone in the environment and is the same relation as `TrExprSyn`
(`Inductive/Rules/Translation.lean`), which already had no environment.

Proved without `HasType`, without an environment, and without a well-formed context
(`Transport.lean`): `weakFV'`, `weakFV` (the context needs only distinct free variables,
`Δ'.fvars.Nodup`, in place of `Δ'.WF`), `weakBV`, `instN`, `instN_let`, `inst`, `inst_let`,
`inst_fvar`, `abstract`, `uninstantiateN`, `uninstantiate`, `instL_same`, `instL_lequiv`
(existence and level equivalence in one statement, with no typing), `instL_lequiv_of`,
`prependLevelParam`, `eqv`, `transport`, `rawShape`, `closed`, `fvarsIn`, `levelParamsIn`,
and the restriction lemmas below.

### 1.2 Which typing conditions `TrExprS` genuinely needs

`TrExprS` has typing premises at `app` (two), `lam` (one), `forallE` (two), `letE` (one),
`proj` (one), `const` (presence and arity) and `lit` (`ContainsLits`). Over an ordered
environment and a well-formed context, all but two are consequences of the typing of the
result, by inversion:

| premise | recovered from `VExpr.WF Δ.toCtx e'` by |
|---|---|
| `app`: `f' : ∀ A, B`, `a' : A` | `VExpr.WF.app_inv` |
| `lam`: `IsType ty'` | `VExpr.WF.lam_inv` |
| `forallE`: `IsType ty'`, `IsType body'` | `HasType.forallE_inv` |
| `proj`: `WF (.proj s i e')` | it is the result; the major's typing from `HasType.proj_inv` |
| `const`: presence, arity | `VExpr.WF.const_inv` |

The two that are not are about syntax the translation erases:

- `letE`: the value is inlined, so `HasType val' ty'` is invisible in the result when the
  variable is unused (`let x : Nat := Sort 0; Nat.zero` translates to `Nat.zero`; see the test);
- `lit`: `VEnv.ContainsLits` is about the literal's type, and the encoding need not mention
  it (`""` mentions neither `Char.ofNat` nor `Nat`).

`TrResidual env Us Δ e` collects exactly these, recursively, and

```
theorem TrExprS.iff_typed (henv : env.Ordered) (hΔ : Δ.WF env Us.length) :
    TrExprS env Us Δ e e' ↔ TrTyped env Us Δ e e'
def TrTyped env Us Δ e e' :=
  TrSyn Us Δ e e' ∧ VExpr.WF env Us.length Δ.toCtx e' ∧ TrResidual env Us Δ e
```

On let-free, literal-free syntax (`Expr.letLitFree e = true`, decidable by `rfl` on concrete
terms) the residual is vacuous (`TrResidual.of_simple`) and
`TrExprS ↔ TrSyn ∧ VExpr.WF` (`TrExprS.iff_syn_wf`). So the typing a translation genuinely
carries is **one** judgment about its result plus the dead-let and literal obligations.

### 1.3 The strengthening boundary

- Syntax restricts for free: `TrSyn.lowerBV` (a source not using inserted bound variables
  translates without them, and the larger translation is the lift) and `TrSyn.restrictFV`
  (free variables: totality, weakening and uniqueness).
- Typing does not (`DESIGN.md` section 5.1). What remains is stated as an equivalence:
  `TrExprS.lowerBV_iff`/`TrExprS.restrictFV_iff`: the lowered typed translation exists exactly
  when the lowered *result* is well typed in the smaller context and the residual holds there.

The boundary is therefore a single judgment, `VExpr.WF env U Δ.toCtx e₀'`, plus the let
residual. Nothing about translation is on the wrong side of it any more.

### 1.4 The three consumers

1. Quotient initialization (`QuotInit.lean`). `plainTr` (7 lines) is a fragment of `trSyn?`
   (`plainTr_trSyn`), `TrExprS.ofPlainTr` (40 lines of inversion) is an instance of the general
   `TrSyn.toTrExprS` (`TrExprS.ofPlainTr'`), and `trSyn? [`u] [] tQuotC = some quotConst.type`
   holds by `rfl` (and the three siblings). `trConstant_quot_syn` is `trConstant_quot` with
   `trSyn?` and `letLitFree` in place of `plainTr`. Remaining typed content: `ci'.WF venv`,
   unchanged.
2. Projection inference (`TypeChecker/Projection.lean`, `Typing/TelescopeTranslation*.lean`).
   `TelTrN` records at each binder a `TrExprS` of the telescope, the existence of the lowered
   translation (`∀ b₀, b = b₀↑ → ∃ b₀', b' = b₀'↑`), and the delete branch. Restated:
   `TelTrN.iff_syn_telWF : TelTrN n Δ e e' ↔ TrSyn Δ e e' ∧ TelWF n Δ e e'`, where `TelWF`
   records only `VExpr.WF` of each (residual) telescope in its context and the residual of the
   source. The existence premise becomes `TrSyn.lower`, and `CtorTelescopeAt.iff_trSyn` shows
   the certificate's translation is the computed `trSyn? ci.levelParams [] ci.type`.
   `TelWF.delete_closed` is the walk's delete step: the lowered term and its relation to the
   body are syntactic, the certificate's content is `TelWF n Δ b b₀'`.
   **What remains genuinely typed** (as the review predicted, `TelTrN` does not disappear): at
   a deleted data field of a structure that may be a proposition, `VExpr.WF Δ.toCtx b₀'` for
   the residual type in the context *without* the field. The ghost-telescope/locality route
   (`GhostTelescope.lean`, `Frame*.lean`) remains the only source of it; it can now produce
   `TelWF` (an `IsType` per deleted residual) instead of `TelTr`, and its syntactic half
   (`GhostTelescope.lean` lines 149-150: `weakBV` + `uniqueCtx` to match lifts) is `TrSyn.lower`.
3. Iota rules (`Inductive/Rules/Translation.lean`). (Step 2 has since replaced `TrExprSyn` by
   `TrSyn`.) `TrExprSyn` *is* `TrSyn`
   (`TrExprSyn.iff_trSyn`); `TrExprS.of_syn` is `TrSyn.unique` (`TrExprS.of_syn'`); each of
   `TrExprSyn.uniqueCtx`, `transport`, `weakBV`, `instL` is the `TrSyn` lemma (`weakBV'`
   shown). `RecursorCheck.ruleRhsTranslation_of_wf` derives the typed translation of a rule's
   right-hand side from `ruleRhsSyn` and `VExpr.WF` of the generator's equation, instead of from
   "some typed translation of the same source" (`ruleRhsTranslation`), which
   `ruleRhsTyped`/`ruleRhsTypedOfResidual` (about 200 lines, `Translation.lean` 982-1185 and
   1455-1487) build. That replacement is only a win where the equation's typing is available
   independently of the rule's; at present `EquationWF.lean` derives it *from* the rule
   translations, so the existing order stays and the gain in this consumer is the deletion of
   `TrExprSyn` and its lemmas (lines 29-216, about 190 lines, 97 references).

## 2. Size of the migration target

| quantity | count |
|---|---|
| `TrExprS` occurrences outside the prototype | 3,116 in 170 files |
| of which `Verify/Inductive` | 2,010 in 127 files |
| `Verify/Environment` (mostly primitives) | 533 in 12 files |
| `Verify/TypeChecker` | 291 in 11 files |
| `Verify/Typing` | 210 in 10 files |
| `TrExpr` (up to defeq) occurrences | 311 |
| theorems named `TrExprS.*`/`TrExpr.*` | 239 (75 in `Typing/Lemmas.lean`) |
| `induction` over a `TrExprS` derivation (11-arm proofs) | 71 in 18 files |
| inversion patterns `let .app ... := H` etc. | 172 |
| `TrExprS.IsUnique` references (+ `noProj`, its primitive form) | 100 (+84) |
| `TrExprS.unique`/`unique'` references | 77/11 |
| `TrExprSyn` references | 97 |
| `TelTrN`/`TelTr` references outside their files | 60/29 |
| `CtorTelescope*` references | 211 |
| `.weakFV` calls | 123 |

Largest files by `TrExprS` occurrences: `Environment/Primitive/Condition.lean` 273,
`Inductive/Context.lean` 141, `Typing/Lemmas.lean` 123,
`Inductive/Recursor/Context/ForallTelescope.lean` 87, `Inductive/Constructor/Positivity.lean`
77, `Environment/Primitive/Recursion.lean` 77, `Inductive/Header/Telescope.lean` 75,
`Inductive/Nested/Lowering/Expansion/Contexts.lean` 72, `TypeChecker/Basic.lean` 69.

`Typing/Lemmas.lean` (2,481 lines), by region: weakening 70 lines, scoping 56, `wf` 23,
`uniq`/`defeqDFC` 121, `TrExpr` constructors 66, substitution 179, `prependLevelParam` 40,
`instL` 115, `abstract` 36, `IsUnique`/`unique` 86, literals 178, uninstantiation 43, `eqv` 29,
`AppStack` 61; the rest (about 1,350) is `Closed`/`FVarsIn`/`VLCtx` infrastructure and
beta-reduction, already syntactic.

## 3. Steps

Every step keeps the statements of existing theorems unless it says otherwise, so each is
mergeable on its own. Steps 1-3 edit `Typing/Lemmas.lean` and must wait for the three
concurrent refactors (`-models`, `-descriptor`, `-restoration`) to land.

**Step 1. Syntactic base below `Lemmas.lean`. Done** (commit `refactor: move the syntactic
translation infrastructure below Typing/Lemmas`). `Typing/Lemmas.lean` lost 932 lines to
`Syntactic/Context.lean` (`Closed`/`FVarsIn`, `VLocalDecl` helpers, the `VLCtx` relations with
their `find?`/`wf` lemmas, `TrExprS.IsUniqueCtx` with `find?_uniq`/`find?_exists`,
`ofLevel_hasMVar`, `BVLift.find?_lift_inv` from `TelescopeTranslationLemmas.lean`) and
`Syntactic/Levels.lean` (`ofLevel_mkLevelMax'`/`IMax'`, `substParams_wf`, and from other files
`VLevel.ofLevel_paramsIn`, `VLocalDecl.LEquiv`/`VLCtx.LEquiv`). Names, namespaces and statements
are kept, so no downstream file changed except for the weakening: `FVLift'.find?`/`FVLift.find?`
take `Δ'.fvars.Nodup`, with 4 call sites (the "15" of the plan counted transitive users through
`weakFV'`). `Basic.lean` and `Transport.lean` import only the new modules; `TrSyn.rawShape`
moved to `RawShape.lean`. "Import only `Typing/Expr.lean`" was not literal: the context
relations' `wf` lemmas need the typing theory, so `Context.lean` keeps `Lemmas.lean`'s imports.

**Step 2. Syntactic `TrExprS` lemmas become corollaries. Done** (commit `refactor: derive the
syntactic TrExprS lemmas from TrSyn`). One-line corollaries now: `TrExprS.closed`, `fvarsIn`,
`unique'`, `unique`, `uniqueCtx`, `levelParamsIn`, `rawShape`, `instL_lequiv_of`, `uniqueS`,
`liftN_inv` (from `TrSyn.lowerBV`), `toSyn`, `of_syn`, `ContextFree.translation_unique` (via
`ContextFree.trSyn?_eq`). Not corollaries, contrary to the plan: `TrExprS.eqv` (it changes the
source, so the typing premises must be re-established, which needs a well-formed context),
`mkAppList_inv` (returns typed components), `ContextFree.targetClosed` (no `TrSyn` closedness
lemma for results). `TrExprSyn` is replaced by `TrSyn` in `Rules/Translation.lean` (inductive and
6 duplicated lemmas deleted, 4 renamed); the prototype's `TrSyn.instL_same` became `TrSyn.instL`.
`IsUnique` is retired outside `Verify/Environment/Primitive/*`: `forall₂_unique` and
`targets_eq_of_unique` lost the hypothesis, `MotiveDecl.familyUnique` and the 8 `IsUnique`
producers are gone. **Deferred** (files owned by the concurrent `-descriptor` rewrite):
`TrExprSyn` survives as an abbreviation with constructor aliases for
`Inductive/Prelude/EqSyntax.lean` (11 references, its tactic names the constructors); `noProj`
(85 references) and the remaining `IsUnique`/`unique'`/`unique` uses (76) are all in
`Verify/Environment/Primitive/{Basic,Condition,Clauses,DivMod,Bitwise,Gcd,Recursion}.lean`, and
`IsUnique`, `unique'`, `unique` stay (now proofs that ignore the hypothesis) until those files
switch to `unique_of_syn`/`uniqueCtx`.

**Step 3. Typed lemmas as products. Partly done** (commit `feat: transport the typed layer as
syntax, typing and residual`). `Typed.lean` now sits below `Lemmas.lean` (`TrExprS.wf` and
`VEnv.ContainsLits.mono` moved into it). Added: the residual transports (`TrResidual.weakFV'`,
`weakFV`, `weakBV`, `instN`, `instN_let`, `abstract`, `uninstantiateN`, `inst_fvar`,
`prependLevelParam`, `mono`) and the corresponding `TrTyped` transports, each the `TrSyn` lemma,
the typing lemma and the residual lemma, none needing a well-formed context. Re-proved through
`iff_typed` with unchanged statements: `TrExprS.prependLevelParam`, `TrExprS.inst_fvar`. **The
plan's premise was wrong for the rest**: `iff_typed` needs `Δ.WF` in both directions (the typing
of a looked-up let value, and the inversions that recover the typing premises), and
`TrExprS.weakFV'`, `weakBV`, `instN`, `instN_let`, `abstract`, `mono`, `eqv` do not assume it
(for `weakFV'` it is not even derivable: it would be strengthening). Routing them through
`TrTyped` would add hypotheses, so they keep their direct inductions. `TrExprS.instL` (a
`TrExpr` result) is also kept: its residual needs the let value's typing moved between
level-equivalent contexts, and there is no `VLCtx.LEquiv`-to-`IsDefEqCtx` lemma. Net: the
`Lemmas.lean` proofs did not shrink (about -70 lines), the gain is the context-free `TrTyped`
API.

**Step 4. `TrTyped` API. Done** (`Syntactic/TypedAPI.lean`, 238 lines). Smart constructors with
the premises of the `TrExprS` constructors (`bvar`/`fvar` also take `henv` and `hΔ`, since the
looked-up value's typing comes from the context); inversions `*_inv`, of which `bvar`, `fvar`,
`sort`, `lit`, `mdata` need no hypothesis and the others take `henv`/`hΔ` to invert the typing
of the result; `toTrExprS`/`TrExprS.toTrTyped`; and `TrTyped.induction`, with exactly
`TrExprS`'s cases (subderivations as `TrTyped`, every context in the motive well formed). It is
not an `@[induction_eliminator]`: it needs `henv` and `hΔ`, which such an eliminator cannot take,
so a consumer writes `TrTyped.induction henv (motive := ...) ... hΔ H` (the test rebuilds
`TrExprS` with it) or `induction H.toTrExprS henv hΔ`.

**Step 5. Migrate consumers that use only syntax. Done** (commit `refactor: retire IsUnique,
noProj and TrExprSyn`). The deferred step-2 items: `Inductive/Prelude/EqSyntax.lean` builds `TrSyn`
derivations directly, and the `TrExprSyn` abbreviation with its constructor aliases is deleted.
`TrExprS.IsUnique` (with its three literal lemmas) and `TrExprS.unique'` are deleted;
`TrExprS.unique` lost its `IsUnique` argument (it is `unique_of_syn`), and its 76 callers in
`Verify/Environment/Primitive/*`, `Inductive/Primitive/*`, `Inductive/Prelude/Eq.lean`,
`TypeChecker/{Reduce,IsDefEq}.lean` dropped the argument. `noProj` is deleted: it was only needed
because `TrExprS.weakR` did not transport the typing premise of `proj`, which it now does like the
other premises (weakening of the projection's typing), so `weakR`, `of_nil_any`,
`of_nil_unique`, `app1_nil_inv`, `app2_nil_inv`, `Condition.dite_tr_inv`/`dite_tr_inv'` and
`Condition.WF.natEq_decideTr` lost their `noProj` hypotheses, `CondOK` lost its `noProj`
conjunct (so `Condition.OK` is weaker and every theorem assuming it stronger), and
`Data.mkTyEq`/`mkTyEq1` lost `hcodU`. Induction proofs over `TrExprS` that never use the typing
arms moved to `TrSyn`, with the `TrExprS` statements kept as one-line corollaries:
`TrSyn.projNamesOK_of_source`, `TrSyn.headsApplied_of_avoids`, `Expr.HeadsApplied.trSyn` (with
`TrSyn.mkAppList_const_inv`, replacing the `TrExprS` version, which had no other user).
**Departures.** The other `induction` proofs over `TrExprS` listed in section 2 use the typing
arms (`TrExprS.mono`, `instL`, `substLevelParamsCore*`, `prependLevelParam_of_fresh`,
`avoids_of_constants`, `RelevantEq.uniq`, `targetProjsRegistered`, `projsRegistered`) or are
inductions over other relations that the grep counted; they stay. The context movers
`peel_outer`/`trExprS_dropN_nat` stay typed: their syntactic half is already a one-liner and the
typed half is the substitution argument of section 4. `Recursor/Context/ForallTelescope.lean` and
the frame records (`Inductive/Context.lean`) were left alone (concurrently refactored on the
mainline; section 5). Net: 20 files, -102 lines.

**Step 6. Telescope certificates on `TelWF`. Done** (commit `refactor: state constructor
telescope certificates as syntax plus typing`). `TelWF` moved from the prototype into
`Typing/TelescopeTranslation.lean`, and the certificate is now

```
def CtorTelescopeAt (venv : VEnv) (ci : ConstructorVal) : Prop :=
  ∃ T, trSyn? ci.levelParams [] ci.type = some T ∧
    TelWF venv ci.levelParams (AddInductive.constructorArity ci.type) [] ci.type T
```

`TelTrN` is restated as the pair `structure TelTrN ... where syn : TrSyn Us Δ e e'; tel : TelWF env
Us n Δ e e'` (the inductive with a `TrExprS` at each node and the existence premise at the delete
branch is gone; `CtorTelescopeAt.iff_telTrN` relates the two forms). Its transports are each the
`TrSyn` lemma and a `TelWF` lemma: `TelWF.weakFV` (now with `Δ'.fvars.Nodup` in place of
`Δ'.WF`), `TelWF.instN` (through `TrResidual.instN`), `TelWF.instL_core`, `TelWF.eqv`,
`TelWF.mono`; the delete branch in each is `TrSyn.lower`. The walk in `Projection.lean` and
`InferType.lean` consumes `TelTrN` unchanged in shape (`toTrExprS` takes `henv`/`hΔ`, which the
checking context supplies; `TelTrN.zero` builds the depth-zero certificate from a typed
translation). The ghost-telescope proof (`loop_base`, `loop_telTr`, `checkType.WF_telTr`) produces
`TelTrN` at the depth of the constructor arity directly: one `IsType` per kept and per deleted
residual, the residual from the run's typed translations, and the syntactic match at the delete
branch by `TrSyn.lower` and `TrSyn.unique` in place of `weakBV` and `uniqueCtx`. `TelTr` (the
unbounded certificate), `TelTr.toTelTrN`, `TelTr.eqv_toTelTrN`, `TrExprS.liftN_inv`/`lift_inv`,
`lift_const`, `TrExprS.const_ctx` and the prototype's `TelTrN.iff_syn_telWF`,
`CtorTelescopeAt.iff_trSyn`, `TelWF.delete_closed` (now `TelTrN.delete_closed`) are deleted.
The producers (`Constructor/Telescopes.lean`, `Constructor/Check.lean`,
`Primitive/Constructors.lean`, `Recursor/Entries/AddConstants.lean`, `Install/Environments.lean`,
`Nested/Restoration/ConstructorTelescopes.lean`) state `TelTrN` at the arity and build
`CtorTelescopeAt` by `CtorTelescopeAt.of_telTrN`; `CtorTelescopes` and its preservation proofs
are unchanged.
**Departures.** `TelescopeTranslationLemmas.lean` did not shrink by 250 lines (476 to 532, 13
files -34 lines overall): every transport keeps its induction over the spine, because the delete
branch must be commuted with the operation at every binder whether the certificate carries a
`TrExprS` or a typing judgment, and the file now also holds `TelWF`'s own lemmas and the
`TelTrN` wrappers that the prototype kept in `Strengthening.lean`. `TelWF.instL_core` reads the
typing at each node through `TrExprS.instL` (via `TrTyped.toTrExprS`, which needs the context to
be well formed), as section 5 anticipated: there is still no `VLCtx.LEquiv`-to-`IsDefEqCtx` lemma
to move the let residual between level-equivalent contexts directly. `TelWF.eqv` likewise
recovers the residual of the renamed source through `TrExprS.eqv` and so takes `Δ.WF`
(`TelTrN.eqv_arity` supplies it for closed certificates). The gain is in the statements: the
certificate is the computed translation plus typing judgments, and weakening no longer needs a
well-formed target context.

**Step 7 (optional). Replace the definition.** Define `TrExprS := TrTyped` (or rename
consumers to `TrTyped`). With step 4's eliminator and smart constructors, the 172 inversion
patterns `let .app h1 h2 h3 h4 := H` are the only syntax that breaks; they become
`obtain ⟨...⟩ := H.app_inv`. Size: 172 sites plus the 71 `induction` proofs (unchanged with the
custom eliminator, modulo argument order). Risk: medium-high for little gain once steps 2-6 are
done; recommended only if the inductive `TrExprS` is in the way of a later refactor. Until
then `TrExprS` and `TrTyped` coexist, related by `iff_typed`.

Refined after step 4: harder than estimated, and not recommended. `TrTyped` is equivalent to
`TrExprS` only given `henv` and `Δ.WF`, so replacing the definition changes the meaning of every
`TrExprS` statement in a context not known to be well formed (the frame records, the
`TrExprS.weakFV'`/`weakBV`/`instN` family). The inversions of the typed rules (`app`, `lam`,
`forallE`, `letE`, `proj`, `const`) and the induction principle need `henv`/`hΔ`, so the 172
inversion sites and the 71 `induction` proofs each gain those two arguments rather than being
unchanged.

## 4. The strengthening boundary afterwards

Every statement that moves a translation to a smaller context splits into a `TrSyn` part,
proved by `TrSyn.lowerBV`/`restrictFV` with no hypotheses, and one typing judgment
`VExpr.WF env U Δ.toCtx e₀'` (plus the let residual, empty on let-free syntax). The typing
judgments are discharged where they are today, never by declarative strengthening:

- projection walk: `TelWF`, from the checker's own acceptance run (ghost telescope);
- primitive recognizer: substitution of an inhabitant (`peel_outer`, `trExprS_dropN_nat`);
- scoped caches: never needed (`DESIGN.md` 5.2).

A grep for `VExpr.WF`/`IsType` hypotheses in a smaller context than their source then lists
every place strengthening is avoided, which is the audit `DESIGN.md` 5.1 currently states in
prose.

## 5. Risks

- **Level normalization.** `TrExprS.instL` concludes `TrExpr` (up to defeq) because
  `instantiateLevelParams` simplifies levels. `TrSyn.instL_lequiv` gives existence and `LEquiv`
  syntactically, but the typed `instL` still needs `LEquiv.defeq` for the result and for the let
  residual. No new difficulty, but no simplification either.
- **The let residual.** It cannot be removed: `TrExprS` accepts only well-typed dead lets, and
  `TrSyn` does not see them. Every typed transport keeps a one-case typing argument for it.
  Kernel sources with `let` are rare in the inductive pipeline (constructor and recursor types
  are let-free after `whnf`), so `iff_syn_wf` covers most uses.
- **Context well-formedness.** `iff_typed` needs `Δ.WF` and `env.Ordered`. Consumers that today
  produce `TrExprS` in contexts not yet known to be well formed (inside the inductive frame
  records) must keep using `TrExprS` directly until they have `Δ.WF`.
- **Merge order.** Steps 1-3 rewrite `Typing/Lemmas.lean` (3 concurrent refactors also touch
  the typing layer); do them after those land and in one short window.
- **Renaming `TrExprSyn`.** `EqSyntax.lean`'s tactic (`apply TrExprSyn.forallE` ...) names
  constructors. Resolved in step 2 by `abbrev TrExprSyn := TrSyn` with constructor aliases,
  which `apply` accepts; the rename of `EqSyntax.lean` itself is deferred to step 5.
