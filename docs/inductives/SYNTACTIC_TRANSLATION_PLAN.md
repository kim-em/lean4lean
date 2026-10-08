# Separating syntactic translation from typed admissibility

This is the migration plan for replacing the typed translation relation `TrExprS`
(`Lean4Lean/Verify/Typing/Expr.lean`) by a syntactic translation plus a typed layer, following
BIG IDEA 2 of the checker review. Step 0 (the prototype) is done on
`agent/verify-inductives-syntr`; the remaining steps are not started. All numbers are from
`grep -c`/`wc -l` on that branch (base `b8fb81be`).

## 1. What the prototype establishes

New files, none used by the verification (no audit roots change):

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
3. Iota rules (`Inductive/Rules/Translation.lean`). `TrExprSyn` *is* `TrSyn`
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

**Step 1. Syntactic base below `Lemmas.lean`.** Move the syntactic infrastructure out of
`Typing/Lemmas.lean` into `Typing/Syntactic/Context.lean`: `Closed`/`FVarsIn` lemmas (lines
16-330) and the `VLCtx` relations `FVLift'`, `FVLift`, `BVLift`, `InstN`, `InstLet`, `Abstract`
with their `find?` lemmas (lines 367-735). Weaken `FVLift'.find?`/`FVLift.find?` from
`Δ'.WF env U` to `Δ'.fvars.Nodup` (the prototype's `find?_nodup`; 15 call sites, each given
`hΔ'.fvars_nodup`). Rebase `Syntactic/Basic.lean` and `Transport.lean` onto it, so that they
import only `Typing/Expr.lean`. Delete the duplicates (`TrExprSyn`'s copies of
`IsUniqueCtx.find?_some`, `BVLift.find?_lift_inv`). Size: about 700 lines moved, 50 deleted,
no proof changes. Risk: low.

**Step 2. Syntactic `TrExprS` lemmas become corollaries.** Re-prove, with unchanged
statements, by `H.toTrSyn.<lemma>`: `TrExprS.closed`, `fvarsIn`, `fvarsList`, `levelParamsIn`
(`UniverseSupport.lean`), `unique'`, `unique`, `uniqueCtx`, `uniqueS`, `eqv` (and
`TrExpr.eqv`), `rawShape` (`RawShape.lean`), `instL_lequiv_of` (`LevelEquiv.lean`), `liftN_inv`,
`lift_inv` (`TelescopeTranslationLemmas.lean`), `toSyn`, `of_syn`; and in
`Inductive/Nested/Lowering/Expansion/Contexts.lean`/`AuxiliarySources.lean`,
`ContextFree.translation_unique`/`targetClosed`, and `Constructor/Positivity.lean`'s
`mkAppList_inv`. Replace `TrExprSyn` by `TrSyn` (97 references, a mechanical rename: the constructors have the
same names and arguments, `TrExprSyn.iff_trSyn`) and delete its lemmas. Then
retire `TrExprS.IsUnique`: `TrSyn.unique` has no side condition, so `unique'` callers (11) move
to `TrExprS.unique_of_syn`, and `noProj` with its 84 references in the primitive files
(`Primitive/Condition.lean`, `DivMod.lean`, `Bitwise.lean`, `Clauses.lean`, `Gcd.lean`), which
exists only to produce `IsUnique`, is deleted; `of_nil_unique` loses its `noProj` hypothesis.
Size: about -400 lines in `Typing/*` and `Rules/Translation.lean`, about -250 in the primitive
files; statement changes only where `IsUnique`/`noProj` hypotheses disappear (callers just drop
an argument). Risk: low; the `noProj` deletion touches many proof scripts but only removes
arguments.

**Step 3. Typed lemmas as products.** Prove the residual's transport lemmas (`TrResidual`
under `weakFV'`, `weakBV`, `instN`, `instN_let`, `abstract`, `prependLevelParam`, `instL`, `mono`;
`weakBV` is in the prototype). Only the `letE` case carries typing (the let value's
`HasType`, transported by `HasType.weakN`/`instN`/`instL`); `instL` needs the value's type up to
`LEquiv`, via `VExpr.LEquiv.defeq`. Then re-prove `TrExprS.weakFV'`, `weakFV`, `weakBV`, `instN`,
`instN_let`, `inst`, `inst_let`, `inst_fvar`, `abstract`, `uninstantiate*`, `prependLevelParam`,
`instL` (`TrExpr` result) and `mono` from `TrExprS.iff_typed` as syntax + `VExpr.WF` transport +
residual transport, as `TrTyped.weakBV` does. Size: about 480 lines of `Lemmas.lean` replaced
by about 300 (residual transport is 11-case boilerplate with one typed case). Gain: not lines;
the syntactic lemmas stop requiring `henv`/`hΔ`, which is what downstream proofs pay for.
Risk: medium; `inst_fvar` and `weakFV'` currently consume `Δ'.WF` for the new binder's typing,
which moves into the residual/`WF` transport.

**Step 4. `TrTyped` API.** Add smart constructors with the signatures of the `TrExprS`
constructors (`TrTyped.app h1 h2 hf ha`, ...), the inversions (`TrTyped.app_inv`, ...), and an
`@[induction_eliminator]` for `TrTyped` whose cases have exactly `TrExprS`'s premises (derived
from `iff_typed`). Size: about 300 lines. Risk: low.

**Step 5. Migrate consumers that use only syntax.** Where a proof uses a `TrExprS` hypothesis
only to locate a target, compare targets, or move a source between contexts, replace it by
`TrSyn`. Candidates by grep: the 71 `induction` proofs over `TrExprS` (18 files), most of which
never use the typing arms (`Nested/Restoration/*` 6 files, `ProjNames.lean`,
`TableAgreement.lean`, `RecursorRenaming.lean`, `CommutationUniform.lean`,
`Declarations.lean`, `TranslationPreservation.lean`, `DeclarationUniverses.lean`,
`Assembly.lean`, `EquivManager.lean`), and the context movers in the primitive files
(`TrExprS.peel_outer`, `MLCtx.trExprS_dropN_nat`: 14 references; their syntactic half is
`TrSyn.lowerBV`, the typed half stays a substitution argument because it is typing
strengthening). Order: `Verify/Typing` (210 occurrences), `Verify/Environment` (533),
`Verify/TypeChecker` (291), then `Verify/Inductive` (2,010) bottom-up along imports. Size:
estimated a quarter of the 3,116 occurrences change, about 750 lines touched, mostly in
statements of auxiliary lemmas. Risk: medium; each file is independent, but the inductive
pipeline's frame records (`Inductive/Context.lean`, 141 occurrences) are shared by many files
and should be migrated in one step.

**Step 6. Telescope certificates on `TelWF`.** Restate `CtorTelescopeAt` as
`∃ T, trSyn? ci.levelParams [] ci.type = some T ∧ TelWF ...` (`CtorTelescopeAt.iff_trSyn`
shows the equivalence), the walk in `Projection.lean`
(`instantiateProjectionParameters.WF_tel`, `instantiateProjectionFields.WF_tel`, `WF_cert`,
`WF_ctorTelescopes`) on `TrSyn` + `TelWF` (the delete step is `TelWF.delete_closed`), and the
ghost-telescope verification (`GhostTelescope.lean`, `loop_base`, `loop_telTr`,
`checkType.WF_telTr`) to produce `TelWF` (one `IsType` per residual) instead of `TelTr`.
`CtorTelescopes` keeps its shape; its preservation proofs (`CtorTelescopesPreserved`, 211
`CtorTelescope*` references, mostly passing the invariant through) are unaffected except at
the producers (`Install/Environments.lean`, `Primitive/Constructors.lean`,
`Nested/Restoration/ConstructorTelescopes.lean`, `Recursor/Entries/AddConstants.lean`). `TelTr`
(29 references) is deleted. Size: about 400 lines changed in `Projection.lean`,
`GhostTelescope.lean`, `TelescopeTranslation*.lean`; `TelescopeTranslationLemmas.lean` (564
lines) shrinks by about 250, since `TelTrN.weakFV`/`instN`/`instL_core`/`eqv` become `TelWF`
transport (typing only) plus `TrSyn` lemmas. Risk: medium; `TelTrN.instL_core` interacts with
level normalization (`LEquiv`), where `TelWF` must be stated up to `LEquiv` of the residual.

**Step 7 (optional). Replace the definition.** Define `TrExprS := TrTyped` (or rename
consumers to `TrTyped`). With step 4's eliminator and smart constructors, the 172 inversion
patterns `let .app h1 h2 h3 h4 := H` are the only syntax that breaks; they become
`obtain ⟨...⟩ := H.app_inv`. Size: 172 sites plus the 71 `induction` proofs (unchanged with the
custom eliminator, modulo argument order). Risk: medium-high for little gain once steps 2-6 are
done; recommended only if the inductive `TrExprS` is in the way of a later refactor. Until
then `TrExprS` and `TrTyped` coexist, related by `iff_typed`.

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
  constructors, so `TrExprSyn` cannot simply become an abbreviation; the rename to `TrSyn` is
  mechanical because the constructors agree name for name (`TrExprSyn.iff_trSyn` is proved
  constructor for constructor).
