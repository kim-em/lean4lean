# E1 follow-up: inductive-side strengthening sites (G3/G4), design

Worktree `lean4lean-e1`, branch `agent/verify-inductives-e1`, HEAD 087c898 (2026-10-06). Read-only study.
Fresh grep of `weakN_iff|weak'_iff|weakN_inv|weak'_inv|weakFV_inv|weakFV'_inv|weakBV_inv|restrictUpSet|skips`
under `Lean4Lean/Verify/Inductive/`: 79 hits, saved with the enclosing declaration of each hit in
`/tmp/l4l-scratch/e1-inductive-grep.txt`. The `skips` hits are all docstrings
(`Bindings.lean:15`, `LoopType.lean:1379`, `CompletedEquationRecursiveCall.lean:3901`,
`Equation/RecursiveCall.lean:3946`). The two class (a) sites (`FirstPass.lean:2436/2521`) were fixed
in 087c898 and now use `IsDefEqU.weakN`. Cone status comes from `/tmp/l4l-scratch/weakn-graph-all.tsv`.

## 0. Summary

- **Every remaining G3/G4 site is a fact computed by a checker run in a context larger than the one
  the proof needs.** The exceptions are a few generic lemmas that are false as stated. The large
  contexts come from how `Inductive/Add.lean` nests binders:
  - `loopType` calls its continuation inside the index binders (Add.lean:127-129, 142). So family
    d >= 1 is checked inside family 0's parameters *and* every earlier family's indices.
  - `runWithStats` (constructors and recursors) runs inside every family's header indices, which are
    stale by then.
  - `loopInd1` nests indices, the major and the motive per family (Add.lean:466-470).
  - `loopCtors` nests each constructor's minor (Add.lean:567), so later constructors' runs happen
    under earlier minors.
  - `loopUArgs` runs under all fields, motives, earlier minors and earlier induction hypotheses.
- **What the checker reads from the local context.** Each lifted call is a fresh `TypeChecker.M.run`
  on `c.lctx` (Add.lean:79-81). Inside a run the checker reads the local context only through:
  - `find?` on specific free variables (TypeChecker.lean:130, 383, 423, 578);
  - `mkForall`/`mkLambda` over its own fresh variables (TypeChecker.lean:174, 238, 1032;
    Primitive.lean:197, 291);
  - error payloads (TypeChecker.lean:114, 122, 232, 282, 350).

  There is no `.index` read and no global read. So locality (L) is true, and runs in a narrower
  context compute the same thing.
- **Recommendation: (P) with a second, checker-visible local context in `AddInductive.Context`,
  plus a handful of local fixes.**
  - Make the narrow context the one the checker actually runs in.
  - Every fact is then produced in the narrow scope.
  - Facts in the larger contexts are recovered by weakening and construction, which are true.
  - (P) avoids (L) completely for `addDecl.WF`.
- **The proof bookkeeping is the same under both strategies.** Under (L) the proof still has to
  build and maintain a *ghost* narrow `MLCtx` with its own `MLCtx.WF`, because (L) needs a WF
  restricted `VContext` to apply the checker's WF theorems. Dependency closure does not give that WF
  (see 2.4). (P) makes that ghost context executable and drops the 4-7k-line simulation theorem.
- (L) remains the informal argument that (P) changes no result; it can be checked empirically by a
  differential test (step 7).

## 1. Per-site table

Classes of removed variables:
- (i) header/family binders: parameters, header indices (including stale ones), and recursor
  indices/majors of other families;
- (ii) recursor motives, minors and induction-hypothesis binders;
- (iii) constructor field or equation field binders;
- (iv) other: the binder being opened itself, or abstract bound-variable groups.

Principles:
- **Subst:** substitution with an inhabitant (`IsDefEq.instN`);
- **RT:** round trip;
- **Syn:** syntactic strengthening (`TrExprSyn`);
- **Sort:** uniqueness plus `sort_inv` (`IsDefEqU.sort_inv`, Theory/Typing/Injectivity.lean:10);
- **Constr:** construction, i.e. weaken a narrow fact and use `uniq`/`uniqueS`/`telescope_unique`;
- **L:** the fresh-run locality theorem;
- **P:** a producer change.

The table names the principle that suffices; "P (or L)" means either works and P is recommended.
**Subst never applies:** the removed binders are free variables with no inhabitant in the narrow
scope (motives, index variables, fields). **Syn never suffices:** every site needs a typed relation
(`TrExprS`, `IsDefEqU`, `HasType`), and `TrExprS` contains typing premises.

### 1.1 Header phase (G3)

| site (decl line; use lines) | cone | checker run (Add.lean) and context change | removed | principle |
|---|---|---|---|---|
| Header/Existential.lean:123 `checkClosedType.rawSourceTranslationWF` (:142 `weakFV'_inv`) | yes | `checkType` of a closed header or constructor type (Add.lean:101-104, called at 138 and 322). For header 0 the context is already `{}`. For header d >= 1 it is params plus the indices of families before d; for constructors it is params plus all header indices. Narrowed to `[]`. | (i) | **P**: `checkClosedType` runs under `withCheckLCtx {}`. The run is then already in `[]` (RT for header 0 today). L with S = {} also works. |
| Header/LoopInd.lean:141 `initialLaterHeaderDefEqOfTranslation` (:164, :177 `weakFV_inv`; :198 `weakN_iff`) | yes | `whnf` of a closed later header (Add.lean:142) in the first family's params plus earlier indices; narrowed to `[]`. | (i) | **P**: closed `whnf` under `{}`. The proof then becomes the family-0 path. |
| Header/RawMaterialization.lean:196 `CheckedSourceHeaderTranslation.checkedTerminal` (:225 `IsType.weakN_iff`) | yes | The fact is in `Hc.mlctx`, the context where the header's check ran; narrowed to `[]`. | (i) | **P**: with the header check and telescope run from `{}`, `Hc.mlctx = []` and `W` is the identity lift. For family 0 this already holds. Strengthening a sort-typed fact would be false, so no local fix. |
| Header/LoopType.lean:3781 `LaterParameterScope.domainTranslation` (:3792 `weakFV_inv`) | yes | The later family's parameter domain `dom` is a domain of the previous `whnf` output (Add.lean:125/142), translated in the full context; narrowed to `H.older` = parameters before i. | (i): the first family's later params p_>=i and earlier families' indices | **P**: parameter snapshots, `whnf` at step i-1 under `paramCheck[i]`. Then forall inversion of the narrow output gives the domain's narrow translation (**Constr**). |
| LoopType.lean:3857 `LaterParameterScope.domainDefEq` (:3891 `weakN_iff`) | yes | `isDefEq dom (getType param)` (Add.lean:122), full context narrowed to `H.older`. | (i) | **P**: run under `paramCheck[i]`. |
| LoopType.lean:4040 `LaterParameterScope.normalizedBody` (:4077 `weakFV_inv`; :4096) | yes | `whnf (body.instantiate1 param)` (Add.lean:125), full context narrowed to `fv :: older`. | (i) | **P**: run under `paramCheck[i+1]`. |
| LoopType.lean:5258 `laterIndexSynthesisWF` (:5410 `weak'_iff`) | yes | Index-step `whnf` (Add.lean:129) of family d >= 1, under earlier families' indices; narrowed to `indexType :: scope`. | (i) | **P**: family d's index chain is opened on top of `paramCheckAll`. |
| LoopType.lean:926 `NarrowRuntimeScope.resultSort` (:949) | yes | `ensureSort` at the end of the telescope (Add.lean:143). | (i) | **P**, same chain. |
| LoopType.lean:739 `NarrowRuntimeScope.restrict` (:746), :788 `restrictTrExpr` (:810) | yes | Header index steps (Add.lean:129), and positivity `whnf` (Add.lean:282) under `loopCtor` fields. Users: Constructor/Positivity.lean:3268 `refinesNarrow`, Constructor/Normalization.lean:35 `uniformNormalFormNarrow`. | (i): earlier families' indices, or all stale header indices in the constructor phase | **P**: header chain; constructors run on top of `paramCheckAll`. Runtime then equals the scope, so `restrict` disappears (RT). |
| LoopType.lean:816 `NarrowRuntimeScope.hasTypeOfFull` (:829); :1164 `FVarNarrowScope.hasTypeOfFull` (:1177); Equation/RecursiveCallScope.lean:150 `FVarNarrowCore.hasTypeOfFull` (:162, off cone) | yes, yes, no | A runtime `narrow'^ : sort u` transferred to the scope. | (i)/(ii), depending on the caller | **Sort**, local: add the premise `IsType scope narrow'`, then weaken, `uniqU` in runtime, `sort_inv`, `sortDF`. Under P the lemmas become unnecessary (the typing is produced in the scope); keep this fix only as the fallback if P is postponed. |
| LoopType.lean:836 `NarrowRuntimeScope.hasTypeOfFullPair` (:854); :1182 `FVarNarrowScope.hasTypeOfFullPair` (:1200) | no | General fixed-type typing strengthening; false. | n/a | **Delete** now (0 users). |
| Header/Elimination.lean:193 `ContextWF.ConsumedDomain.proof_of_largeEliminationCheck` (:210 `HasType.weakN_iff`) | yes | `ensureType dom` (Add.lean:407) runs *inside* the field's own binder (Add.lean:404); `Gamma, x:A` narrowed to `Gamma`. | (iv): the field binder itself | **Sort**, local, now, about 15-30 lines. `Hdom.isType` gives `Gamma |- A : sort u`. Weaken, use uniqueness against `Hprop`, then `IsDefEqU.sort_inv` gives `u ~ 0`, then `sortDF` in `Gamma`. (P alternative: hoist `ensureType` before `withLocalDecl`.) |

### 1.2 Recursor first pass and recursor context (G3/G4)

| site | cone | run and context change | removed | principle |
|---|---|---|---|---|
| Context.lean:1474 `RecursorContextWF.initialClosedHeaderDefEq` (:1497, :1510 `weakFV_inv`; :1532 `weakN_iff`) | yes | Closed `whnf indTypes[dIdx].type` (Add.lean:462) in the whole recursor context; narrowed to `[]`. | (i), (ii): params, stale header indices, earlier families' indices, majors and motives | **P**: run under `{}`. |
| Constructor/Replay.lean:1752 `RecursorLaterParameterScope.normalizedBody` (:1789, :1808) | yes | `loopArgs1` parameter step `whnf` (Add.lean:448) in the recursor context; narrowed to `fv :: older`. | (i), (ii) | **P**: run under `paramCheck[i+1]`. |
| Replay.lean:1506 `RecursorLaterParameterScope.domainTranslation` (:1518); :1667 `domainDefEq` (:1702) | no, no | Same steps. | (i), (ii) | `domainDefEq`: delete (0 users). `domainTranslation` follows from the row above by **Constr** (forall inversion). |
| Recursor/FirstPass.lean:3230 `continueRecursorIndexSynthesisSemantics` (:3590 `weak'_iff`); :2762 `continueIndexSynthesisSemantics` (:3000, off-cone twin) | yes / no | Index-step `whnf` (Add.lean:451) in the recursor context; narrowed to `indexType :: scope`. | (i): stale header indices and earlier families' indices/majors; (ii): earlier motives | **P**: each family's index chain is opened in the checker context on top of `paramCheckAll`; majors and motives go into the main context only. Delete the off-cone twin. |
| Recursor/RecursiveCalls.lean:156 `mkRecInfos.loopInd1.resultSemantics` (:823 `IsType.weak'_iff`) | yes | `IsType (I params indices)` in the narrow scope, from the runtime major type. | (i), (ii) | **Constr**: build it from the constant's type plus the narrow index-domain translations. It is conditional on the row above, which supplies those translations under P. About 60-100 lines. |
| Recursor/CanonicalMotiveReplay.lean:10 `RecursorMotiveTelescopeSeed.consumedTranslation` (:31 `weakFV'_inv`; :42, :48) | yes | Not a checker run: the motive type `mkForall indices (mkForall major sort)` (Add.lean:468) is translated in the expanded context; narrowed to `motiveSourceScope`. | (i): earlier families' indices/majors and stale header indices; (ii): earlier motives | **Constr** from the narrow index translations, which come from the P index chain. Then `uniq` in the narrow scope. About 50 lines after the FirstPass row. |
| CompletedEquationMotive.lean:1088 `CompletedRecursorPhasesResult.finalOwnerNarrowMotiveTranslationAt` (:1137, :1156); Equation/Motive.lean:1103 twin (:1153, :1172) | yes / no | Same seed at the installed stage. | (i), (ii) | **RT**: reuse the repaired `consumedTranslation` (same seed `S`), about 30 lines. Delete the twin. |

### 1.3 Per-field rows, equations and generic lemmas (G4)

| site | cone | run and context change | removed | principle |
|---|---|---|---|---|
| Recursor/CanonicalRecursiveShape.lean:70 `TrExprS.weakBV_inv_lift` (:105-153), used by :259 `removeBeforeInner` (:271) | yes | Bound-variable strengthening inside the generator telescope that comes from the closed `checkRecursorTypes` run (Add.lean:739-744, already `{}`). | (iv)/(ii): the motive group and the earlier minor/hypothesis group, as de Bruijn groups | False as a lemma (no inhabitants). **Constr**: a forward lemma (given a small translation `t0`, `weakBV` plus `uniqueS` gives `T = t0.liftN ..`), about 40-80 lines, can be written now. The small translations of the hypothesis sources come from the per-field rows (**P**: `loopUArgs` under params + fields < f + args). |
| Recursor/Telescope.lean:2563 `TrExprS.dropFVarPrefix` (:2574 `weakFV_inv`) → Recursor/Origins.lean:4467 `parameterTranslationAtSuffix` | yes | Drops the ambient prefix from parameter-level translations. | (i), (ii) | **P** (the parameter steps run under the snapshots), then **RT**: the translation was made when the parameters were the live context. |
| CompletedEquationRecursiveCall.lean:2515 `finalSelectedMinorNarrowFieldAlignment` (:2687 `weak'_iff`); Equation/RecursiveCall.lean:2542 twin (:2717) | yes / no | Translation uniqueness in `baseExpanded`; narrowed to `parameterDecls`. | (ii), (i): rule-wide ambient binders | **Constr**: domain-by-domain `TrExprS.uniq` in the narrow field contexts, about 150 lines. Its inputs come from the `dropFVarPrefix` row and from `FVarNarrowSources`, which are P products. Delete the twin. |
| CompletedEquationRhs.lean:991 `finalCanonicalMinorFieldContextOfApplication` (:1147 `HasType.weakN_iff`) | yes | The minor `bvar` is typed under the trailing equation-field binders (k = 0 drop). | (iii) | **RT/lookup**, local, now: `HasType.bvar` with the minor's `Lookup` in `outer` plus `hminorType`, about 30-40 lines. Its other dependency is `canonicalApplicationContext` (next rows). |
| Basic.lean:1474 `VEnv.HasType.canonicalApplicationContext_of_weakened` (:1493) | yes | Same pattern as the Rhs row. | (iii) | Same lookup at the caller; delete the lemma. |
| Basic.lean:1182 `VExpr.WF.mkApps_canonical_prefix` (:1219) | yes, via the next row only | Generic inversion; false. | (iv) | **Delete.** Its only user is `canonicalApplicationContext`. |
| Basic.lean:1290 `VEnv.HasType.canonicalApplicationContext` (:1417) | yes | Generic context conversion from a well-formed canonical application; false. | (iii)/(iv) | **Constr** at the consumers: Nested/Replacement.lean:1810 `ownerMotiveSuffixContext` (cone) and the Rhs row. Both telescopes come from the same header/field telescopes, so use `TrExprS.telescope_unique` (Recursor/TelescopeUniqueness.lean). Needs the narrow field translations (P). About 150-400 lines per consumer. |
| Equation/Setup.lean:3340 `VEnv.IsDefEqCtx.cancelLiftForallDomains` (:3351 `OnCtx.weak'_inv`; :3376) | yes | Telescope conversion from `expanded` down to `outer`; false. Users: CompletedEquationRecursiveCall.lean:1866, 2145. | (iii) | **Constr** from the P per-field rows. |
| Equation/RecursiveCallScope.lean:93 `FVarNarrowCore.restrict` (:99); Header/LoopType.lean:1117 `FVarNarrowScope.restrict` (:1124) | yes | Translations restricted to generator-shaped scopes (params + motives + earlier minors + fields, skipping indices and majors). | (i), (iii) | **Constr**: *weaken* the checker-narrow translations (P) into the generator scope along `FVLift'`, which is the true direction. Delete `restrict`. |
| RecursiveCallScope.lean:130 `FVarNarrowCore.hasTypeOfFullPair` (:147) | yes, 6 users in CompletedEquationRecursiveCall / Equation/RecursiveCall | Typing of recursive-call arguments and of the major. | (ii), (i), (iii) | **P**: the typing comes from the per-field `inferType`/`whnf` run in params + fields < f + args; then **Constr**/weakening. |
| `NarrowRuntimeScope.scopeWF` / `FVarNarrowScope.scopeWF` (via `VLCtx.FVLift'.wf`, Verify/Typing/Lemmas.lean:451) | yes | The scope's WF is derived from runtime WF by strengthening. | all | **RT** under P: the narrow scope is the checker `MLCtx`, whose WF is maintained. |
| Off cone, delete: Recursor/ContextRestriction.lean:18 `restrictUpSet`, :98 `restrictUpSetCtx`; Recursor/Bindings.lean:142 `restrictTrExprS`; Recursor/RecursiveShapeRow.lean:74 `restrictToFieldPrefix`; Recursor/CanonicalConstructorModel.lean:8, :30; Recursor/CanonicalConstructorReplay.lean:6; Nested/Replacement.lean:1744 `ownerMotiveFirstDomainDefEq` | no | Generic translation restriction. | (i), (ii), (iii) | Delete. Under P the per-field restricted context of HANDOFF item 7 is literally the checker context of the `loopUArgs` run (RT), so this restriction programme is unnecessary. |

**Fixable now, without L or P:**
- Elimination.lean:193 (Sort);
- CompletedEquationRhs.lean:991 and Basic.lean:1474 (lookup);
- the forward replacement of `weakBV_inv_lift` (statement and proof; callers later);
- deleting `mkApps_canonical_prefix`, the two `hasTypeOfFullPair` in LoopType, `RecursorLaterParameterScope.domainDefEq`, and the off-cone list above;
- the `hasTypeOfFull` x3 Sort fix, only if P is deferred.

## 2. Strategy (L): fresh-run locality theorem

### 2.1 What exists

`Verify/TypeChecker/AlphaLocality.lean` (1286 lines) and `WHNFAlpha.lean` (1253) prove *alpha-renaming*
equivariance of `whnf`. Their relation is `ExprAlphaUnder` / `ClosedExprAlphaUnder` over ordered binder
spines, and the contexts are related by `LocalContext.OrderedBinderRenaming` / `Context.OrderedBinderRenaming shared ...`.

Coverage:
- public-`whnf` cache hit and miss (`whnf_cache_hit_success_alpha`, `WhnfLoopAlphaOn.inner`);
- the immediate, forall and mdata cases;
- free-variable heads, both renamed and shared (`whnfAlphaOnFVarAt`, `whnfAlphaOnSharedFVar`);
- native and nat-literal binary operations, `reducePow`, `reduceBinNatPred`.

The `whnfCore` reduction loop body (beta, let, projection, iota, quotient, delta, primitives) is a
predicate (`WhnfLoopAlphaOn`) that is not discharged. There is nothing for `inferType` beyond
`inferFVarShared/At`, and nothing for `isDefEq`.

Every statement is **partial**: "if both sides succeed then the results are related". (L) needs
**success transfer**: if the full run succeeds, the narrow run succeeds with the same value. So the
existing lemmas can be reused only for the shared-free-variable lookup facts.

### 2.2 Statement

The checker reads `find?` results without their `index` field. Narrow `MLCtx.lctx` indices differ,
so agreement is modulo `index`.

```lean
/-- Two checker contexts that agree on a dependency-closed set `D`. -/
structure TypeChecker.Context.AgreeOn (D : FVarId → Prop) (c c' : Context) : Prop where
  env : c'.env = c.env
  safety : c'.safety = c.safety
  lparams : c'.lparams = c.lparams
  fuel : c'.fuel = c.fuel
  eagerReduce : c'.eagerReduce = c.eagerReduce
  find : ∀ fv, D fv → (c'.lctx.find? fv).map LocalDecl.dropIndex = (c.lctx.find? fv).map LocalDecl.dropIndex
  closed : ∀ fv d, D fv → c.lctx.find? fv = some d → d.type.FVarsIn D ∧ d.value.FVarsIn D
  kernelFresh : ∀ fv, ({} : State).ngen.Reserves fv → c.lctx.find? fv = none ∧ c'.lctx.find? fv = none

/-- Frame property of one computation: from states whose caches mention only `D`. -/
def TypeChecker.M.Frame (D : FVarId → Prop) (x : M α) : Prop :=
  ∀ c c' s, c.AgreeOn D c' → s.ScopedIn D →
    ∀ a s', x c s = .ok (a, s') → x c' s = .ok (a, s') ∧ s'.ScopedIn D

theorem whnf.frame       (h : e.FVarsIn D) : (whnf e).Frame D
theorem inferType.frame  (h : e.FVarsIn D) : (inferType e b).Frame D
theorem isDefEq.frame    (h₁ : e₁.FVarsIn D) (h₂ : e₂.FVarsIn D) : (isDefEq e₁ e₂).Frame D
-- likewise checkType, ensureSort, ensureType
```

Here `State.ScopedIn D s` means every key and value of `inferTypeI`/`inferTypeC`/`whnfCoreCache`/`whnfCache`
is `FVarsIn D`. `{}` is trivially scoped. Two consequences of the statement:
- The runs are compared on success only: error payloads embed the local context and differ.
- The final state is literally equal. The equivalence manager and the failure cache need no
  invariant, because they return only booleans and are never dereferenced into local-context reads.

The induction must extend `D` by the fresh variable at each checker binder. E1's `State.leaveScope`
restores the caches on exit, so every entry mentioning that variable disappears with it; this is
what keeps `ScopedIn` an invariant.

**Inductive-side corollary (WF transfer).** Let `Hc : ContextWF c` be the runtime context. Let `N` be a
narrow context: an `MLCtx` with `N.mlctx_wf : N.mlctx.WF venv Us`, whose declarations are those of
`Hc.mlctx` for the free variables in `N` (same `Expr` types), and with
`IsFVarUpSet (· ∈ N.vlctx.fvars) Hc.mlctx.vlctx`. If the inputs are `FVarsIn N.fvars` and
`x.WF (narrowVContext N) {} Q`, then `((monadLift x : AddInductive.M α) c).WF (Q · )`.

So the full run's result satisfies whatever the narrow run's own WF theorem gives, in `N.vlctx`. As the
brief notes, this is not strengthening of an abstract relation: the narrow derivation is produced by
the narrow run.

### 2.3 What is missing for (L), honestly

1. **Monadic relational combinators** for `ReaderT Context (StateT State (Except _))` and `RecM`:
   bind, pure, throw/tryCatch with success-only comparison, `withReader` for `withLocalDecl`/`withLetDecl`
   on both sides with the same fresh id, `withFreshId` with E1's `leaveScope`, fuel loops, `Methods`
   knot-tying. About 300-500 lines.
2. **The unary scope invariant `ScopedIn`.** Much of it exists:
   - `whnf.WF`/`whnfCore.WF` give `FVarsBelow` (Verify/TypeChecker.lean:374-379), and
     `inferType.WF_below` exists (Basic.lean:1670-1677).
   - The cache invariants carry `FVarsBelow` (`ConditionallyWHNF`, `ConditionallyHasType`,
     Verify/Typing/ConditionallyTyped.lean:40-100).

   Missing: `FVarsBelow` for the internal results of `isDefEq`'s lazy-delta and expansion helpers,
   projection, struct eta, unit-like, and the Primitive gadgets. These must be proved in the
   full-context run, which needs the existing WF facts at each step. The universe-support
   invariant (HANDOFF item 7, done, estimated 1.5k-2.2k) is the precedent; this is smaller because
   much is present. About 500-1500 lines.
3. **The relational per-function proof.** It covers all executable checker code:
   - TypeChecker.lean, 1034 lines;
   - Primitive.lean, 623 (natRec/WF unfolding gadgets);
   - Inductive/Reduce.lean, 119 (iota, K, struct);
   - Quot.lean, 132;
   - EquivManager.lean, 65 (state only).

   The relation is identity (same state, context swap), which is simpler than alpha. But totality
   (success transfer) forces each step's inversion and re-execution, unlike WHNFAlpha's
   both-succeed hypotheses. By the WHNFAlpha ratio (about 1250 lines for a small fragment of
   `whnf`): **about 3-6k lines.**
   - `inferType`: each case reads only `find?` on input free variables, plus `mkForall` over fresh ones.
   - `isDefEq` (lazy delta): unfolding depends on the environment only; the comparisons recurse
     on terms in `D`.
   - `EquivManager`: with E1 every lifted call starts with an empty manager, and scope exits
     restore it; equal states need no invariant.
4. **Typing WF transfer to the restricted `vlctx`.** By the corollary, the narrow run's own
   `inferType.WF`/`whnf.WF`/`isDefEq.WF` give `TrTyping`/`TrExpr`/`IsDefEqU` in `N.vlctx`. Two inputs
   are needed:
   - the narrow translation of every *input* (`whnf.WF` and `isDefEq.WF` take `TrExprS c.vlctx e e'`;
     only `checkType` takes a bare `FVarsIn`);
   - `N.mlctx.WF`.

   Neither comes from the full context, which leads to the subtlety in 2.4.

Total (L) theorem: **4-8k lines**, plus the bookkeeping shared with (P) (2.4) and about 15 site
applications at 40-80 lines each.

### 2.4 The `VLCtx.WF` subtlety

`MLCtx.WF` (Verify/TypeChecker/Basic.lean:163) asks, for each declaration, for `TrExprS` of its type in
its *own narrow prefix* and `IsType` there. A dependency-closed (`IsFVarUpSet`) subset of a WF
context is **not** WF in general.

Counterexample: in `Gamma, q : P v, z : T` with `T := (fun x : SJ => Prop) zI`, `T` mentions no `q`
but is typed only via `SI ≡ SJ`, which needs `q`. So `{z} ∪ deps(T)` is syntactically closed but
ill-formed.

Hence the narrow `MLCtx` must be **built inductively alongside the run**. When `Add.lean` opens a
narrow-relevant binder with domain `dom`, the ghost context is extended with `TrExprS N dom dom'` and
`IsType N dom'`. These come from the preceding narrow run's WF (the `whnf` output that `dom` is a
domain of), or from `checkType` in `{}` for the closed source.

Two things to note:
- Dependency closure is only the syntactic side condition (`AgreeOn.closed`, and `upset` for the
  weakening back to the runtime context).
- This bookkeeping is what `NarrowRuntimeScope`/`FVarNarrowScope`/`FVarNarrowCore` try to supply today,
  through the false `restrict`/`FVLift'.wf`. Under (L) they must be rebuilt as narrow `MLCtx`
  companions. That is the same work (P) needs.

## 3. Strategy (P): producer changes

### 3.1 Executable change: a checker-visible context

All changes are in `Lean4Lean/Inductive/Add.lean`.

1. **New context field and helpers.**
   - `Context.checkLCtx : LocalContext := {}`.
   - `monadLift` (79-81) runs `x.run c.env c.safety c.checkLCtx ...` instead of `c.lctx`.
   - `withCheckLCtx l x` replaces the checker view.
   - `withCheckedLocalDecl` opens one fresh id in *both* `lctx` and `checkLCtx`.
   - `withLocalDecl` (83-84) stays main-only.
   - `getType` and all `mkForall`/`mkLambda` (Add-level) keep reading the main `lctx`.
2. **Binder classification.**

   | binder | contexts |
   |---|---|
   | params (116), header indices (127), constructor fields (306), positivity binders (271), `isRecArg` binders (261), `isLargeEliminator` binders (404), recursor index binders (450), `loopCtorArgs` fields (488), `loopUArgs` args (501) | both (`withCheckedLocalDecl`) |
   | major (466), motive (470), induction hypotheses (518, 548), minors (567) | main only |
3. **Snapshots.** `InductiveStats.paramCheckLCtxs : Array LocalContext`: the checker context before
   each parameter (pushed at 116). `paramCheckAll` is the last entry.
4. **Header phase.**
   - `checkClosedType` (101-104) runs under `withCheckLCtx {}`.
   - The closed `whnf type` (142) also runs under `{}`.
   - Cached-parameter branch (121-125): `isDefEq` under `paramCheck[i]`; `whnf` and the recursive
     call under `paramCheck[i+1]`.
   - Each family's index steps start from `paramCheckAll`. Reset explicitly on entering the index
     branch: with `nparams = 0` no snapshot fires.
   - Effect: family d is checked in exactly the context family 0 was.
5. **Constructor phase.**
   - `checkConstructors` runs under `withCheckLCtx paramCheckAll`.
   - Optionally, the per-parameter `isDefEq` (294) runs under `paramCheck[i]`.
   - `isLargeEliminator` runs under `withCheckLCtx {}`, since it reopens every binder itself.
6. **Recursor first pass.**
   - Closed `whnf indTypes[dIdx].type` (462) runs under `{}`.
   - `loopArgs1` parameter steps (448) run under `paramCheck[i+1]`; each family's index chain
     starts from `paramCheckAll`.
   - `loopCtorArgs` runs per constructor under `paramCheckAll`, and `isRecArg dom` (489) under the
     snapshot *before* the field (`dom` does not mention it). Record `fieldCheckLCtxs`.
   - `loopUArgs ui`: replace `inferType ui` (495) by `getType ui`. For a free variable this is the
     same value (`inferFVar` returns `decl.type`, TypeChecker.lean:130; `Recursor/FieldTypeScope.lean`
     already treats it as a lookup). Then run `whnf` under `fieldCheckLCtxs[f]`; args are opened in
     both contexts.
7. **Unchanged.** `checkRecursorType` (739-744) and the equation/nested checks already run in `{}`.

Size: about 80-150 executable lines. Performance: snapshots are persistent values (O(1)), and the
duplicated `mkLocalDecl` is negligible. Benchmark the `Std` replay as for E1.

### 3.2 Proof side

- `ContextWF` / `RecursorContextWF` (Context.lean:349, 468) gain `checkMLCtx`, `checkMLCtx_wf`,
  `checkLctx_eq : checkMLCtx.lctx = c.checkLCtx`, and an `FVLift'` embedding of `checkMLCtx.vlctx`
  into `mlctx.vlctx` with equal declarations.
- **The lifted-run wrappers change in one place.** They are concentrated: about 60 uses across
  `whnfInContext`, `whnfInRecursorContext`, `isDefEqInContext`, `ensureType/ensureSort/checkTypeInContext`
  and `inferTypeFVarInRecursorContext`.
  - Their `VContext` is built from `checkMLCtx`.
  - The old main-context statements become corollaries by weakening (true direction).
  - Each narrow-statement caller must supply a *narrow* input translation. That is the real
    churn. It is the same churn (L) incurs, because the narrow inputs are previous narrow outputs or
    their subterms.
- `Narrow*Scope`, `LaterParameterScope`, `RecursorLaterParameterScope` and the `restrict`/`scopeWF`
  lemmas collapse: the narrow scope *is* the checker `MLCtx`, or a weakening of it.

### 3.3 Fidelity

- The C++ kernel's `add_inductive` keeps one growing `local_ctx` and, to my recollection, creates
  a fresh `type_checker` per call; verify against `src/kernel/inductive.cpp`. Lean4Lean already
  shows each call a smaller context than C++ (scoped `withLocalDecl`); (P) shows a smaller one
  still.
- **Equivalence argument.** In all three, every call consults only `find?` of free variables
  reachable from its inputs and their declarations, plus its own fresh ids (`_kernel_fresh.*`,
  disjoint from `_ind_fresh.*`). So results agree. This is exactly (L), argued and not proved.
  The changes alter no decision procedure; they only change which context is visible. So (P) trades
  the proof of (L) for an executable change whose equivalence is argued.
- Unlike HANDOFF item 8(d) (reusing the header classification), (P) has no observable effect
  under (L), and E1 has already set the precedent for semantics-neutral-in-intent executable
  changes.
- **Empirical check:** a debug flag that runs both `checkLCtx := lctx` and the narrowed variant
  over the replay corpus and compares the resulting environments.

### 3.4 Does (P) avoid (L) completely?

Yes, for `addDecl.WF`. Every narrow scope a site needs is one of:
- a checker context of some run (P makes it literal); or
- obtained from one by weakening or construction: the generator scopes (params + motives + earlier
  minors + fields), `motiveSourceScope`, and `hypothesisContext` all contain a checker scope as an
  `FVLift'` sub-context.

The only needs *smaller* than the producing run's checker context are:
- the field's own binder in `isLargeEliminator`: Sort fix, or hoist the call;
- `isRecArg` inside the field binder: P snapshot.

(L) stays as an optional later theorem "Add(P) = Add(original)". That is outside the
`addDecl.WF` cone.

## 4. Recommendation and ordered plan

**Choose (P) (dual checker context) together with the local fixes. Do not prove (L).**

Under (L) the same narrow-context bookkeeping is required as a ghost structure (2.4), plus a
4-8k-line simulation theorem and per-run upset/agreement proofs. Under (P) the bookkeeping becomes
executable data, and the simulation is replaced by an argued equivalence (3.3) and a differential
test. If Kim rejects executable changes on fidelity grounds, the fallback is (L) with the same plan
order: step 1 changes from "executable plus plumbing" to "ghost narrow contexts plus the (L) theorem".

Trade-offs for Kim:

| | (P), recommended | (L) |
|---|---|---|
| Pros | No new deep theorem. Narrow scopes are WF by construction. Deletes most of the scope plumbing and the false `restrict`/`scopeWF`. | Executable untouched; no fidelity argument needed. |
| Cons | A second executable divergence (after E1), invisible under (L) but only argued; benchmark needed. | About 2x the total work. The success-transfer simulation over all checker code is long and brittle against future checker changes. |

| step | content | files | size |
|---|---|---|---|
| 0 | Local fixes now: Elimination Sort fix; Rhs/Basic lookup; forward `weakBV` lemma; delete false/off-cone lemmas (list in 1.3, `hasTypeOfFullPair` x2, `domainDefEq`, Equation/Motive and Equation/RecursiveCall twins, FirstPass:2762 twin, after a cone recheck) | Header/Elimination.lean, CompletedEquationRhs.lean, Basic.lean, Recursor/CanonicalRecursiveShape.lean, Recursor/{ContextRestriction,Bindings,RecursiveShapeRow,CanonicalConstructorModel,CanonicalConstructorReplay}.lean, Nested/Replacement.lean, Equation/{Motive,RecursiveCall}.lean, Header/LoopType.lean, Constructor/Replay.lean | +150-250 added, 1-3k deleted |
| 1 | Executable (P) changes for all phases (3.1); differential flag | Inductive/Add.lean | 80-150 |
| 2 | `ContextWF`/`RecursorContextWF` dual contexts; narrow lifted-run wrappers with main corollaries; `withCheckedLocalDecl` WF lemmas; snapshot invariants | Verify/Inductive/Context.lean (+ ContextWF users of `withLocalDecl`) | 600-1200 |
| 3 | Header phase onto the family-0 path: Existential:123, LoopInd:141, RawMaterialization:196, LoopType 3781/3857/4040/5258/926/739/788; delete `LaterParameterScope` strengthening and header uses of `NarrowRuntimeScope` | Header/{Existential,LoopInd,LoopType,RawMaterialization,SemanticFold,MaterializedFold}.lean | 800-1500 churn, net negative |
| 4 | Constructor phase under `paramCheckAll`: positivity/normalization narrow facts (`refinesNarrow`, `uniformNormalFormNarrow`), `hasTypeOfFull` callers | Constructor/{Positivity,Normalization,Replay,ExistentialTargets}.lean, Header/SingletonElimination.lean, Recursor/Structure.lean | 500-1000 |
| 5 | Recursor indices: Context:1474, Replay:1752, FirstPass:3230, RecursiveCalls:823, CanonicalMotiveReplay:10, CompletedEquationMotive:1088 | Context.lean, Constructor/Replay.lean, Recursor/{FirstPass,RecursiveCalls,CanonicalMotiveReplay}.lean, CompletedEquationMotive.lean | 800-1500 |
| 6 | Per-field rows: literal narrow rows from `loopUArgs`; forward `weakBV` at `removeBeforeInner`/`recursorTelescope_hypothesisUnlift`; `dropFVarPrefix` → RT; `FVarNarrowCore`/`FVarNarrowScope.restrict` → weakening; `hasTypeOfFullPair` users; `cancelLiftForallDomains` users; `canonicalApplicationContext` consumers; `finalSelectedMinorNarrowFieldAlignment` | Recursor/{SecondPass,FieldTypeScope,Telescope,Origins,CanonicalRecursiveShape}.lean, Equation/{Setup,RecursiveCallScope}.lean, CompletedEquationRecursiveCall.lean, Nested/Replacement.lean | 1500-3000 |
| 7 | Restate `FVLift'.wf`/`BVLift.wf` to take `Delta.WF` (shared with G2 plan step 3); Std replay benchmark; differential replay test | Verify/Typing/Lemmas.lean, Tests | 150-400 |

**Total for (P): about 4.5-9k lines of churn**, a sizeable part of it deletions; the honest lower
bound is about 3.5k. Under (L) the same steps 2-6 apply as ghost contexts, plus 4-8k for the
theorem: about 9-16k.

Risk: steps 2-6 touch the producer proofs (about 35k lines in Header/, Constructor/,
Recursor/{FirstPass,SecondPass,RecursiveCalls,Bindings}). Containment: keep the old main-context
wrapper statements as corollaries, so that only the sites listed above and their narrow-input
threading change.

## 5. The projection-walk corner on E1 (2026-10-07)

The base branch proves the corner from canonical choice (`VEnv.corner_inhabit`, commit c1e4b892;
the Verify-level `projectionWalkCorner_of_choice` is in progress). Its per-call premise is
`StructurePropRecursor env U S info ls`: a registered native recursor `data` whose owner family is
`S` with no indices, whose constructor is `info.ctorName` with `info.nparams` parameters and the
walk's field count, together with universe levels `ls0` (WF, `ls0.length = data.uvars`,
`data.target.inst ls0 = .zero`, `data.levels.map (·.inst ls0) ≈ ls`); temporarily also one family
and one constructor. Plan for E1:

1. Replace the `VContext.projectionCorner : ProjectionWalkCorner` field by `venv.HasCanonicalEq`,
   `venv.HasCanonicalChoice` (hypotheses from the top) and a proved registry fact
   `∀ S info ls, venv.projections S info → ... → StructurePropRecursor venv U S info ls`.
2. The registry fact is not a consequence of `VEnv.Ordered`: the constructor `inductProjections`
   registers projection entries before the block's recursors exist. It is therefore a pipeline
   invariant of `VEnvs.WF` (projection entries, constructors and recursors of a declaration all come
   from the same `CompilationData`, and `NativeRecursorRegistered` is monotone), proved at each
   `addDecl` kind.
3. Transient window. During the recursor phase the context environment is
   `venvCtors.addProjections decl.projectionEntries` (block projections registered, recursors not).
   No user term there contains `.proj S` for a block family `S`: every constructor type was checked
   while the block had no constructors, so `inferProj` on `S` failed there. The only producer is
   `tryEtaStructCore` (via `isDefEq`), which builds `.proj S i t` and may infer its type through
   proof irrelevance. Either an invariant shows that `isDefEq` in this phase never compares a
   constructor application of a block structure with a term it is not syntactically equal to
   (an extension of the `Expr.ProjsOK` invariant of `TypeChecker/HitShape.lean` to block
   structures), or the registry fact is restricted to structures outside the current block and the
   window contexts carry the extended `ProjsOK` invariant. Changing the executable order is not an
   option (the C++ kernel declares the constructors before generating recursors).
