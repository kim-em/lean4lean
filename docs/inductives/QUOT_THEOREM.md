# Quotient initialization in the top-level theorem

Branch `agent/verify-inductives-quot` (2026-10-08).

## Statement

`Lean4Lean/Verify/QuotInit.lean`:

```lean
theorem addQuot.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (hq : ∀ safety, (ves.venv safety).QuotReady) :
    (Environment.addQuot env).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety
```

`addDecl.WF` gains the hypothesis `hq` and closes its `quotDecl` case with
`addQuot.WF`.  `addDecl.WF_of_canonicalEq` keeps its statement; it discharges
`hq` from its canonical-equality hypothesis (`VEnv.HasCanonicalEq.quotReady`),
which was previously unused.  `Declaration.IsModelled` is now `True` for every
declaration.  The hypothesis `hdecl` stays in the top-level statements because
GOAL.md fixes them, but it is trivially satisfiable (`trivial`, see
`Lean4Lean/Tests/QuotInit.lean`).

## Why `QuotReady` at every safety level

The abstract rule `VDecl.WF.quot` requires `env.QuotReady` (the abstract `Eq`
with its canonical type) and the quotient constants are safe, so every
safety-indexed model (`TrEnv'.quot`) must type `Quot.lift`, whose type mentions
`Eq`, at every safety level.  The executable's `checkEqType` checks the shape of
`Eq` and `Eq.refl` but not their safety: an environment whose `Eq` is an
*unsafe* inductive with the right shape passes `checkEqType`, and its safe model
has no `Eq` at all, so `Quot.lift` has no translation there.  The previous
groundwork `checkEqType.WF` only gave `QuotReady` at the unsafe level.  Hence
`addQuot.WF` takes `QuotReady` at every level as a hypothesis, and the top level
supplies it from `HasCanonicalEq` (which the replay of `Init.Prelude` realizes,
`addDecl.eqBootstrapHasCanonicalEq`).  No correction of the Theory rule or of
`VEnvs.WF` was needed, and the executable is unchanged.

## Proof outline

* `Environment.addQuot_eq`: on an environment with `quotInit = false`, the
  executable is `checkEqType`, four `checkName`s, and the installation of four
  `quotInfo` constants with explicit closed types `QuotInit.tQuotC`, `tMkC`,
  `tLiftC`, `tIndC`.  The `withLocalDecl`/`mkForall` computation is replayed
  literally (free variables `_uniq.1`, `_uniq.2`, ... from the default name
  generator) and evaluated with `mkBinding_eq'`/`mkBindingList_eq_fold`, since
  the hashed local-context maps do not reduce by `rfl`.
* `TrExprS.ofPlainTr`: for the fragment of bound variables, sorts, constants,
  applications and foralls, a well-typed syntactic translation (`plainTr`) is a
  `TrExprS` translation.  The closed types translate (`rfl`) to `quotConst`,
  `quotMkConst`, `quotLiftConst`, `quotIndConst`.
* `AddQuot.exists`: any ordered `QuotReady` model without the four names extends
  to an `AddQuot` (the Verify alignment of `VEnv.addQuot`).
* `VEnvs.WF.addQuot`: assembles the new `VEnvs` (`TrEnv'.quot` at every level),
  carrying the constant-map invariants through the four insertions
  (`QuotEnvInv.add`) and across `markQuotInit` (`QuotEnvInv.markQuotInit`).

## Deleted

From `Lean4Lean/Verify/Environment.lean`: `checkEqType.WF` and
`expectedEqType_translation` (superseded by the hypothesis above),
`addDecl.WFCanonicalEq`, `addDecl.WFCanonicalEq_of_canonicalEq`,
`VEnvs.HasCanonicalEq.canonicalEqEnvs`,
`addInductiveDeclaration.preservesWF` and
`addInductiveDeclaration.checkedLoweringClosedWF` (no users).  Kept:
`VEnvs.HasCanonicalEq` and `.mono`, used by the iterable replay statement
`addDecl.WFHasCanonicalEq`.

Eq-bootstrap plumbing with no users (checked by computing the dependency cone
of `addDecl.WFHasCanonicalEq`, `addDecl.eqBootstrapHasCanonicalEq`,
`VEnvs.WF.canonicalEq_constants` and the definitions `Tests/CanonicalEq.lean`
reads, plus every reference from modules outside this task):

* `Verify/Inductive/PrimitiveFinalDispatch.lean` (all three
  `primitiveFinalEnvironmentEqReadyOrAbsentWF` theorems), with its import in
  `Verify/Inductive.lean`;
* from `Verify/Inductive/PrimitiveFinalEnvironment.lean`:
  `CompletedBlockCertificate.eqCanonicalOfBase`,
  `.preservesEqAbsentPrimitive`, `.extendSafePrimitiveEqReadyOrAbsent`,
  `GeneratedRecursors.entryNamesNeEq`,
  `SemanticPrimitiveRunWithStatsResult.extendSafeEqReadyOrAbsent`,
  `VerifiedSemanticPrimitiveInductiveRunResultSourceAligned.extendSafeEqReadyOrAbsent`,
  `AddInductive.run.primitiveFinalEnvironmentEqReadyOrAbsentWF`;
* from `Verify/Inductive/EqCanonicalForms.lean`: the iota-rule translation
  lemmas `eqRecRule{Lhs,Rhs,Type}Expr_syn` and
  `TrExprS.eq_canonicalEqRecRule{Lhs,Rhs,Type}` (the realizability proof gets
  the rule clause from `InductiveSignature.Compiles.eqRecRules`; the test checks
  the rule expressions directly).

Kept although outside the cone: `CanonicalEqEnvs` and `EqReadyOrAbsent`
(`Run/EqCanonical.lean`) and the `CanonicalEqTyping` lemmas, which modules
outside this task still reference; `AddInductive.run.primitiveFinalEnvironmentModelWF`
(not Eq plumbing); `addInductiveDeclaration.finalResultWF` (the source-facing
specification).

The Eq-bootstrap realizability chain (`addDecl.eqBootstrapHasCanonicalEq`,
`VEnvs.WF.canonicalEq_constants`, `Tests/CanonicalEq.lean` and their cone) is
kept: it is what makes the `HasCanonicalEq` hypothesis honest, and the
quotient case now uses that hypothesis.

## Observation

Lean4Lean's `addQuot` makes the `q` binder of `Quot.ind` implicit where Lean's
kernel makes it default.  Binder info is irrelevant to typing and the
executable is not changed; `Tests/QuotInit.lean` compares with the kernel up to
binder info.
