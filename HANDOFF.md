# Inductive verification: status, evidence, and remaining work

Current account, 2026-10-05, branch `agent/verify-inductives`.
This is the single maintained handoff. Update it in place. The source and the
checked theorem types take precedence over this account.

## Intended result

Finish the executable Lean4Lean inductive checker's refinement of an
independent generative specification (Mario's intended treatment of ordinary,
primitive, mutual, higher-order, indexed, and nested inductives), including
dependent projections, structure eta, exact recursor metadata and equations,
with complete proofs. The specification determines artifacts from
declarations; validation must not assume correctness of its own artifact.

## What was established this session (decisive results)

1. **The final theorem and its exact dependencies.** The checker contract is
   `Lean4Lean.addDecl.WF` (`Verify/Environment.lean`): a successful
   `addDecl env (.inductDecl ..)` yields `VEnvs` that are `WF` for the output
   environment, extend the input models, and (through
   `InductiveFinalResult` / `InductiveSpecificationResult`) a `VInductDecl`
   with `TrInductDeclCore` and `VEnv.AddInduct`. An opaque-body dependency
   audit (`scripts/InductiveAudit.lean` mechanism, root `addDecl.WF`) finds
   exactly **10 `sorry` sources**:
   - base metatheory (6): `IsDefEqU.sort_inv`, `forallE_inv_stratified`,
     `sort_forallE_inv`, `rigidApp_inv`, `fieldType_inv_stratified`
     (`Theory/Typing/Injectivity.lean`) and `IsDefEqU.weakN_iff`
     (`Theory/Typing/UniqueTyping.lean`);
   - inductive-specific (4): `VConstructorShape.saturated_of_hasType`
     (`Theory/Typing/RecursorLemmas.lean`),
     `CompletedRecursorConstruction.canonicalConsumedGeneration`
     (`Verify/Inductive/Recursor/CanonicalConstruction.lean`),
     `CompletedRecursorPhasesResult.canonicalCompletedRuleTranslation`
     (`Verify/Inductive/CompletedEquationAssembly.lean`),
     `NestedValidatedRunResult.assemblyNative`
     (`Verify/Inductive/Nested/AssemblyProviderEvidence.lean`).
   `finalValidOfStaged` and the Church-Rosser items (`NormalEq.headParallel`,
   `fullStep`, `FullStep.strip`) are **not** on the path of `addDecl.WF`; they
   matter only to the audit roots `full_church_rosser` and `headParallel`.

2. **The Anchored foundation is disconnected.** None of the 1834
   `Theory/Typing/Anchored*.lean` files (295k lines, all untracked until the
   WIP snapshot) are in the import closure of `Verify.Environment`,
   `FinalDispatch`, `Injectivity`, or the tests. Its targets are the six base
   sorries above; five are open upstream too (`origin/master`, Aug 2026, still
   has `sort_inv`, `forallE_inv`, `weakN_iff`, `TrProj`, `VInductDecl.WF` as
   sorries and several `Experimental/*` attempts), and one is false (next
   item). **Deleted** (with Kim's approval): the 1834 Anchored files, their
   11 sole dependents (`Theory/Typing/{EquationHeaderDerivation,FieldAdequacy,
   NativeDeclaredFieldOrigin,NativeExtensionalTerminal,NativeInitialFieldOccurrences,
   NativeInitialSelection,NativeReplayEligibilitySoundness,NativeResultBridge,
   NativeTerminalSoundness,NativeZeroFieldProgram,TypedWorldProofPrefix}.lean`),
   and two stale unused modules that no longer compiled
   (`Theory/Typing/RigidHeadStrengthening.lean`, `Verify/Typing/ProjectionInverse.lean`).
   Some `docs/inductives/*.lean` witness files import deleted modules and are
   now historical text only. `lake build` (default targets) passes.

3. **`IsDefEqU.weakN_iff` has a mathematical countermodel.** The groupoid
   construction in [STRENGTHENING.md](docs/inductives/STRENGTHENING.md)
   (two singleton-eliminating indexed `Prop` families over a non-discrete
   index type) gives `Γ, q : P v ⊢ SI ≡ SJ` by proof irrelevance while
   separating `SI` and `SJ` in the smaller context. A second opinion (Codex,
   this session) found no defect in the construction but notes the
   certification boundary is open: the checked files establish the
   larger-context derivation and finite transport calculations, not a
   soundness proof for every `VEnv.IsDefEq` rule of a certified `VEnv.WF`
   environment, nor nonderivability of the existential `IsDefEqU`. Scope:
   this refutes unrestricted *equality* reflection; fixed-type typing
   reflection follows the same way; existential `VExpr.WF` strengthening is
   not refuted by it. Adding Lean's `Eq` lets the smaller context extract
   `P v` and so defeats this particular model; no general repair theorem is
   established either way. `weakN_iff` has 63 uses in 24 live files
   (including upstream's `OnCtx.weakN_inv`, `HasType.weakN_iff`,
   `IsType.weakN_iff`, `VLocalDecl.weakN_iff`, `LevelEquiv`,
   `ConditionallyTyped`); it is a base-theory issue shared with upstream.

4. **Two executable regressions were found and fixed** (upstream on the same
   toolchain `v4.33.0-rc2` replays `Init`, `Std`, `Lean.Data`,
   `Lean.Meta.Basic` with no problems except 25/6 "constant has already been
   declared" artifacts shared with this branch):
   - Higher-order recursive fields produced **wrong iota rules**: the
     recursive-call template in `Inductive/Add.lean` (`loopUBlueprints`,
     `mkRecRules.loopU`) placed the recursor placeholder as `.bvar 0` inside
     the field's own lambda binders, where `mkLambda` captured it. `Acc.rec`'s
     rule became `intro x h fun y a => a y (h y a)`; `WellFounded.fixF_eq`
     failed to check and `Lean.Order.iterates.rec` mismatched Lean's.
     Lean's `Expr.abstract` does not shift loose bound variables, so the
     placeholder must be `.bvar xs.size` (now in both sites). Verified by
     regenerating `Acc`, `Lean.Order.iterates`, and a dozen nested inductives
     through `Lean4Lean.addDecl` and comparing recursors (type, metadata,
     rules) against Lean's: identical. The template design is retained
     because first-pass field fvar ids can collide with later minor fvars, so
     a direct construction captures minors (checked: it produced
     `Acc.rec … a y (h y a)`).
   - The nested restoration guard check ran out of fuel: `guardedIotaCheck`
     expands literals (`Nat.succ` chains, string characters) but its fuel was
     `approxDepth + rawBVarBound + 1` with `approxDepth` capped at 255.
     `Lean.Parser.Tactic.MCasesPat` (a `TSyntax` field) was rejected.
     `validateRestoredRecursorRules.guardFuel` now bounds the traversal
     structurally including literal expansion. Note: the guard still walks
     `Nat.succ^n` for a literal `n` in a nested constructor type, which is a
     latent cost problem (a literal of 10^9 would hang); `.lit _ => true`
     plus a freshness premise in `guardedIotaCheck_sound` is the right fix.
   After the fixes, `lean4lean Init` and `lean4lean Std` match upstream's
   baseline exactly. `Std` replay takes ~1m20s here against ~28s upstream:
   a performance regression worth profiling.

5. **The trusted base contained a false implementation axiom.** Both upstream
   and this branch had `axiom Expr.abstract_eq : e.abstract ⟨xs.map .fvar⟩ =
   e.abstractList xs`, where the model `abstract1` **shifts** loose bound
   variables (`bvar i ↦ bvar (i+1)` at or above the cutoff). Lean's real
   `abstract` leaves them unchanged: `(Expr.bvar 0).abstract #[.fvar x]`
   evaluates to `bvar 0` while the model gives `bvar 1` (also false for
   duplicate lists). This is exactly why the recursive-call proofs "verified"
   the buggy executable: the model and the bug agreed. Now:
   - `Verify/Axioms.lean` defines `Expr.abstractN` (one-pass, last occurrence
     wins, loose bvars unshifted; exact mirror of C++ `abstract`), the axiom
     `Expr.abstractN_eq`, and the derived theorem `Expr.abstract_eq_of_closed
     (hnd : xs.Nodup) (h : e.looseBVarRange' = 0)`, plus
     `abstractN_eq_abstractList`, `abstractN_cons`, `abstractN_append_singleton`,
     `abstractN_nil`, `abstractN_hasLooseBVar_zero`, `abstractN_lower`,
     `abstractN_singleton`, `lastRevIdx?` lemmas.
   - The false statement is **gone**: `Expr.abstract_eq_legacy`,
     `abstractN_eq_abstractList_legacy`, and the sequential bridge
     `LocalContext.mkBinding_eq` were deleted (2026-10-05). Every former
     consumer now either runs on the exact model (`mkBinding_eqN`,
     `abstractN` telescopes, `reopenFVarsAt_eq_reopenParams` with a
     `looseBVarRange' = 0` premise, `NestedReplacementReopens.restoreNode`
     stated at arbitrary binder depth) or converts to the sequential model
     through `abstractN_eq_abstractList_of_closed` with an honest closedness
     fact. Closedness is supplied by translations (`TrExprS.closed` plus
     `MLCtx.noBV`), by the kernel's own nested-parameter check
     (`NestedParameterScan.closed`, recorded as
     `GeneratedFamilyWitness.argsClosed`), by `LctxClosed` of semantic
     contexts (`BoundFVarDeclarationAt.closed`), or by new fields/hypotheses:
     `ConstructorRestorationBodyInverse.sourceBVarClosed`,
     `GeneratedRecursorRestorationTelescopeAlignment.oldBVarClosed`,
     `hsourceBVar : Closed source.type` on the constructor restoration chain,
     and `hparamsSize : params.size = nparams` where the honest cancellation
     law needs the parameter count. `--require-complete` no longer reports it.
   - `Verify/LocalContext.lean` keeps two models: the sequential
     `mkBindingList` (now only a specification-side device; its bridge to
     `mkBinding` is `mkBinding_eq'`, which requires `Closed b`, nodup, and
     `DeclsClosed`) and the exact `mkBindingListN` with the true bridge
     `mkBinding_eqN` and the full `cons`/`fold` lemma family. The recursive-call verification
     (`BoundGeneratedRecursiveCall.body/abstractedRecursor/abstractedMajor`,
     `lambdaTelescope`, `appliedFieldLambdaTelescope`,
     `mkLambda_fvars_lambdaTelescopeN`, `mkLambda_fvars_avoidingLambdaTelescopeN`,
     `mkBindingListN_*Telescope`) runs on the exact model and the placeholder
     `.bvar args.size`; the model-internal fingerprints (`replayTrace`,
     `outerAbstracted*`, first-pass `Origins`, equation traces) stay on the
     sequential model and meet the exact model through
     `abstractN_eq_abstractList` with nodup/closedness (e.g.
     `outerAbstractedMotiveApp_eq`, `Equation/Canonical.lean`).
   - Closedness is now a hypothesis of `MLCtx.WF.mkForall_eq/mkLambda_eq`
     (`_he : Closed e`, unused by the sequential proof but required by the
     exact bridge); callers supply it from `TrExprS.closed` with
     `MLCtx.noBV` / `FVarNarrowSources.noBV` / `FVarNarrowCore.noBV`.
     `Closed.instantiate1`, `Closed.consumeTypeAnnotationsVerified`,
     `Closed.consumeForallTypes`, `AvoidsConsts.abstractN`,
     `SameLambdaPrefix.abstractN`, `ForallBinderAt.abstractN`,
     `FVarsIn.abstractN_of` were added.

6. **The source-facing specification needs a hypothesis the executable does
   not check.** Lowering (`ElimNestedInductive.lowerConstructor`, mirroring
   C++ `elim_nested_inductive`) opens the parameter telescope of every source
   constructor type and re-closes it with `mkForall`. Because `instantiate`
   lowers loose bound variables while `abstract` does not shift them, a
   constructor type with a loose bound variable under its parameter binders
   is silently *repaired* (`∀ α, (x : bvar 1) → T α` becomes
   `∀ α, (x : α) → T α`), and the kernel then checks and stores the repaired
   type. So `result.types = sourceTypes` (ordinary case) and "restored
   constructor ≡ source constructor" (nested case) are false for such
   inputs, and the former proofs of them rested on the false bridge. The
   honest statements carry `SourceBVarClosed types` (every inductive type and
   constructor type has no loose bound variables), threaded as
   `HsourcesB` into `ordinary_types_eq_source`,
   `ordinaryFinalSpecificationModelWF`, `inductiveFinalResultWF`, and
   `addInductiveDeclaration.finalResultWF`. The checker contract
   `addDecl.WF` and `finalPreservesWF` are **unconditional**: they go
   through the well-formedness halves (`ordinaryFinalModelWF`,
   `nestedInductiveFinalResultWF.modelExtension`, primitive) only. The
   executable matches the C++ kernel on such inputs (no new rejection); the
   nested path needed no new top-level hypothesis because every source-facing
   fact there comes with a translation of the source.

## Assessment

The inductive verification is **not complete** and cannot be made sorry-free
inside this project's scope without solving open base metatheory:

- Five base sorries are the confluence-class conjectures also open upstream
  (`sort_inv`, `forallE_inv`, `sort_forallE_inv`, `rigidApp_inv`,
  `fieldType_inv_stratified`); `saturated_of_hasType` needs a rigid-head vs
  Pi separation lemma of the same class and is effectively base-layer.
- `weakN_iff` is false and must be replaced; the repair of 63 consumers needs
  a redesign (typing/defeq transport justified by actual inhabitants or a
  context-restricted invariant for the checker's cache), which is upstream
  work as well.
- The three core refinement junctions (`canonicalConsumedGeneration`,
  `canonicalCompletedRuleTranslation`, `assemblyNative`) are each a
  `Nonempty` of a large certificate structure assembling thousands of lines of
  component lemmas written against the formerly false model. Their
  components must be re-audited now that the template chain runs on the exact
  model; the executable they describe is now validated empirically against
  Lean's own recursors, which was not true before.
- The honest reachable target is: executable validated against Lean on large
  corpora; inductive-specific obligations closed; final theorem conditional
  only on the named base conjectures; no false statement in the trusted base.
  Of these, the first and the last are done, and the middle two remain open.

## Remaining obstacles, in priority order

1. **Done: `Expr.abstract_eq_legacy` removed** (item 5/6 above). Residual
   risk: the new `SourceBVarClosed` hypothesis on the specification-facing
   theorems is not discharged by the executable; decide with Mario whether
   the kernel's silent repair of loose bound variables in source constructor
   types should be rejected instead (a one-line `hasLooseBVars` check in
   `checkInductiveSources`, which would be a divergence from C++ on
   malformed input and would let `SourceSyntaxChecks` carry the fact).
2. **Close the three refinement junctions** (see above). Assessment after
   the bridge removal (2026-10-05): the junction structures are unchanged
   and nothing in them depended on the deleted statement, so their component
   lemmas are now honest. For `canonicalConsumedGeneration`
   (`Recursor/CanonicalConstruction.lean`): take `signature :=
   R.sourceSignature` (`CompletedSourceSignature.lean` already proves
   `sourceSignature_models`, field types, constructor names/owners, replay),
   `generation` from `elimLevel`/`recursorDeclarationAbstractLevels`;
   `params`/`motives` are covered by `sourceParameterTranslation` and
   `generatedParametersMotivesTranslation`; `consumedMotive`,
   `consumedMotiveDomains`, `majorBinderSource` cover the owner's indices
   and major. **Missing**: no theorem mentions
   `declareRecursors.recursorType`; the minors telescope has no translation
   to `Instance.minors` (each minor must be matched with `Instance.minor`
   through `RecInfoMinorSemanticSource` and the `Equation/MinorAlignment`
   field/hypothesis splits), and `sourceOrigins` must be assembled from
   `origins`/`minorSources`. `canonicalCompletedRuleTranslation` then needs
   `CompilationRealization` (`Recursor/Realization.lean`): the equation
   build (`existsCanonicalGeneratedEquationBuild`) supplies the rule list,
   so what remains is `RecursorEntryRealization` per owner (metadata fields
   and `RuleRealization` of each concrete rule against `Instance.equation`).
   `assemblyNative` needs the restored analogue
   (`RestoredCompilationRealization`) plus `InductiveRecursorProvenance` on
   top of `assemblyShapeNative`. Use the recursor-comparison scratch
   (regenerating `Acc`, `iterates`, nested types through `Lean4Lean.addDecl`)
   as the executable oracle.
3. **Replace `weakN_iff` and repair consumers**; coordinate with upstream.
4. **Executable hygiene**: literal cost in `guardedIotaCheck`, the `Std`
   replay slowdown, and a review of every runtime rejection added in
   `Inductive/Add.lean` (grep `throw <| .other` in the diff against
   `origin/master`) against Lean-accepted declarations beyond `Init`/`Std`.
5. **Audit discipline.** `scripts/check-inductive-audit.py` roots
   `full_church_rosser`, `headParallel`, and `NormalEq.fullStep` are outside
   the `addDecl.WF` cone; decide whether they remain goals.
6. **Tests.** `Tests/InductiveTheory.lean` was repaired (the enum `Models`
   instance gained the ninth field `constructorArity`).
   `Tests/RecursorOracle.lean` regenerates `Acc`, `Lean.Order.iterates`,
   `Nat`, `List`, `Prod`, several nested inductives, a `TSyntax`-field nested
   type and a multi-binder higher-order predicate through `Lean4Lean.addDecl`
   and compares every recursor (type, metadata, rule RHSs) with Lean's, and
   pins `Expr.abstract`'s behaviour on loose bvars. Still missing: a test
   exercising the first-pass/minor fvar-id collision directly, and a
   large-literal guard test.

## Source map

| Question | Entry points |
| --- | --- |
| Final contract | [Verify/Environment.lean](Lean4Lean/Verify/Environment.lean) (`addDecl.WF`), [Run/FinalResult](Lean4Lean/Verify/Inductive/Run/FinalResult.lean), [Run/SemanticSpecification](Lean4Lean/Verify/Inductive/Run/SemanticSpecification.lean) |
| Generative specification | [Theory/Inductive.lean](Lean4Lean/Theory/Inductive.lean) (`VInductDecl.WF`), [Theory/Inductive/](Lean4Lean/Theory/Inductive/) |
| Base open lemmas | [Injectivity](Lean4Lean/Theory/Typing/Injectivity.lean), [UniqueTyping](Lean4Lean/Theory/Typing/UniqueTyping.lean), [RecursorLemmas](Lean4Lean/Theory/Typing/RecursorLemmas.lean) |
| Abstraction models and axioms | [Verify/Axioms.lean](Lean4Lean/Verify/Axioms.lean), [Verify/LocalContext.lean](Lean4Lean/Verify/LocalContext.lean) |
| Recursive-call verification (exact model) | [Recursor/RecursiveCalls.lean](Lean4Lean/Verify/Inductive/Recursor/RecursiveCalls.lean), [Recursor/Rules.lean](Lean4Lean/Verify/Inductive/Recursor/Rules.lean), [Recursor/SecondPass.lean](Lean4Lean/Verify/Inductive/Recursor/SecondPass.lean) |
| Executable recursor construction | [Inductive/Add.lean](Lean4Lean/Inductive/Add.lean) (`loopUBlueprints`, `RecCallBlueprint.build`, `validateRestoredRecursorRules`) |
| Strengthening countermodel | [STRENGTHENING.md](docs/inductives/STRENGTHENING.md) |

## Evidence and commands

- Dependency audit of `addDecl.WF`: now a permanent root of
  `scripts/InductiveAudit.lean`; result listed above (exactly the 10 sorries
  of item 1; `abstract_eq_legacy` is gone; axioms are the inventory's
  implementation axioms including `abstractN_eq`).
- Executable oracle: regenerate an inductive through `Lean4Lean.addDecl` on a
  renamed copy and compare `RecursorVal`s with Lean's; `lake env
  .lake/build/bin/lean4lean Init` (25 "already declared" artifacts, same as
  upstream), `… Std` (6, same as upstream), `--fresh Init.Prelude`,
  `--fresh Init.Core`.
- `lake build` (default targets), `lake build Lean4Lean.Tests`, the fresh
  `Init.Prelude` (1975 declarations) and `Init.Core` (3953 declarations)
  replays, and `python3 scripts/check-inductive-audit.py --self-test` all
  pass at this state (2026-10-05, after removing the false bridge);
  `--require-complete` fails only on the 10 reachable open obligations of
  item 1 (plus the Church-Rosser roots outside the `addDecl.WF` cone).

Final acceptance still requires: `lake build`, `lake build Lean4Lean.Tests`,
fresh `Init.Prelude` and `Init.Core` replay,
`python3 scripts/check-inductive-audit.py --self-test` and `--require-complete`,
and a review of the final theorem hypotheses. Preserve the toolchain
`leanprover/lean4:v4.33.0-rc2`; add no axioms; do not hide proofs behind
supplied semantic answers; do not add runtime rejections to ease proofs.
