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

7. **Translations are syntactically unique, and the junction must invert the
   executable's type check.** `TrProj` has one constructor, so
   `TrExprS.uniqueS` (`Recursor/CanonicalMinorFields.lean`) gives
   `TrExprS Δ e e₁ → TrExprS Δ e e₂ → e₁ = e₂` with no `IsUnique` side
   condition; every "which translation was chosen" question in the junction
   disappears. The minor premises mention motives, and the first pass only
   translates them in free-variable contexts that interleave indices, majors
   and stale fields between the parameters and the motives; moving such a
   translation into the generator's abstract context `params ++ motives ++
   earlier minors` would need context strengthening, which is the `weakN_iff`
   problem. The only derivation of a closed recursor type available before
   installation is the executable's own `checkRecursorTypes`, so
   `CompletedRecursorConstruction` now retains it (`recursorTypes :
   RecursorTypeTranslations …`; `bindingSemanticWFOfTargets` lets the
   installed targets depend on it). `Recursor/CanonicalRecursorTelescope.lean`
   inverts it into the five binder groups (`recursorTelescope`) and identifies
   the parameter group with the cached parameter telescope and the motive group
   with `Instance.motives` by uniqueness (`recursorTelescope_params`,
   `recursorTelescope_motives`). Each flat minor slot translates the retained
   minor declaration type in its generator context
   (`recursorTelescope_minor`); its field domains are the `insertBinders`
   lift of `H.sourceFields` (`recursorTelescope_minorFields`, by uniqueness
   against `minorFieldsTemplate`); and its residual inverts to the owner's
   motive variable applied to translations of the closed terminal indices and
   to the canonical constructor spine `mkApps (const ctor levels) (vars …)`
   (`minorResidualSource`, `recursorTelescope_minorResidual`); its index
   translations are the lifted `sourceConstructorIndices`
   (`recursorTelescope_minorIndices`: lift the header replay with
   `liftOriginalType`, peel the field telescope, weaken with
   `insertBeforeInner` and `bvLift`, then `uniqueS`); and each hypothesis
   domain translates the retained hypothesis declaration in its generator
   context (`recursorTelescope_hypothesisSlot`) and inverts to a telescope of
   argument domains, the owner's motive variable applied to translations of
   the closed exposed indices, and the recursive field variable applied to
   the canonical argument spine (`hypothesisResidualSource`,
   `recursorTelescope_hypothesisShape`, from the blueprint hypothesis origins
   `RecInfoMinorHypothesisTypeOrigin`). The owner's index and major groups
   are the lifted motive telescope (`recursorTelescope_indicesMajor`), and
   `recursorTarget_eq_of_minors` assembles everything: the checked recursor
   type equals `Instance.recursorType` for any generator instance over the
   consumed families whose minor list equals `T.minors`. So the `types` field
   of the junction is reduced exactly to the minor group, and the minor group
   to item 8: the hypothesis argument domains and exposed indices must be the
   lifts of small-context `Recursive` shapes for `Instance.hypothesis` to
   match. Translation strengthening is available for this:
   `Recursor/ContextRestriction.lean` restricts a lambda-only typechecker
   context to any up-set of its free variables (`MLCtx.restrictUpSetCtx`:
   the result is a well-formed `MLCtx` whose declarations carry the
   strengthened translations, with the `FVLift'` witness; uses
   `TrExprS.weakFV'_inv`, which **does** depend on the false `weakN_iff`
   through `VExpr.WF.weak'_iff` and `HasType.weak'_iff` at
   `Verify/Typing/Lemmas.lean:1316-1354`; an earlier version of this note
   claimed otherwise) and closes such a context into abstract binders
   (`TrExprS.closeAllLams`). The
   remaining program for the minors, independent of item 8's resolution:
   for hypothesis `j` take the semantic call row
   (`RecInfoHypothesisCallSemanticOrigins` → `SemanticBoundGeneratedRecursiveCall`,
   with `current_scope_up : IsFVarUpSet (args ∨ fields ∨ params)`), sharpen
   the up-set to `params ∪ fields.take f ∪ args` (field dependencies lie in
   earlier fields by `VLCtx.WF` plus `fieldParameterUp`; argument scope by
   induction over `RecursorLoopUArgsPrefix` with `whnf.WF`'s `FVarsBelow`),
   restrict the row's context, read the `Recursive` binders off
   `MLCtxForallDomains` of the restricted context and the indices off the
   restricted `exposed_translation`, close with `closeAllLams`, weaken into
   the generator's hypothesis context with `insertBeforeInner`/`bvLift`, and
   identify with `recursorTelescope_hypothesisShape` by `uniqueS` (the two
   passes' telescopes are related through `replayTrace_eq_blueprint`). With
   item 8 resolved by (c), only `Instance.RecursiveTypesWF` for the actual
   instance then remains, by inversion of the retained type check.
   **Done (2026-10-06): per-field rows and the inversion tools.** The
   first-pass producer now retains, from the same executable run, a second
   semantic row per induction hypothesis whose root scope is
   `RecursorFieldPrefixScope`: the parameters and the constructor fields
   strictly before the recursive field (`RecInfoHypothesisCallSemanticOriginsAt`,
   stored as the last conjunct of `RecInfoRuleBlueprintSemanticOriginAt`,
   `SecondPass.lean`; the coarse row is unchanged for the equation layer).
   The field's own declared type is scoped by reading the stored metacontext
   declaration (`Recursor/FieldTypeScope.lean`: the executable's
   `inferType (.fvar fv)` is a local-context lookup, and an all-lambda
   `MLCtx` records the dependencies of a declared type on its own entry;
   `MLCtx.recentTypeScope`, `RecursorRecentBoundFVarArray.fieldTypeScope`),
   so `resultRecursiveDomainOfInferredScope`/`inductionHypothesisTypeOriginOfInferredScope`
   take the inferred type's scope as a hypothesis (the original forms are
   wrappers). The sharpened up-set is `IsFVarUpSet.sharpenPrefix`.
   `recursorTelescope_hypothesisDomains` extends the hypothesis-shape
   inversion with the translation of each binder domain `A[i]` (of the
   literal `i`-th domain of the blueprint telescope, `argDomains`).
   `Recursor/TelescopeUniqueness.lean` closes an all-lambda metacontext entry
   by entry (`MLCtx.lamTypes_telescope`, `lamTypes_find?`), identifies two
   abstract telescopes translating the same sources
   (`TrExprS.telescope_unique`), and pins the universe un-shift
   (`TrExprS.chooseOriginalUniverses_eq`, from `SourceUniverses.lean`'s
   `chooseOriginalUniverses`). `MLCtx.restrictUpSetCtx` now also preserves
   declaration types. Remaining for the minor group: restrict the per-field
   row (`SemanticBoundGeneratedRecursiveCall.restrictToFieldPrefix`,
   `Recursor/RecursiveShapeRow.lean`, in progress), identify its parameter
   and field domains with `parameterDecls` and `sourceFields` by
   `telescope_unique`, weaken the restricted translations into the generator
   context (`insertBeforeInner`) and identify with
   `recursorTelescope_hypothesisDomains`/`_hypothesisShape` by `uniqueS`
   (`replayTrace_eq_blueprint` relates the row to the blueprint origin), then
   un-shift universes and assemble the consumed signature.
   **Universe un-shift (open, 2026-10-06).** The shapes read off the row are
   translations in the recursor universe list `u :: c.lparams` (large
   elimination); the signature needs them in `c.lparams`, with
   `instL (recursorDeclarationAbstractLevels …)` reproducing the checked
   domains. `TrExprS.chooseOriginalUniverses_eq` does this given that the
   source Expr does not mention `u`. The arg domains and exposed indices are
   `whnf` outputs of the field types, which never mention `u`, but the
   checker proves no universe-parameter support for `whnf` (only
   `unfoldDefinition.WF_levelParams` existed; the index telescopes were then
   covered by a runtime check `checkIndexUniverses`, since removed, see
   below). A runtime guard for the argument telescopes is excluded by the
   no-new-rejections rule. Plan (study 2026-10-06, estimate 1.5k to 2.2k
   lines over 7 to 10 files of `Verify/TypeChecker`): add to `VState.WF` and
   `Methods.WF` a hereditary universe-support invariant (results of
   `whnfCore`/`whnf`/`inferType` mention only `Us` when the input and the
   declarations of an up-set containing its free variables do; `isDefEq` only
   threads the state invariant), prove it per method, and bridge to
   `loopUArgs` with the per-field up-set. This also allows removing
   `checkIndexUniverses`. **Done (2026-10-06, merged):** `VContext.UniverseScope`,
   `VContext.LevelsBelow`, `LevelsCache.WF` and the `VState.WF` fields
   `inferTypeI_levels`/`inferTypeC_levels`/`whnfCore_levels`/`whnf_levels`,
   with `Methods.WF` fields `whnfCore_levels`/`whnf_levels`/`inferType_levels`,
   proved for every method (`Verify/TypeChecker/{Basic,Reduce,Recursor,WHNF,
   Projection,InferType}.lean`, `Verify/ExprUniverses.lean`); no pending
   lemmas. The bridge to the recursor pass (`ArgumentUniverses`, the
   hypothesis of `consumedGeneration_of`) is in progress
   (`Recursor/ArgumentUniverses.lean`). **`checkIndexUniverses` removed
   (2026-10-06):** `loopInd1` no longer checks that the index telescope
   mentions only the declaration's universe parameters, matching C++. The
   fact is proved instead: `continueRecursorParameterSemantics` and
   `continueRecursorIndexSynthesisSemantics` (`Recursor/FirstPass.lean`)
   carry `type.levelParamsIn base.lparams` and a universe scope for the narrow
   scope through every `whnf`/`withLocalDecl` step (`whnfInRecursorContext.levelsWF`,
   `UniverseScope.cons`), seeded by the header translation and by
   `ParameterUniverseSupport` (now a hypothesis of
   `mkRecInfos.loopInd1.resultSemantics`), and
   `RecursorRecentBoundFVarArray.indexUniverses` closes the telescope; this
   discharges the `indexUniverses` field of the origin rows. The universe-scope
   lemmas the first pass needs moved from `Recursor/LoopUniverses.lean` to
   `Recursor/UniverseScope.lean`.
   **Assembly (2026-10-06).** `consumedGeneration_of H HU HF : Nonempty
   H.ConsumedGeneration` (`Recursor/ConsumedGenerationAssembly.lean`,
   `CanonicalConstruction.lean`) is proved from `recursorTelescope_hypothesisUnlift`
   (`Recursor/CanonicalRecursiveShape.lean`: each hypothesis binder group is the
   `underFields` lift of small-context translations of explicit blueprint
   sources), the universe un-shift (`TrExprS.unshiftFixed`), `ConsumedModels.lean`
   (`ConsumedSignatureData.models_of_familyTypes`), `ConsumedAdmissible.lean`
   (`consumedInstance_admissible`, with `sourceConstructorIndices_eq_header`),
   `recursorTarget_eq_of_minors`, and `recursiveTypesWF_of_recursorType`.
   `ConsumedGeneration` gained `recursiveTypesWF` and `familyTypesWF`.
   **Closed (2026-10-06):** `canonicalConsumedGeneration :=
   H.consumedGeneration_of H.argumentUniverses`, no remaining hypotheses. The
   per-field semantic rows retain universe support of each call's argument
   telescope and exposed indices (`RecInfoCallBlueprintSemanticOrigin.universes`,
   proved at the producer from the checker's invariant, `Recursor/LoopUniverses.lean`;
   the parameter and constructor-tail support is discharged at the two
   `loopInd2.resultSemantics` call sites, `Run/Formation.lean` and
   `CompletedConstructorReplay.lean`), and `ArgumentUniverses` is stated over
   the producer-retained blueprint calls (an earlier form quantified over
   arbitrary origins and was false). Reachable sorries after this step: the
   ten base obligations of item 1, `canonicalCompletedRuleTranslation`
   (`CompletedEquationAssembly.lean:278`), `assemblyNative`
   (`Nested/AssemblyProviderEvidence.lean:5049`) and
   `RestoredNestedDeclarationsResult.finalValidOfStaged`
   (`Nested/ValidationEnvironmentRegistry.lean:935`).
   Correction of an earlier plan: the junction
   signature cannot be `R.sourceSignature`. Its field types translate the raw
   constructor telescope, while the production minors bind their fields with
   `consumeTypeAnnotationsVerified` domains, and
   `ConsumedGeneration.sourceOrigins` requires `fieldTypes = H.sourceFields`
   (consumed, header universe). The junction signature is a consumed
   signature whose `Models` follows from `sourceSignature_models` through the
   definitional equalities already proved (`sourceConstructorDefEq`).

8. **The recursive-field clause of the specification was restated at the
   instance level (decision taken with Kim, 2026-10-05).** `Models` no longer
   carries `recursiveTypes`; instead `Instance.RecursiveTypesWF g envTypes`
   (`Theory/Inductive/Signature.lean`) demands, for every recursive field,
   the definitional equality of the field type with its `Recursive` shape in
   `Instance.hypothesisContext` (`SignatureData.lean`: parameters, motives,
   earlier minors, all fields, earlier hypotheses), lifted exactly as
   `Instance.hypothesis` lifts the shape. It is required next to
   `Admissible` in `Compiles`, `CompilationRealization`, and (for the nested
   path) `CompilationData.recursiveTypesWF`. Rationale: `InductiveSignature`
   and `Models` are this branch's formalization (upstream has `VInductDecl.WF :=
   sorry`), the generator needs the equality only in that context, and the
   former small-context form (parameters and earlier fields only) was an
   over-specification: production classifies recursive arguments in the
   recursor-construction context and definitional equality does not
   strengthen (next paragraph). The former form implies the new one by
   weakening and universe instantiation; this implication is not yet
   recorded as a lemma. Mario should review the clause with the rest of the
   signature specification. The paragraph below records the obstruction that
   motivated the change.

   **Correction (2026-10-06, decided with Kim after second opinions from an
   Opus agent and from the Astra model through Codex).** The claim that the
   instance-level definitional-equality clause "follows from the retained
   type check by inversion" was wrong: inversion of `IsType [] recursorType`
   yields typing facts only in the context extended by the hypothesis
   binders, and moving a definitional equality with lifted endpoints down to
   `hypothesisContext` is exactly the strengthening that
   `docs/inductives/STRENGTHENING.md` refutes; the first-pass facts need the
   same strengthening from the large stale context; reduction traces are not
   retained by `whnf.WF` and the theory's reduction relations are typed, so a
   trace route would be a new foundation. The clause is therefore restated as
   well-formedness of each generated induction hypothesis in its own context,
   `Instance.RecursiveTypesWF g env := ∀ index j hj, env.IsType g.uvars
   (g.hypothesisContext …) (g.hypothesis …)`, required in `Compiles` and
   `CompilationRealization` at the environment in which the recursors are
   declared (family headers, constructors, and the declaration's projection
   entries, which is `R.context.venv`), since binder peeling keeps the
   environment; it is derived from `IsType [] (g.recursorType owner)` by
   `Theory/Inductive/HypothesisTyping.lean` without new sorries. Planned
   follow-up (option (C)): a small-scope positivity clause in `Models`,
   existential over a source-free telescope and indices with the same target,
   from the header-phase evidence (the old small-context clause existentially);
   its evidence (`uniformNormalFormNarrow` via `restrictTrExpr`) also rests on
   the `weakN_iff` admission, so it is a specification improvement, not a
   repair of strengthening. Both opinions noted that the defeq form in
   `hypothesisContext` would not have pinned the shape well either, because
   later fields in that context may be proofs.

   **Second correction (2026-10-06, decided with Kim after a second Astra
   opinion).** `Models.externalFields` and `Models.recursiveDomains` required,
   for the consumed signature, agreement between the header phase's field
   classification (`checkPositivity`, which records nothing executably) and
   the recursor pass's (`isRecArg`): a field the generator calls external must
   be external for the header too, and the generator's binders must be
   syntactically source-free although the recursor pass never checks binder
   source-freedom. No lemma gives this agreement (it needs `whnf`
   alpha/context locality plus a syntactically retained header telescope, or
   new confluence-class admissions, and confluence alone cannot yield
   syntactic source-freedom). Both clauses are replaced by one
   classification-independent clause `Models.positiveFields`: every field
   type, in its own scope, is definitionally a
   `VInductDecl.UniformFieldNormalForm` at the source universes (source-free,
   or a telescope over source-free domains ending in a fully applied family),
   which is exactly the header evidence (`SignatureFieldModel` now carries
   it). The generator's classification and shapes are constrained only by
   `RecursiveTypesWF`; their fidelity to the C++ classification is validated
   by the recursor oracle tests, not by the specification. Astra's caveat for
   Mario: a future soundness proof for the permitted recursive presentations
   must justify the generated recursive calls (descent along the positive
   constructor structure), which the specification alone does not establish.

   **Third correction (2026-10-06, decided with Kim after an Astra opinion).**
   `Models.families` required each family's signature type `∀ params indices,
   Sort l` to be definitionally the declared type in the source environment.
   For the consumed families (whose indices must be the recursor pass's, since
   the generated motive types are built from them syntactically) this is the
   same obstruction once more: the recursor pass computes the index telescope
   by `whnf` in a context interleaving earlier families' indices, majors and
   motives, and the header phase records its telescope only existentially.
   Decision: drop the definitional conjunct from `Models.families` and add
   `InductiveSignature.FamilyTypesWF` beside `RecursiveTypesWF` in `Compiles`
   (recursor-declaration environment): the parameter-and-index telescope is a
   well-formed context and each family applied to it has type
   `Sort resultLevel`. Derivable for the consumed families from
   `sourceIndexDomains` and `sourceIndices_motive` without strengthening. Lost:
   exact agreement of each index domain with the declared one in its own
   prefix (domains that become equal only under a later binder). The nested
   restoration correspondence (`RestoresFamily.type`) and the K-like
   alignment (`kOfRealization`) consumed the definitional form and are
   rederived from source formation evidence; the restoration clause is
   weakened to "the source header is some telescope ending in the recorded
   sort". Pattern behind all three corrections: a clause tying a telescope
   computed by the recursor pass's `whnf` definitionally to header data in a
   clean context is not provable with the current foundations; provable are
   header-phase facts about the declared data in their own scope and
   well-formedness of the generated types in the recursor-declaration
   environment. Work on branch `agent/family-types` in a separate worktree.

   **Former statement of the risk.** `Compiles` (`Recursor/Realization.lean`,
   `CompilationRealization.generated`) requires `s.Models env decl` for the
   signature whose recursors and equations are installed, and
   `Models.recursiveTypes` asks, for every recursive field, a definitional
   equality `type ≡ s.recursiveType i r` in the *small* context
   `fieldTypes.take i ++ params`. The generator's hypothesis domains are
   `Instance.hypothesis`, built from `r.binders`/`r.indices`, so for the
   installed minor types to be syntactically the generator's output these
   shapes must be the translations of production's `loopUArgs` telescope
   (`RecInfoMinorHypothesisTypeOrigin.args`, `exposedType`). Production
   classifies recursive arguments in the big first-pass context
   (`RecursorRecursiveDomainAt.ctx := R'.mlctx.vlctx.toCtx`, Bindings.lean),
   which interleaves indices, majors, motives, earlier minors and stale fields;
   the raw signature's shapes (`signatureFieldOfUniform`, header phase) are
   only definitionally related normal forms, in the small context. Moving the
   production shapes to the small context is fine for translations
   (`TrExprS.weakFV'_inv` drops any unused free-variable declarations whose
   dependents are kept, and does not use `weakN_iff`), but the required
   *definitional equality* in the small context is exactly context
   strengthening, which `docs/inductives/STRENGTHENING.md` shows false in
   general. `Models.recursiveTypes` has no consumer in the theory besides
   `Models.mono` (grep 2026-10-05). Resolutions, to decide with Mario:
   (a) prove `TypeChecker.whnf` deterministic modulo free-variable renaming
   and context/environment extension, so the recursor-pass telescope equals
   the header-phase one and the raw `Models` transports; (b) have the type
   checker's `whnf` soundness also return an untyped head-reduction trace
   (`FullWHRedS`, whose `weak'_inv` strengthening exists in
   `Theory/Typing/FullHeadStrengthening.lean`) and strengthen the trace;
   (c) restate `Models.recursiveTypes` in the generator's own hypothesis
   context, where the checked recursor type supplies the typing by
   inversion (chosen; see above); (d) change the executable to reuse the
   header-phase classification (rejected: unnecessary divergence from the C++
   kernel). Cost check for (a) (2026-10-05): `Verify/TypeChecker/
   AlphaLocality.lean` already has the renaming framework
   (`ExprAlphaUnder`, `Context.OrderedBinderRenaming`) and locality of
   `whnf` only for the forall, immediate and free-variable-head cases
   (`whnf_forall_alpha`, `whnf_immediate_alpha`, `whnfFVarAt_alpha`);
   `RecursorFieldDecisions.alphaAlignment` (`ReplayCompat.lean`) is
   parametrised by an undischarged classifier-locality hypothesis and has no
   callers. The header phase's recursive normal form is definitional
   (`checkPositivity.loop.uniformNormalFormNarrow` yields `∃ normalized,
   IsDefEqU …`), not the translation of a retained telescope, so (a) also
   needs the header phase to retain its `whnf` telescope syntactically. Until
   one option is chosen, `canonicalConsumedGeneration` cannot be closed,
   independently of the uniqueness and inversion machinery of item 7. With
   (c) chosen, what remains for `canonicalConsumedGeneration` is the item 7
   program (define the shapes by translation strengthening, identify the
   minor group) plus `RecursiveTypesWF` for the actual instance, which
   follows from the retained type check by inversion.

## Assessment

The inductive verification is **not complete** and cannot be made sorry-free
inside this project's scope without solving open base metatheory:

- Five base sorries are the confluence-class conjectures also open upstream
  (`sort_inv`, `forallE_inv`, `sort_forallE_inv`, `rigidApp_inv`,
  `fieldType_inv_stratified`); `saturated_of_hasType` needs a rigid-head vs
  Pi separation lemma of the same class and is effectively base-layer.
- `weakN_iff` is false and must be replaced; about 72 textual uses of the
  `weakN_iff`/`weak'_iff`/`OnCtx.*_inv` family under `Verify` (2026-10-06
  count) depend on it, including `TrExprS.weakFV'_inv` (hence
  `MLCtx.restrictUpSetCtx` and the whole shape-definition program of item 7),
  `ConditionallyWHNF.weakN_inv` (the checker's cache invariant) and the
  header phase's `restrictTrExpr`. The repair needs a redesign (typing/defeq
  transport justified by actual inhabitants or a context-restricted invariant
  for the checker's cache), which is upstream work as well. What the
  consumers actually need is mostly existential well-formedness
  strengthening and strengthening at sort types, which the countermodel does
  not refute.
- The three core refinement junctions (`canonicalConsumedGeneration`,
  `canonicalCompletedRuleTranslation`, `assemblyNative`) are each a
  `Nonempty` of a large certificate structure assembling thousands of lines of
  component lemmas written against the formerly false model. Their
  components must be re-audited now that the template chain runs on the exact
  model; the executable they describe is now validated empirically against
  Lean's own recursors, which was not true before.
- **The junctions are the whole specification connection, not an
  assembly step.** Outside the three junction targets and their
  `Realization` definitions, the verification layer references the abstract
  generator only through `InductiveSignature.Instance.motive`
  (`CanonicalMotiveGroup.lean`). Nothing relates a production minor type to
  `Instance.minor`/`Instance.hypothesis`, a generated iota rule to
  `Instance.equation`, or `declareRecursors.recursorType` to
  `Instance.recursorType` (grep 2026-10-05). The equation layer
  (`Equation/*`, `Completed*`, about 56k lines) proves source-vs-production
  alignment of binders and residuals, not generator correspondence. So
  "recursor metadata/equations" and the minors part of recursor types are
  open in full, hidden behind `Nonempty` of certificate structures; the
  derived audit root `canonicalTypeTranslations` is not independent evidence.
  The first real junction theorem is: for `s := R.sourceSignature`, the
  production minor type of each constructor translates to `Instance.minor`
  (fields via `sourceSignature_fieldTypes`, hypotheses via
  `RecInfoMinorHypothesisTypeOrigin`, residual via the terminal spine).
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
2. **Close the three refinement junctions.** `canonicalConsumedGeneration`
   and `canonicalCompletedRuleTranslation` are closed (item 7). Remaining:
   `assemblyNative` and `finalValidOfStaged` (nested). Scoping (2026-10-06): the rule junction must produce
   `rules = g.equations` syntactically, so each generated rule is identified
   with `Instance.equation` component by component: outer domains from the
   checked type (`canonicalTargets`), field domains from `minorFieldsTemplate`,
   the right-hand side built constructively from the small-context shape
   translations exported by the first junction (weakened into the equation
   context, never derived from minor or recursor contexts, which would be
   strengthening), the left-hand side and type from
   `sourceConstructorIndices_replay` after universe rebase, typing of the
   equations transported from the equation layer's defeq-aligned residuals,
   recursor metadata from the generated entries (`getMajorInduct`,
   `KTargetCheck`), and the literal identity `info.rules = blueprints.map build`
   carried from the producer (dropped today before
   `CompletedRecursorPhasesResult`). Estimate 2k to 4k lines. The nested
   sorries: `finalValidOfStaged` needs executable-vs-abstract restoration
   commutation (`restoreNested` against `Restoration.expr`,
   `ContainerSpecialization` built from the lowering, name/order agreement),
   a rule-free restored recursor realization and `RecursorEnvCoherent.extend`
   for the stripped map; `assemblyNative` additionally needs the rule junction's
   content restored (`CompilationData.equations`, `RestoredRuleRealization`,
   provenance), `CertifiedSpecializations` from the installed containers, and
   a substitution lemma (restoration preserves `IsDefEq`) for the constructor
   correspondence; the auxiliary families' `resultLevel`/`indices` comparison
   rests on the Injectivity base sorries. Estimate 4k to 6k lines beyond the
   rule junction.
   **Progress (2026-10-06, later):** rule junction components committed:
   `GeneratedRecursorEntry.rules_eq`/`rulesLiteral` (literal blueprint builds),
   `consumedGeneration_shapeTranslations` (`Recursor/ConsumedShapeTranslations.lean`;
   `consumedGeneration` is now the explicit construction), `RecursorMetadataRealization`
   (`RecursorMetadataRealization.lean`, every `RecursorRealization` field but `rules`),
   `EquationWF.lean` (`equationsWF` modulo `GeneratorBodyTranslations`),
   `RuleLhsTranslation.lean` (lhs/type bodies, closedness),
   `RuleTranslation.lean` (`TrExprSyn`: untyped translation with unique targets;
   `ruleRhsSyn` hypothesis-free; `ruleRhsTranslation` needs any typed closed
   translation of the rule rhs, being discharged from the equation frame),
   `RuleTranslationAssembly.lean` (`completedRuleTranslation_of (Hrhs :
   H.RuleRhsTranslations) : Nonempty (CompletedRuleTranslationResult H)`).
   **Closed (2026-10-06):** `canonicalCompletedRuleTranslation` (moved to
   `CompletedRuleTranslation.lean`) `:= H.completedRuleTranslation_of
   H.ruleRhsTranslations`, no hypotheses; full build, tests, audit self-test
   and fresh `Init.Prelude`/`Init.Core` replays pass. Reachable sorries: the
   ten base obligations plus `assemblyNative` and `finalValidOfStaged`. Nested
   components committed: `Nested/ContainerSpecializations.lean`
   (specializations, certified, scoped, direct families, well-formed for the
   consumed parameters, constructor renaming), `Nested/RestorationCommutation.lean`
   (`restoreNested` vs `Restoration.expr` under `RestorationMapAgreement` and
   `RestoreReady`), `Nested/StrippedValidity.lean`
   (`finalValidOfStaged_of_shapes`), `Nested/RestoredRecursorShape.lean`
   (restored `VRecursorShape`), `Nested/CompilationDataAssembly.lean`
   (`CompilationData` of the run modulo `NestedCompilationPending`:
   constructor `RestoresType`, auxiliary family headers, restored recursors
   and equations), `Nested/RestorationAgreement.lean` (2026-10-06:
   `RestorationMapAgreement` for the run from `RestorationTableData` via
   `TrExprS.instantiateRevList_inv`; `RestoreReady` of lowered recursor types
   from the closed-form `LoweredRestoreReady`; per-owner
   `restoredRecursorTypes` modulo `ForallTelescope`/`LoweredRestoreReady`/
   `ForallDomainsReady` of the generated type and the restored type's
   translation). Found and repaired there: the `head` clause of
   `RestorationMapAgreement` was false for open arguments (sequential
   `instantiateRev`), now requires free-variable arguments of parameter arity;
   `RestoreReady` rejected literals (`lit`/`mdata` cases added). In progress:
   discharging those syntactic hypotheses, `Theory/Inductive/RestorationDefEq.lean`
   (restoration preserves `IsDefEq`; constructor `RestoresType`), and the
   auxiliary family header conjuncts.
   **Later (2026-10-06):** the readiness predicates were false for inputs with
   `let`/`proj`; replaced by `Expr.HitShape` (Nested/HitShape.lean: every
   auxiliary head applied to the parameter variables at the declaration's
   universe parameters) with commutation from hit shape plus the translation
   of the restored output in an auxiliary-free environment
   (`RestorationCommutationHit.lean`). Committed since: beta subject
   reduction, eliminator schema avoidance, source and auxiliary constructor
   restoration (restoring expansion leaves, lowering levels recorded in the
   traces), auxiliary family headers, `CompilationData` assembly
   (`CompilationDataConstructors.lean`), restored recursors field
   (`RestoredBlockAssembly.lean`), hit-shape provenance of generated
   recursor types and rule rhs (`RecursorHitShape.lean`, modulo
   `HitShapeInputs` and `WhnfHitShapeFacts`), run-level inputs and totality
   (`HitShapeInputs.lean`). In flight: retained `loopArgs1`/call-root traces
   (`indexDomains`, `callRoots`; branch `agent/verify-inductives-origins`),
   whnf/inferType hit-shape preservation (`agent/verify-inductives-hitshape`:
   `whnf.hitShape`, `inferType.hitShape` proved via new `VState.WF`/`Methods.WF`
   cache invariants; `EnvHitShape` instance for the lowered environment and
   the `WhnfHitShapeFacts` discharge pending), restored equations identity,
   and `Hshapes`/`finalValidOfStaged`.
   **Later still (2026-10-06):** `HitShapeInputs` fully discharged on
   `agent/verify-inductives-origins` (retained `loopArgs1` traces
   `RecursorIndexTrace`/`RecInfoIndexTraces` inside `RecInfoMinorSourceAlignment`,
   rooted call origins `RecInfoCallBlueprintOrigins.rooted`; family headers
   avoid the auxiliary names because `buildAuxiliary` never lowers headers:
   `LoweredInductiveMapping.type`), so `recursorHitShape` needs only `W`.
   Restored equations (`RestoredEquations.lean`): rule right-hand sides are
   identified with the restoration of the generator's equations through the
   lambda-telescope commutation; lhs and type cannot be read off the
   executable (`RecursorRule` has only `ctor`, `nfields`, `rhs`) and are
   supplied by the certificate's own rule choice (`RestoredRulesRealization`),
   which `assemblyNative` must realize with the restored generated lhs/type.
   In flight: `assemblyNative_of_whnf` (origins worktree), `WhnfHitShapeFacts`
   discharge (hitshape worktree), final shapes.
   Record of what the first junction used: the `params` and `motives`
   groups (`recursorTelescope_params`, `recursorTelescope_motives`), the
   field-domain template `minorFieldsTemplate`, the per-minor translation
   `recursorTelescope_minor`, the field-domain identification
   `recursorTelescope_minorFields`, and the residual inversion
   `recursorTelescope_minorResidual` (motive variable, constructor spine),
   the index identification `recursorTelescope_minorIndices`, the
   hypothesis-domain shape `recursorTelescope_hypothesisShape`, the index and
   major groups `recursorTelescope_indicesMajor`, and the assembly
   `recursorTarget_eq_of_minors` (recursor type modulo the minor group).
   Previously planned and now done: `idx` equals the lifted
   `sourceConstructorIndices`
   (forward: `liftOriginalType`, `insertBeforeInner`, `bvLift`, then
   uniqueness); each hypothesis domain inverts to `wrapForalls A (app (mkApps
   (bvar m) I) (mkApps (bvar f) bvars))`, and the consumed signature's
   `Recursive` shapes must be defined so that `Instance.hypothesis` reproduces
   `A` and `I`: either as unlifts (`VExpr.unliftN`) of the inverted domains,
   justified by first-pass scope facts (`O.args` domains and `exposedType`
   indices mention only parameters, earlier fields and earlier arguments), or
   by forward derivations closed with `mkLambda` over fields and arguments,
   dropped to the parameter suffix (`dropFVarPrefix`), abstracted
   (`abstractParameters`) and weakened. Then `Models` of the consumed
   signature by definitional transport from `sourceSignature_models`,
   `sourceOrigins` by construction, `types` from `T.target_eq`, and
   `minorTranslation` from the `params ++ motives ++ minors` prefix of `T`.
   The `Recursive` shapes and `Models.recursiveTypes` are blocked by item 8.
   The other junctions (`canonicalCompletedRuleTranslation`, `assemblyNative`)
   need `RecursorEntryRealization` per owner (`Recursor/Realization.lean`) and
   the restored analogue plus `InductiveRecursorProvenance`; the equation
   build (`existsCanonicalGeneratedEquationBuild`) supplies the rule list.
   Staging: the junction is proved at the `CompletedRecursorConstruction`
   stage, whose fields (now including `recursorTypes`) are the only premises;
   post-installation results (`GeneratedRecursorTelescopeTranslation`,
   `finalSelectedMinorTypedSplit`) are reusable as technique only. Use the
   recursor-comparison scratch (regenerating `Acc`, `iterates`, nested types
   through `Lean4Lean.addDecl`) as the executable oracle.
3. **Replace `weakN_iff` and repair consumers**; coordinate with upstream.
   **Scoping (2026-10-06, `/tmp`-free summary):** a dependency walk of the
   built oleans found 3445 constants depending on `IsDefEqU.weakN_iff`, 1523
   of them in the cone of `addDecl.WF`, through every declaration kind: the
   checker-cache invariants `ConditionallyHasType.weakN_inv` /
   `ConditionallyWHNF.weakN_inv` (`Verify/Typing/ConditionallyTyped.lean`)
   used when `withLocalDecl`/`withLetDecl` leave a scope, and the
   `EquivManager` invariant `VState.WF.ectx` used by `quickIsDefEq.WF`. The
   weaker fallbacks (existential `VExpr.WF` strengthening, `IsType`
   strengthening, strengthening at sorts, `TrExprS.weakFV'_inv`) are refuted
   as well: `(fun x : SJ => x) z` with `z : SI` is typed under `q` and, by
   `app_inv`, uniqueness and `forallE_inv`, typing it without `q` would give
   `SI ≡ SJ`. Only two use sites are pure weakening. **Executable evidence
   (`docs/inductives/CacheScopeExperiment.lean`):** both the C++ kernel and
   the Lean4Lean checker accept a closed definition whose typing needs
   `SI ≡ SJ` in the empty context, provided an earlier `let` binding forces
   the comparison chain under a binder `q : P v` first; without that binding
   both reject it. So the implemented conversion is not local to the context
   and no invariant of the form "cache entries are derivable in the current
   context" holds for the current executable; `addDecl.WF` as stated is
   false for it (assuming the countermodel). Options for Kim: E1 change the
   executable (save and restore caches and the `EquivManager` around binder
   scopes, always open a binder in `isDefEqLambda`/`isDefEqForall`, re-check
   a few Primitive gadget pieces in the empty context; statement of
   `addDecl.WF` unchanged; departs from C++ exactly on declarations whose
   acceptance needs a conversion established under a binder and reused
   outside it; performance to measure); E3 add an environment-level
   strengthening hypothesis to `addDecl.WF` (restricts the theorem; false
   for some Lean-valid environments). E2 (prove executable locality) is
   impossible given the experiment. Inductive-side consumers (header phase,
   consumed translation, `restrictUpSetCtx`, `weakBV_inv_lift`) need either
   producer changes keeping a narrow-context run or a locality theorem for
   fresh checker runs. Estimated total 3k to 12k lines depending on route.
   **Decision (Kim, 2026-10-06): try both routes in parallel and keep the one
   that reaches the end.** E1 is developed on branch
   `agent/verify-inductives-e1` (worktree `../lean4lean-e1`): scoped caches
   and `EquivManager`, binder always opened in `isDefEqLambda`/`isDefEqForall`,
   Primitive gadget pieces re-checked in the empty context; success criteria
   are a full build with no `weakN_iff`-family use under the checker, Primitive
   and `ConditionallyTyped`, the cache-scope experiment now rejected by the
   Lean4Lean checker, and fresh `Init.Prelude`/`Init.Core` replays with
   timings against the unmodified branch. E3 is developed on
   `agent/verify-inductives-e3` (worktree `../lean4lean-e3`): `VEnv.Strengthening`
   replaces the sorry as an explicit hypothesis threaded to `addDecl.WF`,
   quantified over exactly the intermediate environments each declaration kind
   uses (the output environment's strengthening is never claimed). The nested
   junction work continues on `agent/verify-inductives` and is merged into
   the surviving route afterwards.
   **E1 status (2026-10-06):** checker cluster done on `agent/verify-inductives-e1`
   (commits be54d43, 000dbcc, 758bb60): `State.leaveScope` restores the infer,
   whnf, failure caches and the `EquivManager` at every `withFreshId` scope
   (keeps `ngen`, `unfold`); `isDefEqLambda`/`isDefEqForall` always open a
   binder; `Condition.check` re-checks the gadget pieces at `[]`;
   `unfoldNatWellFounded` re-checks `F` in the outer context. No
   `weakN_iff`-family use remains under `Verify/TypeChecker`,
   `ConditionallyTyped`, `Primitive`; the checker still reaches `weakN_iff`
   only through `VExpr.WF.of_occurs`, `VIotaRuleShape.args_typing`,
   `TrExprS.weakBV_inv₁` (class (b), being repaired) and the inductive side.
   The cache-scope experiment is now rejected by the Lean4Lean checker.
   Replays check the same declaration counts; cost: `Init.Core` unchanged,
   `Init.Data.List.Lemmas` +21%, `Std.Data.HashMap.Lemmas` 26.6 s to 49.0 s
   (+84%), inherent to discarding in-scope cache entries.
   **E1 inductive side (design, 2026-10-06, `docs/inductives/E1_INDUCTIVE_DESIGN.md`):**
   79 strengthening uses under `Verify/Inductive` strengthen fresh checker
   runs from the nested context of `Inductive/Add.lean` (later families run
   inside earlier families' indices; constructor and recursor phases inside
   stale header indices; later constructors under earlier minors). Chosen
   repair (P): a second local context `checkLCtx` seen only by the lifted
   checker calls (parameters, indices, fields, argument binders in both
   contexts; majors, motives, minors, hypotheses only in the main one), with
   snapshots per parameter and per field; estimated 4.5k to 9k lines of churn
   (much deletion), versus 9k to 16k for a fresh-run locality theorem (L).
   (P) is a second executable departure, invisible if (L) holds (argued, not
   proved). Scoping reports copied to `docs/inductives/WEAKN_SCOPE.md` and
   `docs/inductives/RESTORE_READINESS.md`.
4. **Executable hygiene**: literal cost in `guardedIotaCheck`, the `Std`
   replay slowdown, and a review of every runtime rejection added in
   `Inductive/Add.lean` (grep `throw <| .other` in the diff against
   `origin/master`) against Lean-accepted declarations beyond `Init`/`Std`.
   `checkIndexUniverses` is gone (its fact is now proved, see the universe
   un-shift entry under item 7 above).
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
- After adding `recursorTypes` (2026-10-05): `lake build` (629 jobs) and
  `python3 scripts/check-inductive-audit.py --self-test` pass.
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
