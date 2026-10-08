# Restoration readiness: what the Expr-level obligation really is

Worktree: /home/kim/worktrees/lean4lean/lean4lean-agent-verify-inductives (HEAD 1b78e96).
All paths are relative to it. Line numbers are at HEAD; uncommitted files were ignored.

## 0. Executable facts the analysis depends on

- Hit semantics. `ElimNestedInductive.Result.restoreNestedNode` (Lean4Lean/Inductive/Add.lean:854-872):
  - a bare `.const c ls` with `c ∈ auxRec` is renamed (857-859);
  - otherwise a node `t` is a hit iff `t.getAppFn = .const c _`, `c` is an `aux2nested` family or a constructor of one (`getNestedIfAuxCtor`, 845-847), and `args.size ≥ nparams`.
  - The `assert!` (864, 868) is `panic` = `default` = `none` in the logical model, so an under-applied aux head is a miss, not a hit. This is proved in `restoreNestedNode_eq_of_notRecursor` (Verify/Inductive/Nested/RestorationCommutation.lean:144-189), and `restoreHead` (130-142) packages it.
  - On a hit, the executable returns `nested[As]` applied to `args[nparams:]` verbatim. It never inspects `args[:nparams]` or the hit's universe levels, and `Expr.replace` does not descend into the result.
  - Every miss is traversed structurally, including `letE`, `proj` and `mdata` (Lean4Lean/Expr.lean:47-60; relational model `ExprReplacement`, Nested/Replacement.lean:17).
- Domains of every `withLocalDecl` are `dom.consumeTypeAnnotationsVerified` (Expr.lean:26-35). That function strips only an outer `optParam`/`autoParam`/`outParam`/`semiOutParam` wrapper, so the result is a subterm.
- whnf never touches a forall. `whnf'` (TypeChecker.lean:558) and `whnfCore'` (404) return `.forallE` unchanged; the proof is `whnf_forall_result_eq` (Verify/TypeChecker/AlphaLocality.lean:925, used in Recursor/ReplayCompat.lean:877).
  - So a whnf call rewrites a binder domain only when the input is not already syntactically a forall.
  - In that case the exposed forall comes from a delta-unfolded env definition (levels instantiated), a beta/zeta instance (`instantiate`), or a proj/iota/Nat/native reduct, and its domains are subterms of that reduct.
  - whnf never normalizes inside a domain.
- Lowering output (Add.lean:1059-1099, 1031-1044):
  - every replaced node is literally `mkAppRange (mkAppN (.const auxI st.lvls) As) I_nparams args.size args`;
  - `As` are the fvars opened by `withParams` (1081-1091), and `st.lvls = lparams.map .param` (2058);
  - the trailing `args[I_nparams:]` are untouched source subterms, because `replaceM` stops at the hit;
  - the result is closed by `lctx.mkForall As` (1096);
  - auxiliary constructors go through the same `lowerConstructor` (`lowerNext` 1105-1114 over `newTypes`, which `buildAuxiliary` 1006-1029 extends).
- The source of "Ht", meaning the translation of the restored output in an environment without aux names:
  - `validateRestoredRecursorTypes.check` (Add.lean:1349-1366) type-checks the restored recursor type in `validationEnv`. That environment is the source env plus restored headers and constructors, so it has no `_nested` family or constructor names.
  - `validateRestoredRecursorRules.run` checks the rules in the stripped `restoredEnv` (2032-2034). This is existing behaviour, not a new check.

## 1. Q1: Expr-level facts about (A) the recursor type and (B) rule right-hand sides

### Overall shape

`oldInfo.type = (declareRecursors.recursorType stats recInfos lctx d).inferImplicit 1000 false` (Add.lean:728). `inferImplicit` changes binder infos only. `recursorType` (707-715) is `lctx.mkForall` over five fvar arrays:

```
params, motives, flatMap minors, indices[d], #[major]
```

with body `motive indices major`.

Expr-level skeleton facts that already exist:
- `RecursorLocalSelections` (Recursor/Origins.lean:2960).
- `RecInfoBindings.toRecursorLocalSelections` (3008) and `selectionNoAlias` (3019).
- `Hsel.forallTelescope` with residual `concreteRecursorResult` (Recursor/CanonicalRecursorTelescope.lean:35-70) gives `Expr.ForallTelescope` of the type at the full arity.
- Each domain Expr is the lctx declaration type of the corresponding fvar, abstracted (`LocalContext.mkForall`; `BoundFVarArray.forallDomainsOnly`, Recursor/CanonicalIndexReplay.lean:186).
- Everything in `CanonicalRecursorTelescope.lean` (`recursorTelescope`, `_params` 76, `_motives` 106, `_minorFields` 345, `minorFieldsTemplate` in CanonicalMinorFields.lean:75) is translation-level. It inverts the retained `TrExprS` of `recursorTypes` (CompletedRecursorConstruction.lean:50).

### Exact Expr declaration types retained in `CompletedRecursorConstruction` (CompletedRecursorConstruction.lean:16-85)

- `origins : RecInfoTypeOrigins` (Origins.lean:1344). Uses `BoundFVarTypeOrigins` (421) to give, for motives, majors, indices and minors, the exact Expr stored by `withLocalDecl`.
- `majorShapes : RecInfoMajorTypeShapes` (Origins.lean:1439): major type `= (mkAppN (mkAppN stats.indConsts[i] stats.params) indices).consumeTypeAnnotationsVerified`.
  - `stats.indConsts[i] = .const name stats.levels` (Add.lean:156) and `stats.levels = lparams.map .param` (Add.lean:168).
  - So the major domain is a literal hit `auxI stats.params idx-fvars`.
- `motiveShapes : RecInfoMotiveTypeShapes` (Origins.lean:1528): motive type `= lctx.mkForall indices (lctx.mkForall #[major] (.sort elim))`. Its major binder domain is the literal hit above.
- `minorSources : RecInfoMinorSourceAlignment` (Origins.lean:4121-4151), for every minor:
  - `S.origin` is the minor declaration type;
  - `S.sourceConstructors = indTypes[owner].ctors`;
  - a `traversal` exists with `isValidIndApp? stats traversal.terminal = some _`;
  - `S.motiveApp = motive itIndices (mkAppN (mkAppN (.const ctor stats.levels) stats.params) S.fields)`. This is a literal aux-constructor hit when the owner is auxiliary;
  - `BindingContextLE` of root, terminal and source contexts into the final context.
- `RecInfoMinorTypeShape` (Origins.lean:1190-1225): `sourceType = mkForall fields (mkForall hypotheses motiveApp)` and `consumed_eq`.
- `RecInfoMinorTraversalShape` (Origins.lean:746-772) carries:
  - `decisions : RecursorFieldDecisions` (Constructor/Replay.lean:2492-2522). The exact executable field loop: each field is declared with `dom.consumeTypeAnnotationsVerified` of the current syntactic binder, then `body.instantiate1 (.fvar _)`, with no whnf (`loopCtorArgs`, Add.lean:478-492).
  - `parameterPrefix : RecursorParamPrefix stats 0 constructor.type parameterTail` (Recursor/Structure.lean:805): the constructor's parameter binders are instantiated syntactically with `stats.params`.
  - `fieldTelescope`, `fieldClosed`.
- Hypotheses (IH): `RecInfoMinorHypothesisTypeOrigins` (Origins.lean:1168) and `RecInfoMinorHypothesisTypeOrigin` (850-871) record:
  - the exact `loopUArgs` run: `RecursorLoopUArgsInput` (810: `inferType` then `whnf`) and `RecursorLoopUArgsPrefix` (825: whnf after each instantiate; declared domains are the consumed domains of the whnf-exposed forall);
  - `owner_valid : isValidIndApp? stats exposedType = some ownerIdx`;
  - `type_eq : type = current.lctx.mkForall args (motive itIndices (field args))`.
- Rule blueprints (B):
  - `blueprints : RecInfoRuleBlueprintOrigins` (Origins.lean:1414) and `RecInfoRuleBlueprintOriginAt` (1393): `B.fields = S.fields` and `B.lctx = S.sourceFullContext.lctx`, so the field lambda domains are the minor's field declaration types.
  - `RecInfoCallBlueprintOrigins` (1366-1391): each call `template` is literally `O.current.lctx.mkLambda O.args ((mkAppN (.bvar n) itIndices).app (mkAppN field args))`.
  - Rule rhs construction: `RecRuleBlueprint.build`/`RecCallBlueprint.build` (Add.lean:670-691). The recursor heads are `.const (mkRecName auxI) lvls`. These are `auxRec` names, which are only renamed and never hits.
  - Translation of (B): `CompletedRecursorConstruction.ruleRhsSyn` (Verify/Inductive/RuleTranslation.lean:1214) gives an untyped `TrExprSyn` to the generator equation rhs.
- Index declaration types: only the exact Expr (`origins.indices`) and translations (`indexRows`, `chooseOriginalIndexDomains_*`, CanonicalIndexReplay.lean:234/292). The family indices of the consumed signature are translations of these recursor-time Exprs (`consumedFamilies`/`sourceIndices`, Recursor/CanonicalFamilyReplay.lean:65-82). There is no Expr relation to the auxiliary header syntax.
- Parameter declaration types: only translation-level (`parameterSuffix`, `parameterDecls`). The Expr is the consumed domain of the whnf-exposed header at `checkInductiveTypes.loopType` (Add.lean:108-133). That runs in the pre-declaration env, which has no aux names.

### Field domains: syntax or only translations?

Syntactically, they are fixed by the retained trace. The declaration type of field `j` is `consume(dom_j)`, where:
- `dom_j` is the j-th binder domain of `parameterTail` after instantiating the earlier field fvars;
- `parameterTail` is the lowered `ctor.type` with its parameter bvars instantiated by `stats.params`.

This lives in the context updates of `RecursorFieldDecisions`. However, no lemma states it explicitly: `RecursorFieldDecisions.fieldDeclarationAt` (ReplayCompat.lean:747) only gives existence of some cdecl. An induction on `RecursorFieldDecisions` stating "`lctx.find? fields[j] = cdecl … (consume dom_j)`" is about 60-120 lines.

The translation-level facts are `recursorTelescope_minorFields` (CanonicalRecursorTelescope.lean:345) and `sourceFieldDomains` / `sourceFields_headerReplay` (CanonicalFieldReplay.lean:243; translated in `R.headerVEnv`, which contains no constructors or recursors).

Origin and scope files mentioned in the question:
- `FieldTypeScope.lean` (`inferTypeFVarRun.WF` at 19: fvar inference returns the declaration type; `fieldTypeScope` at 155) gives scope only.
- `TelescopeUniqueness.lean` (`TrExprS.telescope_unique` at 129) is translation-level.
- `ConsumedShapeTranslations.lean` (32-196) is translation-level.
- `SourceBVarClosed` (Nested/Lowering.lean:1367) is bvar-closedness of the source.
- `RecInfoCallBlueprintSemanticOrigin` (Recursor/SecondPass.lean:37) and `RecursorFieldPrefixScope` (SecondPass.lean:302) are semantic and scope facts.

### Where the recursor-pass whnf calls sit, and whether they rewrite domains

- `checkInductiveTypes.loopType` (Add.lean:119, 125, 129, 142): whnf of the header and of each body. Parameter domains and header-time index domains are domains of whnf outputs.
- `mkRecInfos.loopArgs1`/`loopInd1` (Add.lean:448, 451, 462): whnf of each family header and body. The recursor's index domains (motive types, indices group) are domains of whnf outputs (region R1).
- `isRecArg.loop` (Add.lean:259): classification only; nothing is stored.
- `loopUArgs` (Add.lean:495, 502): `whnf (inferType ui)` and whnf of each body.
  - The IH binder domains `xs` (region R2) and the exposed type, hence `itIndices` (region R3), are whnf outputs.
  - These appear in minor IH types in (A) and (B), and in call lambdas in (B).
- `loopCtorArgs`: no whnf. Field domains are the lowered constructor's syntactic binder domains.
- `checkPositivity.loop` (Add.lean:282): a separate run at constructor-check time. Its syntactic `hasIndOcc dom` check (271) is exported only as `UniformFieldNormalForm` of a defeq normal form (Constructor/Normalization.lean:194; Theory/Inductive/Signature.lean:34-55). It is never tied to the recursor's `xs` domains.

A whnf call rewrites a domain only through a delta, beta, zeta or iota step at the head. It then exposes a domain that is a subterm of the reduct, so the domain is syntactically different from anything in the input whenever the input field type was not already a syntactic forall telescope ending in a valid inductive application.

## 2. Q2: lowered constructor types (C)

### Expr-level characterization (exists)

- `NestedExprMapping` (Nested/Mapping.lean:1472-1547) is structural over every Expr constructor, including `letE`, `mdata` and `proj`.
- Hit leaves are `NestedReplacementHasFinalMapping` (Mapping.lean:1120-1138):

  ```
  lowered = mkAppRange (mkAppN (.const auxName auxLevels) As) value.numParams n input.getAppArgs
  auxLevels = state.lvls
  ```

  together with the `aux2nested` lookup.
- `NestedExprReopening` (1632) and `restore_eqv` (1892) give the syntactic inverse of executable restoration.
- Per constructor:
  - `LoweredConstructorTranslation`/`Mapping`/`Reopening` (Nested/LoweringTrace.lean:65, 232, 253): `out.type = lctx.mkForall As lowered`, `As.size = nparams`.
  - `lowerConstructor.translation` (1078), `LoweredConstructorTranslations.finalMapping` (1511), `restoredBody_inverse` (448), `restoredBody_inverseOfSyntax` (488).
- Source-side disjointness: `RestoreSourceDisjoint` (Nested/Lowering.lean:1595) and `RestoreNamesReserved` (1655; every aux family and constructor has prefix `_nested`), via `SourceConstructorSyntax.noNestedAux`.
- So every aux head in a lowered constructor type is `mkAppN (const auxI lparams) As` applied to trailing args, the trailing args avoid restorable names, and after `mkForall As` the params are the bvars at the right depth. This is exactly the existing `LoweredRestoreReady.hit` shape (RestorationAgreement.lean:1510-1518).
- What is missing is only an explicit lemma packaging this (NestedExprMapping plus RestoreSourceDisjoint gives readiness of `lowered`) and its transport through `mkForall As`, `RecursorParamPrefix`, field `instantiate1` and `consume`.
- For auxiliary constructors, the pre-lowering source is `lctx.mkForall As (instantiateForallParams J_ctor.type …)` (Add.lean:1022-1027). Its disjointness needs env freshness of aux names (`NestedAuxMapNamesFresh`, Mapping.lean:526; `GeneratedFamilyWitness`, 348).

### VExpr-level characterization

- `VExpr.NestedExprExpansion` (Theory/Inductive/Formation.lean:618), `NestedConstructorExpansion` (698), `NestedExpansion.leafTarget` (748).
- `VInductDecl.NestedAuxiliarySource` (Theory/Inductive.lean:~307-345) has leaf output:

  ```
  VExpr.mkApps (.const aux auxiliaryLevels) (source.paramVars depth ++ targetTrailing)
  ```

  This is VExpr readiness at hits. However, `targetTrailing` is itself a `NestedExprWFExpansion` and may contain hits, and the docstring notes that erased (let/mdata) occurrences are not tracked.
- `DirectAuxConstructor` (Theory/Inductive.lean:254) relates aux constructor types only up to `IsDefEqU`.

### Positivity as syntactic facts

- `isValidIndAppIdx.param` (Constructor/Positivity.lean:1535): parameter args are literally the `stats.params` fvars, via `Expr.eqv_fvar_eq`.
- `isValidIndAppIdx.indexNoOccurrence` (1554): `hasIndOcc indConsts` is false on index args. `indConsts` covers all lowered families, including aux families, but not aux constructor names.
- `isValidIndAppIdx.validIndAppAt` gives the VExpr `ValidIndAppAt` (Theory/InductiveShape.lean:52-62): indices are `SourceConstFree` with respect to the family names.
- These are recorded for:
  - the constructor terminal (`minorSources`, Origins.lean:4138);
  - the IH exposed type (`owner_valid`, Origins.lean:866);
  - `isRecArg` decisions (`RecursorFieldDecisions`).
- So (iii) holds syntactically for the major, motive-major and intro hits (trailing args are fvars) and for lowering hits (trailing args are source args). Index-arg family-freeness of R3 is syntactic; aux-constructor-freeness of R3 is not.
- The positivity domain check (`hasIndOcc dom`) is not recorded syntactically anywhere usable for R2.

## 3. Q3: Route S versus Route T

### Key observation: (i) and (iii) come from Ht, which already exists

`TrExprS.sourceAvoidsFresh` (Constructor/Positivity.lean:2297) says that a `TrExprS` in an env lacking names `N` forces the Expr to avoid `N` syntactically, including let types and values, mdata and proj majors.

Apply it to `Ht : TrExprS targetEnv … (restoreNested input) t` with `N` = aux family and aux constructor names (absent from `targetEnv`; see the `RestoreNamesReserved`/freshness plumbing).

Every aux occurrence the executable does not consume as a hit survives verbatim into the output, so:
- under-applied, bare, mdata-separated or let-separated heads with fewer than `nparams` args are refuted;
- (iii), restorable names in a hit's trailing args, is refuted, because trailing args are copied verbatim.

Recursor names need nothing: they are renamed wherever they occur, consistently with `Restoration.recursorName`.

What remains is genuinely irreducible: (ii) and (lev). Every node the executable actually replaces must have its first `nparams` args equal to the opened params (equal translation suffices), and its universe levels must translate to `auxLevels`. The executable ignores both; `Restoration.expr` uses both through `HeadSpecialization.apply` (Theory/Inductive/Restoration.lean:47, 74-100).

Commutation-proof side facts (both routes):
- `RestoreFragment` is unnecessary. `TrExprS.toSyn` and `TrExprSyn.uniqueCtx` (RuleTranslation.lean:47, 62) with `TrExprS.IsUniqueCtx`/`IsUniqueDecl` (Verify/Typing/Lemmas.lean:1920-1926; vlam types may differ, vlet values equal) give same-Expr translation equality for all syntax, including let and proj (`TrProj` is `direct`, Typing/Projection.lean:11-16).
- `ForallDomainsReady` can be dropped. The parameter prefix is not traversed (`SameForallPrefix`), so the output prefix equals the input prefix. Ht then gives name-avoidance, and `noConstsOfSourceAvoids` (Positivity.lean:2367) gives VExpr avoidance. Alternatively, parameter domains are translated in the header-check env, which has no aux names.
- The current false hypotheses are `RestoreReady` (RestorationCommutation.lean:563, no let/proj constructors, fragment args), `ForallDomainsReady` (964), `LoweredRestoreReady` (RestorationAgreement.lean:1510) and the `Hfragment` premise of `RestoredRuleRhsTranslation.restoredRhs` (RestorationCommutation.lean:1270).

### Route S (syntactic Expr readiness)

New predicate `RestoreReady'`:
- `hit`: head `const c auxLevels`, `c` a head, `nparams ≤ #args`, and `args.take nparams = As` literally. No condition on trailing args.
- Structural constructors for every Expr form, including `letE`, `proj`, `mdata`, and `const`/`app` with any head.
- A de Bruijn twin (`LoweredRestoreReady'`) and the existing transport `LoweredRestoreReady.restoreReady` (1545) adapted.

Commutation changes:
- Add a context relation for `vlet` entries, `valt = r(vals)` (proved from the IH on the value, since the value is ready syntactically).
- Add `Restoration.expr` commuting with `liftN` for scoped heads (`Restoration.Scoped`, Restoration.lean:60; no such lemma exists yet; `replaceConsts_liftN` in RestorationDefEq.lean:67 is the analogue).
- Add a `proj` case.
- Add a lemma for untraversed trailing args: an Expr avoiding names has `r(s) = t` under the context relation.
- Generalize the spine clause so a head whose args are split by mdata or let still matches. This needs `HeadSpecialization.apply` with extra args equal to `mkApps` of the exact application.
- Size: about 600-900 lines.

Provenance needed:
- (a) Hits built by the recursor (major, motive-major, minor intro):
  - read off `RecInfoMajorTypeShapes`, `RecInfoMotiveTypeShapes`, `RecInfoMinorSourceAlignment`;
  - push them through the five `mkForall` groups and the per-minor `mkForall fields/hyps`, then `abstractList stats.params` gives the bvar-param form.
  - Mostly plumbing with existing abstraction lemmas (`Expr.abstractList_mkAppN`, `abstractN_eq_abstractList`, `getAppFn_instantiateRevList_fvars_const`). About 500-800 lines.
- (b) Field domains, in both the minor types and the rule field lambdas:
  - the `RecursorFieldDecisions` declaration-type lemma (about 100 lines);
  - readiness of lowered constructor types from `NestedExprMapping` and source disjointness;
  - transport through `mkForall As`, `RecursorParamPrefix` instantiation by `stats.params` (reopenParams infrastructure: LoweringTrace.lean:342-376, `Expr.reopenFVarsAt_eq_reopenParams`), `instantiate1` of field fvars, and `consume` (subterm).
  - About 600-1000 lines.
- (c) whnf regions R1 (index domains), R2 (IH binder domains), R3 (IH exposed indices). Not covered by anything existing. This needs a whnf readiness-preservation lemma. `P(e)` is: every aux family or constructor occurrence that heads a maximal spine has literal `As` params and `lparams` levels. `P` holds of all inputs (lowered field types, aux headers, env bodies, which have no aux names).
  - Note that `P` must not constrain trailing args: beta can put a hit inside another hit's trailing args, so a stronger `P` is not closed under `instantiate`. Ht handles trailing args.
  - The lemma has to go through `whnfCore'` (beta, zeta, proj, `reduceRecursor` including the K and structure-eta paths, which call `inferType`), `reduceNat`, `reduceNative`, `unfoldDefinition`, and per-call caches. Caches are empty per lifted call (Add.lean:80-82), so the cache invariant is local.
  - Scale: comparable to `WHNFAlpha.lean` (1253 lines) plus the `inferType` paths, roughly 2-4k lines.

Route S total: roughly 4-6k lines. The whnf lemma is the bulk.

### Route T (translation-level readiness plus (i) from Ht)

Commutation by induction on `TrExprS` of the input. The hypotheses are:
- VExpr readiness of `s`: every aux-headed VExpr spine has param vars at the current depth and levels equal to the translated `auxLevels`;
- Ht plus freshness of aux family and constructor names in `targetEnv`.

Contexts carry, for vlet entries, the guarded relation `ready(vals) → r(vals) = valt`:
- discharged at bvar lookups from `ready(s)` (the inlined value is a lifted subterm of `s`);
- established at `letE` from the value IH.

This handles erased positions (let types, unused let values, discarded param args) without any Expr-level knowledge. No Expr condition at all is needed beyond what Ht gives. (lev) can be stated on the VExpr side. Size: about 700-1000 lines, plus about 100-300 lines for name freshness of `targetEnv`/`validationEnv` (from `mkUniqueName` freshness, `RestoreNamesReserved`, `NestedAuxMapNamesFresh`, checkName distinctness).

Then VExpr readiness of `canonicalGeneration.recursorType owner`, decomposed via `Restoration.expr_recursorType` (Nested/RestoredRecursorShape.lean:121) and its counterpart for equation rhs:
- Params: translated in the header-check env, so `SourceConstFree` holds (`TrExprS.noFreshConsts`, Positivity.lean:2411). Easy if the pre-declaration translation is exposed; `RecursorContextWF.cdeclTypeAvoids` (2318) is the template.
- Motives: `familyApp` is constructive (param vars). Family index VExprs are translations of recursor-time loopArgs1 Exprs (R1). No VExpr fact makes them aux-free. This needs either the whnf lemma (name-level suffices here, since inputs have no aux names) or an alpha replay against the header-time `loopType` run (different env; there is no env-monotonicity lemma for whnf).
- Field types: need readiness of the consumed signature's `fieldTypes`. Obtainable by transporting Expr readiness of field domains (Route S (b)) to VExpr. The VExpr formation evidence `NestedAuxiliarySource` gives the hit form, but identifying the consumed field types with those VExprs is still a translation-uniqueness exercise.
- IH binder domains `A` (R2): no syntactic VExpr fact exists. `Models.positiveFields` is up to defeq. Same gap as Route S (c).
- IH indices `I` (R3): `ValidIndAppAt` gives family freeness. Aux-constructor freeness needs the name-level whnf lemma or replay.

### Verdict

The irreducible Expr-level obligation is (ii) and (lev) at executable hit nodes. Hits built by the recursor and by lowering already satisfy it literally, and existing provenance reaches them. The gap common to both routes is the whnf-produced regions, above all R2. Nothing in the tree relates the recursor's `loopUArgs` normalization to the positivity check's normalization, and nothing gives a syntactic invariant for whnf outputs.

Route S is somewhat cheaper overall, for two reasons:
- Route T still needs the same whnf fact for R2 and R3, plus R1 and an Expr-to-VExpr transport for field types.
- Route S's extra cost (let/proj in the predicate, erased positions) is uniform under a single syntactic whnf-preservation lemma, and the provenance proofs are uniform over positions.

Best combination:
- Weakened Route S predicate, with (i) and (iii) discharged by Ht instead of a syntactic proof. This removes `RestoreFragment`/`ForallDomainsReady` and every "aux-free" side condition.
- (ii) and (lev) supplied by Origins/RecInfo shapes for recursor-built hits, by `NestedExprMapping` for field domains, and by one new whnf (and `inferType`) readiness-preservation lemma for R1-R3.

The existing infrastructure does not yet yield R1-R3. For the common case where a field type is already a syntactic forall telescope ending in a valid inductive application, `whnf_forall_result_eq` plus a small "whnf of an inductive-headed application is the identity" lemma makes R2 and R3 literally subterms of the lowered syntax. That covers ordinary inputs but not delta, beta or let field types (for example `Stream' (List T)`).

## 4. Q4: alternatives and what translation or typing forces

- Translation of the input alone forces nothing syntactic: a bare `const auxI` passed to a higher-order term, `mdata` around a head, or a let-bound head all translate. Well-typedness (`HasType`) of the lowered term does not force full application either, by eta or by `(fun F => F As) auxI`.
- The translation of the output (Ht), which the executable already checks (`validateRestoredRecursorTypes`, `validateRestoredRecursorRules`), forces (i) and (iii) at Expr level through `TrExprS.sourceAvoidsFresh`. This is the alternative worth adopting.
  - It needs freshness of aux family and constructor names in the target VEnv. Aux recursor names need nothing.
  - It is consistent with C++ fidelity: no new check is added.
- Neither translation nor typing forces (ii) or (lev). A hit `auxI q …` with `q ≠ As` is well-typed and translates on both sides, and the executable and the abstract restoration then disagree (`nested[As]` against `nested[q]`). It can only be excluded by provenance: literal lowering hits, plus preservation through whnf.
- The `RestorationDefEq` route (`Restoration.expr_isDefEq`, Theory/Inductive/RestorationDefEq.lean:616; `replaceConsts` with lambda heads) does not help. A `q ≠ As` hit is not defeq-equal, and `RestoredRecursorShapeInputs.type` (RestoredRecursorShape.lean:199-205) needs exact equality.
- Possible shortcut for R2 instead of a general whnf lemma: an alpha replay of `loopUArgs` against `checkPositivity.loop`, whose `hasIndOcc dom` check is syntactic. Existing tools are `WHNFAlpha.lean`, `RecursorFieldDecisions.alphaAlignment` (ReplayCompat.lean:569) and `ConsumeTypeAnnotationsAlphaCompat` (ConsumeAlpha.lean:80). It would need three things not present today:
  - `whnf (optParam T v) = whnf T`, because positivity runs on `dom` and `loopUArgs` on `consume dom`;
  - whnf invariance under the headerEnv-to-ctorEnv extension;
  - handling positivity's early exit on `!hasIndOcc t`, which itself needs a name-level whnf fact.
  The cost is probably similar to the preservation lemma, and it does not cover R1 or the constructor part of R3.
