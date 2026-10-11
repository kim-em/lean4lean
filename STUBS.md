# Open-proof ledger: verified inductives on the ι pattern calculus

Every `sorry` outside `Lean4Lean/Experimental/`, with its origin. The default `lake build`
targets (including `Lean4Lean.Theory` and `Lean4Lean.Verify`), `Lean4Lean.Tests` and
`Lean4Lean.Experimental` build. The accepted open proofs are exactly the `openProofs` of
`scripts/inductive-audit-inventory.json`, which `scripts/check-inductive-audit.py
--require-complete` checks against the dependency closure of the audit roots.

| statement | file | origin | status |
|---|---|---|---|
| `VEnv.WF.patsStrong` | `Theory/Typing/EnvLemmas.lean` | PR #43 | open |
| `VEnv.Model.PatValid.iota` | `Theory/Typing/HeadInjectivity/Model/PatSound.lean` | new: the `pat` case of `Model.sound` for the registered ι rules (see the observation-model section) | open |
| `IsDefEqU.weakN_iff` | `Theory/Typing/UniqueTyping.lean` | master | open on master; the one strengthening principle the checker uses |
| ~~`VEnv.WF.patCtor_rigid`~~ | `Theory/Typing/HeadInjectivity/Model/WFFacts.lean` | PR #53's `WF.installed_constructor_rigid` (`ConstructorRigidity.lean`) | proved (`WFFacts.lean:332`) |
| ~~`NormalEq.parRed`~~ | `Theory/Typing/ChurchRosser.lean` | master | retired: PR #53's sorry-free engine replaces master's file |
| ~~`VEnv.WF.singletonInstance_align`~~ | `Theory/Typing/Confluence/SingletonPatCoverage.lean` | new | proved by route (b) (`singletonInstance_alignJ`, see the confluence section) |
| ~~`VEnv.RestoredPattern.clause`~~ | `Theory/Inductive/RestorationInterpretation.lean` | new: the `pat` analogue of PR #53's `RestoredEliminator.clause` | proved |
| ~~`InductiveSignature.instantiateParams_liftN`~~ | `Theory/Typing/RestorationShapes.lean` | PR #53's `CaseReduction.lean` | proved |
| `VEnv.WF.patsStrong` | `Theory/Typing/EnvLemmas.lean` | PR #43 | wave 1D (`patsStrong`), after the 0b spike |
| `VEnv.Model.PatValid.nested` (`-- NESTED STUB`; replaces `Model.PatValid.iota`, whose ordinary case is `Model.PatValid.ordinary`) | `Theory/Typing/HeadInjectivity/Model/PatSound.lean` | new: the `pat` case of `Model.sound` for the ι rules of a nested block (see the model pat stubs section) | model pat stubs |
| ~~`VEnv.WF.patCtor_rigid`~~ (closed, model pat stubs: `CompiledInductive.rule_ctor_cases` along the history) | `Theory/Typing/HeadInjectivity/Model/WFFacts.lean` | `ConstructorRigidity.lean` on the source branch (`WF.installed_constructor_rigid`) | model pat stubs |
| `IsDefEqU.weakN_iff` | `Theory/Typing/UniqueTyping.lean` | master | open on master; the one strengthening principle the checker uses (PORT_PLAN section 5) |
| ~~`NormalEq.parRed`~~ (retired, wave 4: the verified-inductives branch's engine, sorry-free, replaces master's file) | `Theory/Typing/ChurchRosser.lean` | master | wave 4 |
| `VEnv.WF.singletonInstance_align` (WAVE 4 STUB) | `Theory/Typing/Confluence/SingletonPatCoverage.lean` | new: index alignment of a `Prop`-source singleton ι instance with its generic equation (see the wave 4 section) | wave 4 (needs a decision, see there) |
| ~~`VEnv.RestoredPattern.clause`~~ (closed, wave 3 eqinst) | `Theory/Inductive/RestorationInterpretation.lean` | new: the `pat` analogue of the source branch's `RestoredEliminator.clause` | wave 3 (Equations+Install) |
| ~~`InductiveSignature.instantiateParams_liftN`~~ (closed, wave 3 eqinst) | `Theory/Typing/RestorationShapes.lean` | source `CaseReduction.lean` | wave 3 (Equations+Install) |

Not stubs but conditional results: everything through `VEnv.WF.orderedStrong` (the strong
system, substitution theorems, inversion lemmas) depends on `patsStrong`; everything through
`VEnv.WF.headInversion` and `IsDefEq.uniq` depends on `patsStrong` (through
`VEnv.WF.orderedStrong`, see the observation-model section) and on `Model.PatValid.iota`.
`Injectivity.lean` has no `sorry` of its own: PR #43's `IsDefEqU.const_arity_inv` is derived
from `VEnv.WF'.inductTypeRigid` and `headInversion`. The confluence theorem
`VEnv.WF.church_rosser` depends on `patsStrong`, `Model.PatValid.iota` (through
`IsDefEq.uniq`, which the engine's transport lemmas use throughout), and on nothing else
(`scripts/check-inductive-audit.py`).
`VEnv.WF.church_rosser` depends on `patsStrong`, `Model.PatValid.nested` (through
`IsDefEq.uniq`, which the engine's transport lemmas use throughout) and the wave 4 stub
`WF.singletonInstance_align`, and on nothing else (`scripts/check-inductive-audit.py`).

## Cleanup 1

Behaviour-preserving cleanup; no statement changed.

* Deleted, nothing imported or used them: `Nested/Restoration/Validation/RecursorBinders.lean`
  (209 lines, a copy of `MajorHeads.lean`'s private lemmas), `Theory/Inductive/GuardedIotaLemmas.lean`
  (105), `Theory/Typing/TelescopeConversion.lean` (24), `Nested/Restoration/HeadTranslation.lean`
  (206), `Theory/Typing/InductiveParams.lean` (179; `Tests/IotaShape` imports `PatsIota`
  instead), `Theory/Typing/DefinitionRegistryInstallation.lean` (14, `VEnv.installDefinitions`).
* `Nested/Restoration/TranslationPreservation.lean` (1344 lines) cut to its consumed part: the
  projection-name lemmas are `Nested/Restoration/TranslationProjNames.lean` (69 lines) and
  `Expr.TrailingArgs` moved to its one consumer `LoweredRuleAvoidance.lean`; `restorationTranslates`,
  `RestoreTypedCtx` and the opening lemmas had no consumer.
* `RecursorData.installEntries`, `CompilationData.recursorEntries_lookup` and
  `RecursorRegistered.constant_exists` deleted (no consumer; the first was an audit root only).
* Duplicates merged (one public copy kept): `Nested/Restoration/SignatureVars.lean` (70 lines, a
  copy of `Theory/Typing/SignatureVars.lean`); `vars_length` and its variants (four copies) into
  `length_vars`; `VExpr.piBinders_wrapForalls`, `piBody_wrapForalls`, `piArity_wrapForalls`,
  `lamArity_wrapLams` into `Theory/VExpr/Telescope.lean` and `VExpr.bvarsDesc_succ_zero` into
  `Theory/VExpr.lean`; private `lamBody_wrapLams` copies replaced by `VExpr.lamBody_wrapLams`
  where it is imported; `find?_add_cases`/`Environment.find?_freshAdd_cases`/
  `find?_freshAdd_preserves` into `findAddFresh_cases`/`findAddFresh_of_find`;
  `IsDefEq.close_sort_header` into `UniqueTyping.lean`; `VInductDecl.RawCtorShape.constructorShape`
  into `RecursiveShapeCorrespondence.lean`; `VConstant.eq_of_fields` into `DeclarationData.lean`;
  `Restoration.expr_wrapLams` into `RestorationShapes.lean`.
* Moved: the model-side replay of `addInduct` from `Install/Rebase.lean` (452 to 231 lines) to
  `Theory/Inductive/AddInduct.lean` and `Theory/Typing/InductiveLemmas.lean`;
  `Theory/Inductive/RestorationNames.lean` (151 lines) folded into `Restoration.lean`.
* Process markers and provenance stripped from comments outside
  `Theory/Typing/HeadInjectivity/`; 31 unused imports dropped.

## Replay theorems (`Verify/Replay.lean`) and the restored tests

No stubs. `Verify/Replay.lean` proves `Replayed.foldlM`, `replayFresh.WF`, `replayFresh.WF_target`
and `replayPure.WF_fromImports` from the hypothesis-free `addDecl.WF` and `VEnvs.WF.empty`;
PR #53's `AddDeclChain`, `HasCanonicalEqType`/`hasCanonicalEqType_spec` and the `_mode`
variants are gone (the kernel's `checkEqType` replaces the driver's `Eq` check, and there is one
cache mode). The four theorems are audit roots; the three that rely on `addDecl.WF` reach the same three
accepted open proofs as `addDecl.WF`, and `Replayed.foldlM` reaches none. Every test is in
`Lean4Lean/Tests.lean`: `InductiveTheory` gives `enumDecl` its kernel recursor
and rule and proves the full structure `enumDecl.WF .empty` (including the `VEnv.PatTyped` rule
clause) and that `VEnv.addInduct` installs it; `TypedInductiveCompilation` installs the
container with `addInduct` and `RecsOf`; `CorruptRecursorMetadata` is stated against
`TrRecursorEntry` and `InductiveSignature.Models` (PR #53's `TrCompilation` does not exist
here).

## Confluence on the ι pattern calculus

`VEnv.WF.church_rosser` (`Theory/Typing/Confluence/WFParams.lean`): in a well-formed environment
with canonical `Eq`, definitionally equal terms reduce in the full presentation to normally equal
terms. It is PR #53's theorem with the ι rules read off `VEnv.pats`:

* **The engine** (`ChurchRosser`, `HeadReduction`, `FullReduction`, `LevelledReduction`,
  `FullChurchRosser`, `LevelledConfluence`, `PrefixUnfolding/`, `SingletonExtraction/`) is
  PR #53's without its case-schema steps. `IsDefEq.church_rosser` covers the `pat` rule
  through the class `FullPatCoverage`: every typed instance of a registered rule joins in the full
  presentation (coverage of each live pattern step instead of literal `pat_env` inclusion). The
  singleton prefix unfolding reads its equation through
  `VEnv.PatEquation` (the equation is realised at every typed instance of its extracted
  telescope) instead of a stored equation.
* **The parameters** (`WF.params`, `Confluence/Params.lean`): the recursor registry
  (`recursorRegistry`, `Confluence/Registry.lean`) chooses, for each name, the compilation data of
  the recursor of an installed declaration whose rules are exactly the registered patterns of that
  name (`RecursorEntry`; existence from `WF'.oneRecursor`: along the history the patterns of one
  head are the rules of one recursor); the pattern table (`ConcretePattern`,
  `Confluence/Patterns.lean`) is the δ rules of the registered definitions, the guarded quotient
  rule and the registered ι rules under the universe guard of their recursor
  (`GuardedIotaPattern`; soundness is `IsDefEq.pat`, so PR #53's `GeneratedIotaSoundness`, 1.2k
  lines, is gone). The non-overlap facts rest on the head separation of
  `Confluence/HeadSeparation.lean`; the structure facts on `WF'.structureCtorCoherent`
  (`Confluence/StructureMajor.lean`).
* **Coverage**: stored equations (`WF.equationCoverage`: δ rules by one pattern step, the quotient
  rule by `Confluence/QuotCoverage.lean`); registered ι rules (`WF.patCoverage`): one guarded
  pattern step where the source of the major is not `Prop` or the target is small, and the
  singleton prefix unfolding otherwise (`WF.singletonPatCoverageJ`,
  `Confluence/SingletonPatCoverage.lean`, through `RecursorRegistered.zero_join` of
  `Confluence/SingletonCoverage.lean` applied to the rule's generic equation, realised by the rule,
  `RecursorRegistered.patEquation_of_empty`).
* **Index alignment (route (b), closing the former stub `WF.singletonInstance_align`).** At a
  `Prop`-source singleton instance `rec A (c B)` the prefix unfolding reads the data fields off the
  index arguments, the rule's reduct off the constructor's fields; joining them needs the joins of
  the index arguments with the constructor's index expressions, which the typing of the major
  implies but no subderivation of `IsDefEq.pat` carries. The confluence induction is strengthened
  to joinable typings: `HasTypeJ` (`Confluence/JoinableTyping.lean`) is a typing whose
  applications and constants are syntax-directed and whose conversions are joins, and
  `IsDefEqStrong.church_rosserJ_of` proves both sides of every strong derivation (of any
  environment below the confluence environment) join and are joinably typed, given coverage of
  the rules at joinably typed instances (`FullPatCoverageJ`; `FullPatCoverageJ.toFull` recovers
  `FullPatCoverage`). Joins are stable under substitution and application and injective on
  Π-types (`Confluence/JoinLemmas.lean`) and on sort-typed rigid spines
  (`FullCRDefEq.rigid_spine_inv`, `Confluence/EtaSpine.lean`, through the reducts of a rigid
  spine, which function eta expansion of partial applications takes out of spine form); a
  joinable typing of an application spine joins its head's declared telescope
  (`Confluence/JoinTelescope.lean`). `singletonInstance_alignJ` (`Confluence/SingletonAlign.lean`)
  then aligns the instance with the generic equation, given the joins of the definitional
  equality of the constructor's declared type with its normalized type
  (`RestoresFamily.constructors`, a derivation in the environment the declaration's type formers
  are added to). Those come from the confluence of that earlier environment
  (`stage_types_joins`, `Confluence/StageJoins.lean`), so the coverage is proved by induction
  along a chosen history of the environment (`VEnv.WFH`, `VEnv.stages`,
  `Confluence/History.lean`; `WF.patCoverageJ`, `WF.stage_rank_lt`): the recursor registry is
  pinned to its stages (`RecursorEntry`), so the rules a stage registers are installed at earlier
  stages.

**Decisions.** PR #43's `ChurchRosser.lean` and `HeadReduction.lean` are replaced by PR #53's
engine: its `NormalEq.parRed` is sorry-free, so master's two `sorry`s are retired. PR #43's
small-environment instance (`toParams`, `DefEqsAsPats`, `inductParams`, `crDefEq_of_induct` in
`InductiveParams.lean`) is deleted: `WF.params` covers every well-formed environment, with
definitions and the quotient, which `DefEqsAsPats` excluded. The rest of `InductiveParams.lean`
(#43's non-overlap facts for `VEnv.pats`: `WF.pat_simple`, `WF.pat_uniq`, `WF.pat_app_l`,
`WF.pat_app_l_uniq`, `WF.pat_app_uniq`) had no consumer and is deleted too (see "Cleanup 1").
`VEnv.HasCanonicalEq` (`Theory/CanonicalEq.lean`) states the ι rule of `Eq.rec`
as a registered pattern whose reduct template `fun α a motive refl => refl` has free binder
domains (the rule never reads them); `Verify/CanonicalEq.lean` realizes it from the prelude
(`addDecl.preludeEq_hasCanonicalEq`, reading the rule off the kernel recursor through
`TrEnv.iotaRulesRegistered`, given the installed `Eq.refl`/`Eq.rec` metadata `IsPreludeEqReflVal`,
`IsPreludeEqRecVal`), which `Tests/PreludeEq` checks for `Init.Prelude`.

**Deviations from PR #53.** The confluence theorem is not sorry-free: it
inherits `patsStrong` and `Model.PatValid.iota` through `IsDefEq.uniq`, which the engine uses
(PR #53 had neither). `RecursorRegistered` records the typing of its compiled block
**Deviations from PORT_PLAN.** The confluence theorem is not sorry-free: besides the stub above it
inherits `patsStrong` and `Model.PatValid.nested` (formerly `Model.PatValid.iota`) through `IsDefEq.uniq`, which the engine uses (the
source branch had neither). `RecursorRegistered` records the typing of its compiled block
(`VInductBlock.WF`), and `RecursorRegisteredAt` fixes its installation.

**Edits outside the confluence files.** `Pattern.lean` (`Check.nonzero`, `OK.map_levels`,
`Check.Unguarded`), `Interpretation.lean` (the guard's cases),
`EqTyping.lean` (`Eq.rec`'s ι rule through `IsDefEq.pat`, `IsDefEq.canonicalEqRec_iota`),
`Experimental/SExpr.lean` (`defeqsS` skips the guard). Facts read from elsewhere:
`HeadInjectivity/Rules/Compiled.lean` (`iotaRHS_apply_of_matches`, `block_rules_wf`),
`HeadInjectivity/Model/WFFacts.lean` (`WF.quotMk_rigid`, `WF.quot_rigid`,
`WF.quot_not_projection`), `Verify/TypeChecker/CheckerEnv.lean` (`TrEnv.iotaRulesRegistered`).

**Audit.** `scripts/InductiveAudit.lean`, `scripts/check-inductive-audit.py`,
`scripts/inductive-audit-inventory.json`: the top-level theorems, the inductive pipelines, the
checker, `addDecl.preludeEq_hasCanonicalEq`, the confluence engine, and as strict roots (only the
three standard axioms) the generator definitions, the foundational lemmas and
`VEnv.WF.church_rosser` with `WF.params` and its coverage lemmas. The accepted open proofs are
`WF.patsStrong`, `IsDefEqU.weakN_iff` and `Model.PatValid.iota`;
`WF.patsStrong`, `IsDefEqU.weakN_iff`, `Model.PatValid.nested` and `WF.singletonInstance_align`;
`--require-complete` also rejects a listed proof no longer reached. CI runs `--self-test` and
`--no-build --require-complete`.

## The observation model on the ι pattern calculus

`VEnv.WF.chainHeadInjectivity` and `VEnv.WF.headSeparationModel` (`HeadInversion.lean`) are
theorems: `WF.chainHeadInjectivity_of_sound henv henv.soundEnv` and
`WF.headSeparation_of_sound henv henv.soundEnv`, with `VEnv.WF.soundEnv` from the history
induction `VEnv.WF'.envValid` (`Model/EnvValid.lean`). The model is
`Theory/Typing/HeadInjectivity/{Model,Projections,Rules}/` (22 model files, 4 projection
files, 3 rule files).

**Dependence on `patsStrong`.** The model interprets strong derivations and the extraction
strengthens the weak links of a `TypeChain` by `IsDefEq.strong` (`Model.chain_sub`,
`Model.spine_data`, `Model/Extract.lean`), which takes `VEnv.OrderedStrong` on this calculus;
the substitution theorems (`IsDefEq.substDF`, `IsDefEqStrong.substEq'`) and inversion lemmas
(`HasType.app_inv`, `HasType.const_inv`, `HasType.head_const_lookup`) the model uses take
`OrderedStrong` too. Every model lemma therefore takes `henv : env.OrderedStrong`, supplied by
`VEnv.WF.orderedStrong`, i.e. by `patsStrong`. The history induction uses nothing else from
`patsStrong`: it only ever strengthens derivations of the final environment and of the header
environments of projection entries (`ProjDeclAt`, which now records `envTypes.WF`), both through
`WF.orderedStrong`. A reorganisation that uses `patsStrong` on strict prefixes only would not
remove the use, because the extraction's input is a weak chain of the final environment.

**What changed from PR #53.** `Obs` loses `elimRule` and gains `pat` (`Model/Interp.lean`), of
the same `RuleBind` shape as the stored-rule clause `rule`, which stays for the quotient rule
(the one `defeqs` entry with a constructor major); the reduct template `rhs = wrapLams doms
body` is read off `SimplePattern.iotaRHS'`, the generic leading arguments are
`Model.iotaLead` (bound variables for parameters, motives and minors, then the constructor's
result indices) and the fields `Model.iotaFs`; the recursor's major domain
(`VExpr.RecShape`) supplies the family `I` and its levels `lsI` to the eta binding; in mode C
the clause records that the rule is the only pattern headed by its recursor. `IsCtor` reads
the constructor of a pattern (`VEnv.IsPatCtor`, `Rules/ConstructorMajor.lean`). `HTS`,
`HeadTy` and the spine lemmas are for constant heads only. `DeltaRules` gains a `pats` field
(no pattern is headed by a defined constant) and loses its inductive case (`addInduct` adds no
`defeqs`). `Model.sound` takes `PatValid` for the patterns of `E` (`Model/Sound.lean`);
`EnvValid` has fields `rule`, `proj`, `pat`. `Model/WFFacts.lean` proves the static facts
along the history: `WF'.defeqs_cases`, the quotient facts (`WF.quotConsts`, `WF.quot_rigid`,
`WF.quotMk_rigid`, `WF.quot_not_projection`), `WF.projStatic`, `WF.isCtor_rigid`,
`WF.installedCtor_resultRigid`, `WF.patCtor_rigid`. `EnvValid` carries `HeadsClosed` and
`PatsClosed` (no later declaration adds a rule or a pattern headed by an existing constant).
Dropped: `EnvTables/`, `Rules/{Coverage,RecursorEquations,RestoredRecursorEquations}`,
`Model/{CaseRule,CaseRuleSound,RecursorRule,RestoredRecursorRule,Singleton,FamSort,EmptyRule,
TeleArity,CtorArity,ProjMajorWF,ProjMajorRules,ProjStaticWF}` (eliminator registry and
stored-equation provenance); `IotaSoundnessLemmas.lean` is not needed (the stored-equation
detour collapses to `IsDefEq.pat`).

| statement | file | what remains |
|---|---|---|
| `VEnv.Model.PatValid.iota` | `Model/PatSound.lean` | The `pat` case of soundness for an instance `rec us args ≡ rhs us pmm fields` of a registered rule, from the semantic typing of redex and reduct (`HTS.spine`, `HTS.lamSpine`) and the static facts of the block: `VInductDecl.WF.rec_shape` (the `dsH`/`I`/`lsI` data of `Obs.pat`), `rules_ctor`, `PatsIota` and `rules_nodup` (uniqueness), the family's recorded sort (`FamSort`, `Model/FamSort.lean` on PR #53, from soundness of the environment before the block), proof binders of a singleton elimination (mode C, `Model/Singleton.lean` on PR #53), the projection entry of a structure family (eta mode). The two directions are `pat_lhs_sub`/`pat_rhs_sub_head` of `Model/RuleSound.lean` with the instance's spine in place of the λ-wrapped generic sides; `pat_rhs_sub_head` is already stated for an abstract head clause `hrule`. Estimated 1.5k to 2.5k lines. |
| ~~`VEnv.WF.patCtor_rigid`~~ (proved) | `Model/WFFacts.lean` | The constructor of a registered pattern is a constructor of its block or of a container block (`VInductDecl.RecsCompiled`, `VRecRule.OfEquation`, the compilation's `equation_major_cases`), hence rigid (`WF'.inductCtorRigid`). |


## Not ported or replaced

| item | where | why | status |
|---|---|---|---|
| `Theory/Typing/Confluence/**`, PR #53's `ChurchRosser`/`FullReduction`/`LevelledReduction`/`FullChurchRosser`/`HeadReduction`, `LevelledConfluence.lean`, `NormalSubstitution.lean`, `Inductive/{RecursorData,RecursorPrefixUnfolding,QuotPrefixUnfolding,RecursorEquationHeads,RecursorEquationCoverage,SingletonReconstruction}.lean`, `Typing/{RecursorRegistration,RecursorRuleRegistration,RecursorRegistryInstallation,StoredRuleHeads,PatternCaptures,DefinitionPatterns,QuotLiftTelescope,QuotPropInhabitant,ConstructorRigidity,RecursorMajorFamily}.lean`, `PrefixUnfolding/`, `SingletonExtraction/` | ported, except the case-schema files and `GeneratedIotaSoundness`/`RegistryOfWF`/`DefinitionHistory`, replaced by `Confluence/{Registry,HeadSeparation,Patterns}.lean` | see the confluence section | done |
| `Theory/Typing/HeadInjectivity/{Model,Rules,Projections}/**`, `EnvTables/`, `Typing/IotaSoundnessLemmas.lean` | PR #53 | the observation model; `EnvTables/` and `IotaSoundnessLemmas.lean` dropped | see the observation-model section |
| `Theory/Typing/Interpretation.lean`, `Inductive/RestorationInterpretation.lean`, `Typing/RestorationShapes.lean`, `Inductive/RestorationHead.lean` | ported with `PatClause` in place of the eliminator clause; see the nested-interface section | | done |
| `Theory/Typing/Strengthening/**` | PR #53 | dropped: master's `IsDefEqU.weakN_iff` is the one strengthening principle | not ported |
| `Inductive/Case*.lean`, `CaseSchema*`, `ProjNamesAvoid`, `RestorationProjNames`, `Typing/{CaseReduction,CaseMotive,CaseSourceSort,CaseMajorDomain,EliminatorCoherence*,SchemaStructCompat,EliminatorRestorationScope,ProjNamesTyping,ProjectionFamilyArity,ProjectionConstructorFamily,SignatureVars}.lean` | PR #53 | the case-eliminator registry, dropped with `VExpr.elim` | not ported |
| PR #43's `ChurchRosser.lean`, `HeadReduction.lean`, `InductiveParams.lean` | replaced | the engine files are replaced by PR #53's; `InductiveParams.lean` is deleted | done |

## Not a stub: hypotheses of the declaration judgment

`VInductDecl.WF` (`Theory/Inductive.lean`) keeps the recursor typing (`recs_wf`), the rule
typing (`rules_wf : VEnv.PatTyped`), the recursor shapes (`rec_shape`, `rule_shape`,
`rules_nodup`) and the constructor-constant clause (`rules_ctor`) as *fields* discharged by
the checker verification, not as theorems of `RecsCompiled`. Deriving `rules_wf` from the
typing of the generated λ-wrapped equations needs uniqueness and Π-injectivity, both
conditional on open proofs; the checker verification discharges the field directly from
`generatorEquationWF`.

## Executable, tests, divergences

No stubs: the executable and test ports add no `sorry`. `Lean4Lean/Tests.lean` is the manifest
of the `Lean4Lean.Tests` library (which no longer globs `Lean4Lean/Tests/`); every test is
imported there.

| test | needs | status |
|---|---|---|
| `AmbientContext` (PR #43) | `Verify.TypeChecker` | restored |
| closed-form and translation checks of `QuotInit` (removed from the ported test) | `Verify.Environment` (`Environment.addQuot_eq`, `VEnv.addQuot`) | restored |
| `InductiveTheory`, `TypedInductiveCompilation` | re-expression for the structure `VInductDecl.WF` and `VEnv.pats` | restored |
| `CorruptRecursorMetadata` | `Verify.Inductive.Recursor` | restored |
| `CorruptRestoredRecursorMetadata` | `Verify.Inductive.Nested` | restored |
| `RecursiveFieldClassification` | `Theory.Typing.Interpretation` | restored |
| `PreludeEq` | `Verify.Inductive.Prelude.EqSyntax`; `VEnv.HasCanonicalEq` only for confluence | restored |
| `CacheMode`, `SyntacticTranslation` | dropped with the scoped cache mode and the strengthening study | not ported |

## Environment model (`Verify/Environment/**`)

No `sorry` in `Lean4Lean/Verify/Environment/**`, `Verify/Environment.lean` or `Verify.lean`.

| statement | file | kind | status |
|---|---|---|---|
| `InductiveDeclPreserves` | `Verify/Environment.lean` | named hypothesis of `addDecl.WF_of` (not a `sorry`): a checked inductive declaration, at any fuel, preserves `VEnvs.WF` and extends every safety level | proved: `inductiveDeclPreserves` (`addInductiveDeclaration.WF_preserves`) |

Interface notes:

- `VEnvs`, `VEnvs.WF` (now with `blocks : InstalledBlocks safety env (ves.venv safety) .complete`),
  `VEnvs.axiom_of_choice` and `VEnvAt` live in `Verify/Environment/Model.lean`;
  `Verify/TypeChecker.lean` imports it.
- `RecursorAlignment.lean` is gone. `Verify/Environment/RecursorCoherence.lean` keeps
  `KLikeAlignment`, `KLikeRecursor`, `QuotCoherent`, `QuotEnvCoherent`; `RecursorRulesCoherent`
  is the K clause only; `EquationHeadsCoherent` is a structure with `defeqs` (as before) and
  `pats` (every registered pattern is headed by a recursor of the map), so `rigid`,
  `rigid_quot` and `rigid_of_fresh` give the two-field `VEnv.Rigid`. The ι rule the checker
  fires is `TrEnv.pats_iota'` (PR #43), which already reads `ctorParams` off the constructor's
  own `ctorInfo` and so covers nested auxiliary recursors.
- `CheckingEnv.Valid` has no `ctorTelescopes`; `InstalledBlock` has no `eliminators` and no
  constructor telescope; `InstalledBlocks.addInduct` takes `decl.WF venv ∧ venv.addInduct decl =
  some venv'` and the K clause of the new recursors (`hrecK`) instead of the old `AddInduct`.
- `AddInduct` (PR #43's structure) has the projection stage: `stR : decl.addRecs (decl.addProjs
  envC) = some envR`, `AddInduct.envP`, `addTypesCtorsProjs`, `addTypesCtorsProjsRecs`.
  `AddInduct.ctor_find` no longer concludes `ctorParams = numParams` (false for nested blocks).
- `TrEnv'` gains `inductProjections` (the projection stage, premise `(env.addProjections
  entries).WF`), and `empty` is either map stage.

Found while porting (since fixed, see the inductive-interface section):

- `VEnv.InstalledBelow` (`Theory/Inductive.lean`) installed a block through
  `VInductBlock.install`, which adds the generated rules as stored equations (`defeqs`). No
  environment built by `VEnv.addInduct` contains them, so `InstalledBelow` failed for every
  container with at least one generated rule in the environments the checker builds, and with
  it `VInductDecl.NestedFormationWF` (which requires the container to be `InstalledBelow`). The
  installed-blocks invariant uses `VEnv.InductInstalled venv decl := ∃ base installed,
  decl.WF base ∧ base.addInduct decl = some installed ∧ installed ≤ venv`
  (`Verify/Environment/Blocks.lean`) instead; `InstalledBelow` is now restated on `addInduct`.

Not ported:

| item | why | status |
|---|---|---|
| `Verify/CanonicalEq.lean` | needs `Verify/Inductive/Prelude/EqSyntax.lean` and a `VEnv.HasCanonicalEq` whose `Eq.rec` rule is a pattern; `addDecl.WF` no longer needs it | restored |
| `Verify/QuotInit.lean` | replaced by PR #43's `Verify/Environment/Quot.lean` | not ported |

## Header phase (`Context.lean`, `Context/**`, `Formation.lean`, `Header/**`)

Proved: `AddInductive.checkInductiveTypes.WF`, `CheckedHeaders.Describes.headerCertificate`,
`AddInductive.declareInductiveTypes.WF`, `TrInductDeclCore.sourceNames_nodup`. No `sorry` in
`Context.lean`, `Context/**`, `Header/**` or `Formation.lean`.

Two corrections of the header interface (both were false as first stated):

* `HeaderParameterContext.paramsTr` placed the parameter variables at `.bvar i`; the
  continuation of `checkInductiveTypes` runs beneath the index binders of every family (the loop
  nests them), so they are `.bvar (depth + i)`.
* `declareInductiveTypes.WF` takes `decl.isUnsafe = isUnsafe` beside `Describes` (which does not
  constrain `isUnsafe`), since `HeaderEnvironment.isUnsafe` asserts it.

Statement of a boundary theorem: `AddInductive.declareInductiveTypes.WF` as first stated was
false. Its postcondition built a `ContextWF` over the header environment, whose
`CheckingEnv.Valid` needs every name a header lists to be absent or a constructor of that
header, but `declareInductiveTypes` only checks the header names (a source constructor named
like an existing definition, or like a family of the same block, passes it). The executable
checks constructor names only in `declareConstructors`, after `checkConstructors`. The
postcondition is now `headerEnv.constants.WF ∧ (ConstructorNamesAbsent indTypes headerEnv → ∀
decl, Describes → Nonempty HeaderEnvironment)`, as PR #53's
`declareInductiveTypes.headersWF`; the consumer (`constructorPhase.WF`) obtains
`ConstructorNamesAbsent` from a successful `declareConstructors`
(`AddInductive.declareConstructors.namesAbsent`, `Header/Installation.lean`), as PR #53's
`formationCoreWF` does (case on `checkConstructors`, then on `declareConstructors`).

Fields of the header interface: `CheckedHeader.formation`
(the loop's `HeaderFormation`); `HeaderPhase.{loopHeaders, headers_eq, cache, suffix,
ambientParams}` (the loop's accumulator and parameter invariants); `HeaderEnvironment.
{sourceStatsWF, sourceHeaderParams, statsWF, headerParams, parameterScopeEq}` (`HeaderStatsWF`,
built by `HeaderPhase.statsWF` for every described declaration);
`ContextSemantics`/`RecursorContextWF` carry `shapes`/`iota` in place of the cache mode, with
`RecursorContextWF.checkerEnv`. `InstalledHeaders` and
`AddInductive.declareInductiveTypes.installedWF` (the header environment before the declaration
is known, as PR #53's `declareInductiveTypes.headersWF`), `InstalledHeaders.toHeaderEnvironment`.
`declareRecursors.checkRecursorType.WF` (`Context.lean`) takes a `CheckerEnv` and no cache
mode. PR #53's top-level `TypeAnnotations.lean` is `Context/TypeAnnotations.lean`; the
helpers PR #53 kept in `Theory/Typing/IotaSoundnessLemmas.lean` and used here
(`VerifyInductive.VExpr.takeForalls_rebuild`) are in `Formation.lean`, with the rest of
PR #53's `Formation.lean` (`IndexedPrefix`, `List.Forall₂.targets_eq_of_unique`,
`VEnv.addConstVals_append`, ...).

## Constructor phase (`Verify/Inductive/Constructor/**`)

Proved: `CheckedFormation.signature`, `AddInductive.constructorPhase.WF`. No `sorry` in
`Constructor/**`.

* `CheckedFormation.signature`: the family table is read off the header certificate's type
  shapes (`HeaderCertificate.familyTelescope`), the constructors off the checked tails
  (`CheckedFormation.tails`). The empty declaration gets the empty signature.
* `constructorPhase.WF`: `declareInductiveTypes.installedWF` (header), then the constructor check
  `AddInductive.checkConstructors.WF` (`Constructor/CheckRun.lean`: the declaration is the one
  whose constructor types are the raw translations of the run, `accumulatesRawTargets`; the
  certificates come from `checkConstructors.loopTypes.refinesChecked` and
  `loopTypes.ownerNormalFormsWF`), then `declareConstructors` (`Constructor/Declare.lean`:
  `insertConsts` of the `constructorInfo`s, fresh, distinct, nonprimitive) and the constructor
  environment (`Constructor/Install.lean`: `CheckingEnv.Valid` via
  `InstalledBlocks.addCtorStage`, recursor shapes and ι rules, projection-stage `WF` via
  `VEnv.WF.inductProjections`, closure, `InductInfosFromDecl`, parameter alignment).

Statement changes: `constructorPhase.WF`'s postcondition is `∃ R : ConstructorCheck …, R.classes
= out.2` (the first form `Nonempty … ∧ ∀ R, R.classes = out.2` was unprovable: nothing pins an
arbitrary `R`'s classes); `Install/Ordinary.lean` adapted.
`RecursorInput.constructorTails` is stated over `headers.statsWF.parameterScope`. Fields:
`CheckedFormation.tails`; `ConstructorCheck.{ivals_eq, ctor_numParams, parameterPrefixes,
constructorTails, ownerNormalForms}`. Definitions the recursor phase imports from
`Constructor/Tails.lean`: `ParameterPrefix`, `ParameterSegment`,
`Expr.ForallSpine`, `CheckedConstructorParameterPrefix`, `ConstructorParameterPrefixes`,
`CheckedConstructorTailAt`, `ConstructorTails`, `ConstructorOwnerNormalForm(At/s)`,
`ConstructorScopedTelescope` (= the header's `ScopedHeaderTelescope`).
`Constructor/OwnerNormalForms.lean` imports `Recursor/Context/FVarArrays.lean` (whose import
closure stays inside `Constructor/{Tails,Positivity,PrefixUtilities,CheckedFormation,
SourceSignature}`). PR #53's `Header/Declaration.lean` is not ported: `CheckedHeaders.declOf`
selects the declaration from the checked headers and the raw constructor rows.

## Recursor phase (`Verify/Inductive/Recursor/**`, `Rules/RuleSyntax.lean`, `Rules/FromTemplates.lean`)

Proved: `RecursorInput.recursorPhasesWF` (the boundary theorem) and
`InductiveSignature.VRecRule.OfEquation.ofTr`. `Recursor/**` contains no `sorry`; the boundary
theorem's only `sorryAx` sources are the accepted open proofs `VEnv.WF.patsStrong`,
`VEnv.Model.PatValid.iota`, `VEnv.IsDefEqU.weakN_iff`. Ported: PR #53's `Recursor/**` (65 files,
about 41.8k lines) and `Rules/{RuleSyntax,FromTemplates}` (2.5k; they sit inside the recursor
chain).

Structure: `RecursorInstallation` (`Recursor/Installation.lean`) is PR #53's
`RecursorCheck` (extends `RecursorConstruction`), produced by `RecursorInput.recursorInstallationWF`
(PR #53's run theorem); `Recursor/Recs.lean` reads the kernel recursors `rvals` and the model
recursors `recs` (rules: `ctorParams := decl.nparams`, `rhs :=` the generated equation's) off it,
with every shape clause of `VInductDecl.WF`; `Recursor/Checking.lean` proves the checking
invariant at the recursor stage (`InstalledBlocks.addCtorStage` from the source blocks,
`recursorShapesOf`); `RecursorInstallation.toRecursorCheck` (`Recursor/Check.lean`) assembles the
`RecursorCheck` interface. The rule coverage is the rule phase's `RecursorInstallation.rulesCovered`
(`Rules/Coverage.lean`).

Interface changes:
* `RecursorCheck` gained `installation : RecursorInstallation R outEnv` with
  `installation_{elimLevel,kTarget,outVEnv,rvals,signature,generation,recs,rvals'}` and
  `rules_ctorParams`.
* `RecursorCheck.trRecs` and PR #43's `AddInduct.recs` translate recursor types in the projection
  stage (`R.envP`, `decl.addProjs envC`), where the executable checks them
  (`Verify/Environment/Basic.lean`, `Verify/Environment/Lemmas.lean`, `Install/Rebase.lean`).
* `VRecRule.OfEquation.ofTr` takes the index-count side condition `harity`
  (`Models.constructorArity`); `ofTrModels` discharges it from a modelling signature.
* `RecursorInput.literalDisjoint` supplies positivity's literal side condition.

Recursor-side homes of content that lived elsewhere in PR #53:
`Recursor/Inputs.lean` (PR #53's `ConstructorCheck`'s header-side members on `RecursorInput`:
`sourceContext`, `statsWF`, `parameterScope`, `recursorHeaders`, `headerLE`/`ctorLE`/`sourceLE`,
`find?_origin`, `headerInfo_find`, `ctorInfo_find`, `modelCtorAt`), `Recursor/SourceAlignment.lean`,
`Recursor/Signature/RecursorTypeTelescope.lean` (from `Nested/Restoration/ExprReplace`),
`Recursor/Signature/SourceReplay.lean` (the replay-based source signature of PR #53's
`Constructor/{SourceSignature,CheckedFormation}`), `Recursor/Entries/Metadata.lean` (from
`Install/Metadata`). Dropped: the case-eliminator and telescope-certificate lemmas
(`addEliminators`, `SourceCtorsCertified`, `CtorTelescopeAt`), `RecursorCheck.alignmentOfTr`
(replaced by `recursorShapesOf`), the old `AtomicAddConstants` helpers; the constructor
loop's production (owner normal forms, parameter prefixes) moved to `Constructor/**`.

## Rule phase (`Verify/Inductive/Rules/**`)

`RecursorCheck.generatedRuleTranslation` is proved. PR #53's `Rules/**` is ported onto
the recursor installation (`RecursorInstallation`, PR #53's `RecursorCheck`): `Rules/{Alignment,
MinorContext,MinorPremise,Motive,RecursiveCallScope,RecursiveCall,RecursiveApplication,
EquationTranslation,RecursiveBody,RecursiveResults,Rhs,Lhs,EquationWF,LhsTranslation,Translation}`,
with the assembly in `Rules/Coverage.lean` (`RecursorInstallation.rulesCovered`, which the recursor
phase uses to build `TrRecursor`, and `equationsWF'`). Support from other PR #53
directories: `ContextLemmas.lean` (`rebaseCommonSuffix`, from `Install/Lookups`),
`SameForallPrefix.lean` (from `Nested/Restoration/ParameterOpening` and
`Nested/Lowering/ParameterOpening`), `InstallationLemmas.lean` (from `Install/BlockCertificate`).
`rules_wf : PatTyped` is the restatement of the generated equations' `VDefEq.WF`
(`Instance.equation_patTyped`, `Rules/IotaPatTyped.lean`; `RecursorCheck.rules_wf_of`,
`Rules/RulesWF.lean`). `RecursorCheck.rules_ofEquation` gives `VInductDecl.RecsOf`'s rule clauses.
Foundation changes met in the port: `.ordered` → `.orderedStrong` where `TrExprS.weakBV`/
`VLCtx.IsDefEq.refl` now take `OrderedStrong`; constructor lookup through `R.core.ctorsAdded`.
The rule chain's only `sorryAx` dependencies are the accepted open proofs `VEnv.WF.patsStrong`,
`Model.PatValid.iota`, `IsDefEqU.weakN_iff`.

No `sorry` in `Rules/**`. `RecursorCheck.rulesCovered`/`equationsWF` are read off the
installation (`installation_*`); `ruleCtorParams` is the recursor phase's `rules_ctorParams` with
`models.nparams`.

`Rules/RuleSyntax.lean` and `Rules/FromTemplates.lean` belong to the recursor chain (PR #53's
`Recursor/**` imports them).

## Installation (`Install/**`, `Primitive/**`, `Prelude/**`, derived `RuleTranslations` facts)

No `sorry` in the install/primitive/prelude directories. Proved: `BlockCertificate.installedBlocks`
(`hpres`), `rebase`, `extendSafeExact`, `extendUnsafeExact`, `RecursorCheck.blockCertificate`,
`Kernel.Environment.checkDuplicatedUnivParams.WF`, `RuleTranslations.blockWF`/`compilesTo`/`recsOf`
(`recsOf` through the rule phase's `rules_ofEquation`), `ConstructorCertificate.withRecs`,
`checkPrimitiveInductive_eq_true_iff`, `loweringRun.primitiveNoop`, the recursor-names-not-primitive
fact, `AddInductive.constructorPhase.primitiveWF`, and `VEnvAt.recursorShapes`
(`Verify/TypeChecker.lean`, read off the installed-block descriptors). `Prelude/{EqSyntax,EqReady,Eq}`
are ported (the `QuotReady` half: `Environment.addInductive.preludeEqExtensionWF`; the
`HasCanonicalEq` half is `Verify/CanonicalEq.lean` with `Tests/PreludeEq`).

Interface changes:
* `Verify/Inductive/HeaderData.lean`: `LocalContextWF` (`ContextWF` with `checking :
  CheckingEnv`, no `HasPrimitives`/`shapes`/`iota`) and `HeaderData` (`HeaderEnvironment` with
  `context : LocalContextWF`, without the header context's `parameters`), `HeaderEnvironment.toData`.
  The header-only environment of `Bool`/`Nat` violates `HasPrimitives`, so no `ContextWF` exists there.
* `Verify/Inductive/RecursorInput.lean`: `RecursorInput` = `ConstructorCheck` with its
  `CheckedFormation` fields flattened under the same names and `headers : HeaderData`;
  `ConstructorCheck.toRecursorInput`, `CtorInstall.toRecursorInput`. `RecursorCheck`,
  `RuleTranslations`, `RecursorInput.recursorPhasesWF` (renamed from `ConstructorCheck.recursorPhasesWF`),
  `blockCertificate` and `OrdinaryInstallation` are indexed by `RecursorInput`.
* `Constructor/{Checked,Install}.lean`: `ConstructorsChecked` and `CtorInstall` are over `HeaderData`;
  `CtorInstall.nprim` is replaced by `hasPrimitives` (of the constructor model) and `safePrimitives`
  (of the constructor environment); the ordinary path proves both from nonprimitive names
  (`CtorInstall.ordinaryPrimitives`); shapes/iota/equation heads/quotients and the parameter context come
  from the source context. `Constructor/CheckRun.lean`: `checkConstructors.WF` concludes
  `ConstructorsChecked H.toData`.
* `Verify/Environment/Blocks.lean`: `RecursorShapes` moved here (from `TypeChecker/CheckerEnv.lean`);
  `InstalledBlock.WF` gains `shapes : ∀ r ∈ B.recursors, visible → RecursorShapesAt env.constants venv r`;
  `addBlock`/`addInduct` take `hrecShapes`, `addCtorStage` takes it as an auto-discharged argument.
  `InstalledBlocks.recursorShapesCoherent` (`TypeChecker/CheckerEnv.lean`).
* `RecursorInput`, `ConstructorCheck` and `CtorInstall` gain `literalDisjoint` (positivity's literal
  side condition, `AvailableLiteralDisjoint`, in the recursor phase's context).
* `BlockCertificate` gains `compiled` (a well-formed compiled block, for `rebase`), `newUnsafe` (inserted
  constants carry the declaration's `isUnsafe`) and `recShapes`; `rebase` takes `ves.WF env` and
  `decl.isUnsafe = false`. `RuleTranslations.compilesTo`/`recsCompiled`/`recursorsWF` take
  `indTypes.toList ≠ []`.

Every caller of `InstalledBlocks.addInduct` (including the nested installation) supplies
`hrecShapes`, i.e. `RecursorShapesAt` of each new recursor, auxiliary recursors included (their majors are
containers at specialized arguments, so `recursorShapesOf`, which reads the major off `MajorApp` and the
rules' constructors off the source declaration, does not cover them).

## Nested equations and installation (`Nested/Equations/**`, `Nested/Install/**`, two Theory lemmas)

Proved: `InductiveSignature.instantiateParams_liftN`, `VEnv.RestoredPattern.clause`,
`RestoredBlock.rulesWF`, `RestoredBlock.blockWF`, `RestoredBlock.installedFacts` (from
`kernelFacts`, below). The nested `InstalledBlocks.addInduct` call is inside
`installedFacts`. Its `hrecShapes` is `RestoredBlock.recShapes` and its `hrecK` is `recK` (both
cover every new recursor, auxiliary ones included). `BlockCertificate.compiled` is
`RestoredBlock.compiledWF` and `newUnsafe` is `RestoredBlock.newUnsafe`.

* `RestoredPattern.clause` gains three fields of `VEnv.RestoredPattern`: `wf : envS.WF`,
  `recursorNotHead`, and `templateTyped` (the interpreted reduct template is typed). The
  `PatClause` gives the typing of the interpreted redex only. The interpreted reduct is a
  β-*expansion* of the restored reduct, so its typing has to come from the template, and
  uniqueness of typing (`IsDefEq.uniq`, hence `wf`) turns the forward `SimAt` around. Nothing
  constructs a `RestoredPattern` yet. `rulesWF` does not need it: the substitution goes from the
  lowered *recursor* stage, which has no patterns of the block.
  Who constructs a `RestoredPattern`: nobody on the current
  route. It is needed only if a restoration substitution is built from a lowered environment
  that already registers the block's ι rules (the lowered rule stage or a later one). Its
  `PatClause` then has to be discharged per lowered rule, and whoever builds that
  substitution constructs it: `wf` from the target's `VEnv.WF`, `recursorNotHead` from
  `CompilationData.recursorName_not_head` (`RuleAlignment.lean`), and `templateTyped` from
  the typing of the interpreted template (`Restoration.equation_wf` on the lowered equation).
* `rulesWF` is `VEnv.patTyped_iota_of_wrapped` on the restored equation of each rule.
  `RestoredBlock.ruleEquation` (`Nested/Equations/RuleAlignment.lean`) recovers the exact
  ι counts from the restored generated equation (`rules_ofRestoredEquation`), the restored
  recursor type (`rec_shape`'s arity and motive-application conjuncts, *not* `MajorApp`) and
  the reduct's λ-arity (`rule_shape`). `envP_wf`/`envR_wf` (`Rules.lean`) are proved from the
  restored block's fields.
* `installedFacts` takes `TrEnv c.safety c.env Hc.venv`, the base's
  complete `InstalledBlocks`, and its `ConstructorParameterAlignment`.
  `Nested/Install/Dispatch.lean` passes `wf.tr wf.blocks wf.constructorParameterAlignment`.
  `ContextWF` has the blocks at `.headers` only, which `InstalledBlocks.addInduct` cannot
  extend.

| statement | file | how it is proved |
|---|---|---|
| ~~`RestoredBlock.restoredEquationsWF`~~ (proved) | `Nested/Equations/Rules.lean` | A `RestoredBlock` field, produced in `nestedRestoredBlock` from `NestedRun.hrestoredWF_of` (`Nested/Restoration/Equations/RestoredWF.lean`): the restoration substitution (`Equations/WF.lean`, without eliminators), the projection-name premises (`Equations/ProjNames.lean`, `Equations/ProjNamesAvoid.lean`), the auxiliary constructor lambdas (`Equations/AuxiliaryConstructors.lean`), the projection clauses of `AuxiliaryProjections.lean`. |
| ~~`RestoredBlock.kernelFacts`~~ (proved) | `Nested/Install/Installed.lean` | `constructorOwnersPresent`, `inductInfosFromDecl` (for `runDecl`, carried along `run_decl`), `mutualInductivesClosed` (given the base's closure, from its complete blocks), `primitives`; `recMajor` and `constructorParameterAlignment` are `RestoredBlock` fields. `ConstructorCoherence.lean`'s `FoldSteps.restoredSourceMemberInfos` and `sourceTypeNames` are public for it. |

`VExpr.RecShape`'s `MajorApp` conjunct (`VInductDecl.WF.rec_shape`,
`RestoredBlock.rec_shape`) was false for the auxiliary recursors of a nested block: their major
is the container applied to the specialization arguments, not to parameter variables.
`MajorApp` is weakened to a head family constant applied to parameter-closed arguments
followed by index variables. `ruleEquation` uses only the arity and motive-application
conjuncts, so it is unaffected.

`InductInstalled` records the compiled block
(`∃ block, decl.CompilesTo base block ∧ decl.RecsOf block ∧ block.WF base`, in
`Verify/Environment/Blocks.lean`). The `InstalledBlocks.addInduct` call in `installedFacts`
supplies it from `RestoredBlock.compiledWF`.

## Nested restoration (`Nested/Restoration/**` outside `Validation/`, `Uniform/`; `CompilationMajors.lean`)

Proved: `Instance.restored_equation_major`, `CompilationData.constructor_name_cases`,
`ContainersInstalled.constructor_isPatCtor`, `CompiledInductive.rule_ctor_cases`
(`Theory/Inductive/CompilationMajors.lean`, no `sorry`; with the ported helpers
`Restoration.expr_wrapLams_parts`, `headName_of_mem`, `CompilationData.headName_source`,
`CaseCompilationData.headName_auxiliary_constructor`/`directFamily_restored_constructor_names`,
`CompilationData.constructor_equation`, `CompiledInductive.constructor_equation`/
`equation_major_cases`, `VDefEq.HasConstructorMajor.ofEquation`).

The restoration is one dependency chain, ported in PR #53's topological order: besides
`Nested/Restoration/**` (minus `Validation/{Checks,Stripped*,ParameterPrefix,ParameterScopes,
Result}` and `Uniform/**`) also PR #53's
`Install/{AddInduct,FromRun,Certificate,RunView,Permutation,DependencyOrder,RecursorTranslations,
ConstructorCoherence}`, `Equations/{SourceIotaFamilies,SourceIota,RuleRhs}` and the translation
half of `Equations/{RestoredRules,GeneratedGuard}` (PR #53's paths and names kept); the side
environments' models (PR #53's `Validation/{Environment,ConstructorEnvironment}`) live in
`Nested/Restoration/SideEnvironment/`. `Nested/Equations/**` and `Nested/Install/**` keep the
typing side.

`VExpr.RecShape` was false for nested blocks as inherited from #43 (same family as
`rules_own_params`/`rec_counts`/`recs_over_block`): its `MajorApp` required the major's leading
arguments to be the recursor's parameter variables, which a restored auxiliary recursor
(`Tree.rec_1`, major `List (Tree α)`) violates. `MajorApp` is weakened
(`MajorApp.of_params` is the old shape; Tests/IotaShape's
`Tree.rec_1` control now expects acceptance). Its consequence: nothing
pinned the split of a registered rule's arity into constructor parameters and fields any more;
hence the field `VInductDecl.WF.rules_ctorParams` (own constructors at `decl.nparams`,
or a container `D` with `InstalledBelow env D` at `D.nparams`), produced by the ordinary recursor
phase (`RecursorCheck.rules_own`), the rebase, and `RestoredBlock.rules_ctorParams`.

Ported (PR #53's names kept; `NestedRun` in `Restoration/Run.lean` with PR #53's signature,
its lowered run as `LoweredView`): Steps, RecursorTelescopes, FreshExtensions,
ConstructorTranslations, Translations, Nonprimitive, Tables, TrRestoredRecursorVal, RecursorShape,
AuxiliaryRecursorsWF, Install/Permutation, Lookups (with target-native `LoweredLookups`),
KernelData (new: fold entries, `FreshExtension.map_eq`, `entries_perm`), LoweringRestoration,
SourceTranslations, SourceValidation, InstalledFamilyLookups, Install/DependencyOrder,
SideEnvironment/{Environment,ConstructorEnvironment}, SourceHeaders, SourceDeclaration,
ContainerSpecializations, CompilationData, SourceConstructors, Commutation, ExpansionInverse,
CommutationUniform, TranslationProjNames, Levels (part), RestoredShapes (new: the restored
`rec_shape`/`rule_shape`/closedness), plus Verify-side copies of PR #53's Theory
IotaSoundnessLemmas/ProjNamesOK. The registered ι rules are fixed by the
restoration interpretations (`VEnv.WF.pats_fixed_of_avoid`, `Nested/Restoration/PatsFixed.lean`,
from the model's `VEnv.WF'.patsAvoidFreshConsts` and `pats_origin`).

`nestedRestoredBlock` (`Restore.lean`) is assembled with no `sorry` of its own:
`NestedRun.ofRestoration` (the run of the restoration), `NestedRun.sourceParameterWF`,
`NestedRun.assemblyBase` (the rule-free `RestoredBlockBase` and the kernel-order permutation),
`NestedRestorationFolds.kernelOrder`, `NestedRun.trTypes`/`newUnsafe` (`AssemblyTypes`),
`NestedRun.recMajor`/`constructorParameterAlignment` (`AssemblyKernel`),
`NestedRun.strippedChecker` (`StrippedFacts`, over `RuleFree`), `NestedRun.assemblyRecursors`
(`AssemblyRecursors`, consuming `NestedRun.hrestoredWF_of`), and the
`HEq` casts of `ViewCast`.

Fields of `RestoredBlock`: `rules_ctorParams`, `runDecl`, `run`, `run_decl`,
`sourceSyntaxChecked`, `constructorArityPrefix`, `run_loweredEnv`, `run_lowered` (the run object
read by `Nested/Equations/**` and `Nested/Install/**`), `recMajor`, `constructorParameterAlignment`
(for `kernelFacts`), and `restoredEquationsWF` (formerly a theorem of `Rules.lean`).

The stripped environment: `AddInduct.map_eq` is a structural `ConstMap` equality and
`stripRecursorRules` re-inserts each recursor, so no `AddInduct` lands in the stripped map. The
rule-free stage is built over `insertConsts` of the stripped entries, and transported along
lookups by `CheckingEnv.Valid.mapExt`/`CheckerEnv.mapExt` (`Nested/Install/Permutation.lean`);
`stripRecursorRules.checkingValid`/`checkerEnv` are stated accordingly.

No `sorry` in `Nested/Restoration/**` or `CompilationMajors.lean`.
`nestedRestoredBlock` depends on `sorryAx` only through the accepted open proofs
(`VEnv.WF.patsStrong`, `VEnv.Model.PatValid.iota`, `VEnv.IsDefEqU.weakN_iff`).

The container constructors' kernel listing is not derivable from abstract `InstalledBelow`
(two installed declarations may share a family name with different constructors), so the
lowering keeps it: the field `AuxiliaryFamilySource.containerKernel`
(`Lowering/Expansion/AuxiliarySources.lean`), carried as the last conjunct of
`NestedRun.restorationTablesRestoringAll`.

## Restoration validation and uniformity (`Nested/Restoration/{Validation,Uniform}/**`)

Proved: the seven statements of `Validation/Passes.lean`; no `sorry`. `Validation/**` and
`Uniform/**` are 5.8k lines over 15 files. Three statements carry premises the first
statements lacked, because the passes run the checker without checking them or because the
first form was circular:

* `validateSourceConstructorTypes.run.WF` takes the closedness of the constructor types
  (`SourceSyntaxChecks.ctorTypesClosed`, `Validation/Checks.lean`).
* `validateNestedAuxiliaries.WF` (and `.WF_typing`, keeping the inferred types, PR #53's
  `NestedOccurrencesTyped`) take the checker context `mlctx` of the lowering's parameters;
  `NestedLoweringOutput.parameterMLCtx` (`Validation/ParameterPrefix.lean`, from
  `params_opening` with `LoweringParamOpening.toMLCtx`) supplies it.
* `stripRecursorRules.checkingValid`/`.checkerEnv` are stated over a rule-free `AddInduct` into
  an environment `S` whose lookups and `quotInit` agree with the stripped map's
  (`CheckingEnv.Valid.mapExt`/`CheckerEnv.mapExt`), with the rule-free facts `RuleFreeStage`
  (`Validation/Stripped.lean`): the projection stage's `VEnv.WF`, the recursor types, the
  block's names not primitive, the restored header facts, the K clause and shapes of the new
  recursors at the recursor stage (`RecursorShapesAt.stripRules`, `KLikeRecursor.of_k_false`
  derive the last two from `RestoredBlock.recShapes` and `k = false`). They are produced in
  `Restoration/RuleFree.lean` and `AssemblyBase.lean`.

Also ported: `Uniform/{Recursors,Generic,Heads,Base,Lowered,Run,Whnf,Declarations,
RunEnv}.lean` (the parameter uniformity of the lowered recursors, ending in
`NestedRun.recursorParamUniform_of_wfCore`, read by `Restoration/{Recursors,RecursorRenaming,
MajorHeads,LoweredRuleAvoidance}`, `Equations/{RuleRhs,ProjNames}`; `normalizedTotal_of` by
`CompilationDataConstructors`, `RecursorTranslations`), `Validation/ParameterScopes.lean`
(read by `AssemblyKernel`, `Install/Installed`). Not ported:
PR #53's `Validation/Result.lean` (superseded by `RestorationRun`), `Validation/{Environment,
ConstructorEnvironment}` (in `SideEnvironment/`), the `NestedRun` part of
`StrippedRecursorShapes` (replaced by the two lemmas above). The lowered names'
non-primitivity is the field `NestedRun.loweredNonprimitive`.

## Nested lowering

Statement changes to `NestedLoweringOutput`/`loweringRun.WF` (`Verify/Inductive/Lowering.lean`):

1. `loweringRun.WF` takes `wf : ves.WF env`: `nested_app`'s `FVarsIn` and the container
   parameter count of a sibling `J ∈ I.all` need `EnvironmentTypesClosed`/`MutualInductivesClosed`
   (auxiliary constructor types instantiate kernel constructor types). The ordinary branch's
   consequences (`loweringRun.types_nonempty`, `loweringRun.ordinary_types_eq_source`) stay
   hypothesis-free through `loweringRun.sourceShape`.
2. `lctx_params` reads `res.params.toList.reverse.map (·.fvarId!) = res.lctx.fvars`
   (`LocalContext.fvars` is most recent first).
3. `aux_fresh` is `env.find? t.name = none ∧ ∃ i, t.name = .num `_nested i`; field
   `aux_ctor_names` (an auxiliary constructor is a container constructor renamed under the
   auxiliary family). Disjointness from the source family names (a source family may be named
   `_nested.1`) and constructor freshness (kernel constructor names need not extend their
   family's name) are not lowering facts; they come from the lowered installation.
4. `restore_source`'s premise `LoweredAuxiliariesInstalled` is replaced by
   `RestoreSourceDisjoint res loweredEnv sc.type` per source constructor (PR #53's
   premise; `LoweredAuxiliariesInstalled` does not exclude a source constant registered in
   `loweredEnv` as a constructor of an auxiliary family). The restoration establishes it from the
   lowered installation (`RestoreAuxConstructorsFresh`, `AddConstants`).
5. `loweringRun.WF` also takes `hsources : SourceSyntaxChecks env types`, and
   `loweringRun.types_nonempty`/`loweringRun.ordinary_types_eq_source` take `wf` and `hsources`
   (`Dispatch.lean`'s two calls and the nested dispatch updated): the ported refinement
   (`ElimNestedInductive.run'.translationClosed`) carries a closing context that exists only for
   closed source types.
6. Fields: `params_opening` (the parameter opening of the first source header, for the
   parameter metacontext of `validateNestedAuxiliaries.WF`, PR #53's `resultParameterMLCtx`) and
   `closed : NestedLoweringOutputClosed …` (PR #53's run relation, so restoration
   lemmas port verbatim). `SourceBVarClosed` and `RestoreSourceDisjoint` are defined in
   `Nested/Lowering/Refinement.lean` (imported by `Lowering.lean`); PR #53's
   `NestedLoweringOutput` def is `NestedLoweringRun` (`Nested/Lowering/Output.lean`), its inductive
   `SourceSyntaxChecks` is `SourceSyntaxChecked`.

7. `VEnv.InductInstalled` (`Verify/Environment/Blocks.lean`) also records
   a well-formed compiled block of the declaration (`∃ block, decl.CompilesTo base block ∧
   decl.RecsOf block ∧ block.WF base`), so that an installed declaration is a container of
   nested formation (`VEnv.InductInstalled.installedBelow : … → VEnv.InstalledBelow venv decl`).
   `InstalledBlocks.addInduct`'s `hadd` and `VEnv.InductInstalled.of_addInduct` take it; the
   ordinary installer supplies `BlockCertificate.compiled` (`Install/BlockCertificate.lean`,
   also replayed in `rebase`), `SourceAddInduct.inductInstalled` takes it as a hypothesis
   (`Install/Result.lean`). The nested installer goes through `BlockCertificate` and supplies it
   from `RestoredBlock.compiledWF`.

`loweringRun.WF` is proved (no `sorry` in `Lowering.lean` or `Nested/Lowering/**`): each field
in `Nested/Lowering/Assembly.lean` from `NestedLoweringOutputClosed`
(`ElimNestedInductive.run'.translationClosed`), over PR #53's lowering refinement
ported under `Nested/Lowering/` (`Refinement`, `ParameterOpening`, `Recognition`, `Expression`,
`Queue`, `AuxiliaryFamilyPositions`, `Output`, `Ordinary`, `Restore/{ExprReplace,ParameterOpening}`;
new: `Counts` for `types_length`). `Nested/Lowering/Expansion/**` and `AuxiliaryFamilies`,
`AuxiliaryConstructors`, `OccurrenceTyping` are ported too: the nested expansion for
`RestoredBlock.formation` is `RecursorInput.nestedExpansionData` / `RecursorInput.nestedFormationWF`
(`Nested/Lowering/Expansion/Data.lean`), over the lowered run's `RecursorInput`
(`LoweredRun.input`), the lowering run and the restoration side's source facts. Adaptations:
PR #53's `OrdinaryConstructorCheck`/`HeaderEnvironment` arguments became
`RecursorInput`/`HeaderData`, the eliminator cases of the expansion relations are gone, and
`InstalledBelow` facts are read through `addInduct`'s stages (`VEnv.addInduct_stages`).

## Nested interface (`Verify/Inductive/Nested/**`)

`Verify/Inductive/Nested/**` is imported by `Verify/Inductive.lean` and by
`Verify/Environment.lean` (through `Nested/Install/Dispatch.lean`). `NestedInductivePreserves`
is the theorem `nestedInductivePreserves`; `addDecl.WF` has no hypothesis. The interface and
the phases are the nested section of `Lean4Lean/Verify/Inductive/README.md`. The boundary
theorems, all proved:

| statement | file | PR #53 counterpart | phase |
|---|---|---|---|
| `loweringRun.WF` | `Verify/Inductive/Lowering.lean` | `NestedLowering`/`NestedLoweringOutputClosed` (`Nested/Restoration/SourceTranslations.lean`, over `Nested/Lowering/**`): `ElimNestedInductive.run.refines`, `LowerNextStep`, `NestedAuxMapModels`, `ConstructorRestorationInverse.restoredType_eqv_source`, `types_eq_source_of_aux2nested_size_eq_zero` | lowering |
| `validateSourceConstructorTypes.run.WF` | `Verify/Inductive/Nested/Restoration/Validation/Passes.lean` | `Validation/Checks.lean` (`validateSourceConstructorTypes.WF`) with `checkType.WF`/`ensureSort.WF` | validation |
| `validateRestoredRecursorTypes.check.WF`, `.run.WF` | same | `Validation/Checks.lean`, `Validation/Environment.lean` (`ValidationEnvironment`) | validation |
| `validateRestoredRecursorRules.check.WF`, `.run.WF` | same | `Validation/Checks.lean`, `Validation/StrippedEnvironment.lean` | validation |
| `validateNestedAuxiliaries.WF` | same | `Nested/Lowering/Basic.lean`'s `validateNestedAuxiliaries.WF` (`NestedBindingContextWF`, `NestedOccurrencesTyped`) | validation |
| `stripRecursorRules.checkingValid` | same | `Validation/StrippedEnvironment.lean`, `Validation/StrippedRecursorShapes.lean` (overwriting a well-formed `SMap`, `Aligned` under same-type replacement) | validation |
| `nestedRestoredBlock` | `Verify/Inductive/Nested/Restoration/Restore.lean` | `nestedValidatedRawSourceWF` + `NestedRun.assemblyOfRun` (`Install/Certificate.lean`, `Install/CertificateOfRun.lean`) + `RestoredBlockCertificate.blockCertificate` (`Install/BlockCertificate.lean`): the restoration folds (`Steps.lean`), the restored source declaration (`SourceDeclaration`, `SourceTranslations`, ...), the specialization tables (`Tables`, `TableAgreement`, `ContainerSpecializations`), the restored recursors (`Recursors`, `RecursorRenaming`, `RecursorShape`, `RecursorAlignment`), the compilation data (`CompilationData*`), the kernel order (`Install/Permutation`, `DependencyOrder`, `RecursorTranslations`) | restoration |
| `RestoredBlock.rulesWF` | `Verify/Inductive/Nested/Equations/Rules.lean` | `Equations/WF.lean` (`restoredEquationSubstitution`, `restoredEquationsWF_of_substitutionPremises`), `Equations/{RestoredRules,RestoredRulesBase,GeneratedGuard,RuleRhs,SourceIota*}.lean`, restated as `PatTyped` (`Rules/IotaPatTyped.lean`) | equations |
| `RestoredBlock.blockWF` | same | `Restoration.equation_wf` along the substitution, `RestoredBlockCertificate.blockCertificate`'s `rulesWF` | equations |
| `VEnv.RestoredPattern.clause` | `Theory/Inductive/RestorationInterpretation.lean` | new: the `pat` analogue of `RestoredEliminator.clause` (the interpreted redex is β-convertible to a redex of the restored rule, `Agrees.expr_simAt`, `BetaRed.mkApps_wrapLams`) | equations |
| `InductiveSignature.instantiateParams_liftN` | `Theory/Typing/RestorationShapes.lean` | `CaseReduction.instantiateParams_liftN` | equations |
| `RestoredBlock.installedFacts` | `Verify/Inductive/Nested/Install/Installed.lean` | `Install/BlockCertificate.lean` (`inductInfosFromDecl`, `cover`, `constructorOwnersPresentOfContext`), `Install/FromRun.lean` (`assemblyBaseValid`), `Install/ConstructorCoherence.lean` (`constructorParameterDomainsDefEqOfSource`) | installation |

The ordinary path's obligations, carried by the interface: `InstalledBlocks.addInduct`'s
`hrecShapes` is `RestoredBlock.recShapes` (every new recursor, auxiliary recursors included,
whose majors are containers at specialized arguments; `recursorShapesOf` does not cover them,
so `Restoration/RecursorShape.lean` and `Validation/StrippedRecursorShapes.lean` are ported);
`BlockCertificate.compiled` is `RestoredBlock.compiledWF`, `newUnsafe` is `RestoredBlock.newUnsafe`.

For the model: `CompiledInductive.rule_ctor_cases` is what
`WF.patCtor_rigid` reads (the second alternative is `VEnv.IsPatCtor env ru.ctor`, the
container's own registered rule, so the history induction recurses on an earlier pattern);
`Model.PatValid.iota` reads `RecsCompiled` as `⟨block, .intro compiled containers, recsOf⟩` with
`CompilationData.equations`/`recursors` (restorations of the generator's equations and
recursors, `RestoredBlock.rules_ofRestoredEquation`) and `blockWF` (equation typing in the empty
context); README nested section, "What the nested instance provides".

New Theory files of the nested interface: `Theory/Typing/Interpretation.lean`
(`VEnv.Interpretation` without `elim`; `Sound` with `ordered : OrderedStrong`, a `pats` clause
`PatClause` and no eliminator clause; `PatClause.of_fixed`, `Sound.addPat`, `Sound.of_le` with
`hpats`), `Theory/Inductive/RestorationInterpretation.lean` (no eliminators; `RestoredPattern`),
`Theory/Typing/RestorationShapes.lean`, `Theory/Inductive/RestorationHead.lean`,
`Theory/Inductive/Restoration.lean` (now also `restorableNames`, `headName`, `expr_mkApps`,
`equation_parts`, `expr_of_avoid`, `VExpr.projNamesAvoid`, two closedness lemmas),
`Theory/Inductive/CompilationMajors.lean`. No existing Theory file was edited for it.

## Inductive interface (`Verify/Inductive/**`)

`Verify/Inductive/**` is imported by `Verify/Environment.lean` through
`Verify/Inductive/Dispatch.lean`. `InductiveDeclPreserves` is the theorem
`inductiveDeclPreserves`; `addDecl.WF_of` keeps the `InductiveDeclPreserves` form. The
interface and the phases are in `Lean4Lean/Verify/Inductive/README.md`. The boundary theorems,
all proved:

| statement | file | PR #53 counterpart | phase |
|---|---|---|---|
| `AddInductive.checkInductiveTypes.WF` | `Verify/Inductive/Header/Check.lean` | `checkInductiveTypes.accumulatesHeadersSourceAligned` (`Header/Check.lean`), restated with `HeaderPhase` | header |
| `CheckedHeaders.Describes.headerCertificate` | `Verify/Inductive/Header/Check.lean` | `HeaderFormations.complete` (`Header/Telescope.lean`): `TypeShape` reads only the header fields | header |
| `AddInductive.declareInductiveTypes.WF` | `Verify/Inductive/Header/Installation.lean` | `HeaderDeclaration.toHeaderEnvironment` (`Install/Headers.lean`), `declareInductiveTypes.installsHeadersAtomicWF` | header |
| `TrInductDeclCore.sourceNames_nodup` | `Verify/Inductive/Formation.lean` | same name, via `VEnv.addConstVals_append` | header |
| `CheckedFormation.signature` | `Verify/Inductive/Constructor/CheckedFormation.lean` | `sourceSignature`, `sourceSignature_models`, `sourceSignature_familyTypesWF_header` (`Constructor/CheckedFormation.lean`), without the case schema | constructor |
| `AddInductive.constructorPhase.WF` | `Verify/Inductive/Constructor/Check.lean` | `AddInductive.formationCoreClosedWF` (`Install/Formation.lean`) from `declareInductiveTypes.WF`, `checkConstructors.checkedWF`, `declareConstructors.WF` | constructor |
| `RecursorInput.recursorPhasesWF` | `Verify/Inductive/Recursor/Check.lean` | `ConstructorCheck.recursorPhasesWF` (`Recursor/Check.lean`), output `TrRecursor` and the shape clauses of `VInductDecl.WF` | recursor |
| `InductiveSignature.VRecRule.OfEquation.ofTr` | `Verify/Inductive/Recursor/Entries/TrRecursorVal.lean` | new: a rule that is a generated equation (`TrRecursorRule`) and translates to a `VRecRule` (`TrRecursor`) is `VRecRule.OfEquation` (`TrExprS.unique`, shape of `Instance.equation`) | recursor |
| `RecursorCheck.generatedRuleTranslation` | `Verify/Inductive/Rules/RuleTranslations.lean` | same name: `ruleRhsTranslations`, `equationsWF`, `trRules`, plus `rules_wf : PatTyped` | rules |
| `RuleTranslations.blockWF` (`addRecs` is `addConstVals` over the recursors) | `Verify/Inductive/Rules/RuleTranslations.lean` | `VInductDecl.addRecs_eq_addConstVals` | installation |
| `RuleTranslations.compilesTo` | `Verify/Inductive/Rules/RuleTranslations.lean` | `OrdinaryCompilationCertificate.compilesTo` (`Compilation.lean`): `CompiledInductive.intro` with no auxiliaries | installation |
| `RuleTranslations.recsOf` | `Verify/Inductive/Rules/RuleTranslations.lean` | new: `VInductDecl.RecsOf` from `trRules`, `trRecs`, `recursors_eq` and `VRecRule.OfEquation.ofTr` | installation |
| `ConstructorCertificate.withRecs` | `Verify/Inductive/Formation.lean` | new: transport of `CtorShape`/`CtorTailWF` along `VInductDecl.withRecs` | installation |
| `RecursorCheck.blockCertificate` | `Verify/Inductive/Install/BlockCertificate.lean` | `RecursorCheck.blockCertificate` + `OrdinaryInstallation.extend*Exact`'s assembly of `AddInduct` (`Install/BlockCertificate.lean`, `Install/OrdinaryExtension.lean`) | installation |
| `BlockCertificate.installedBlocks` (`hpres`) | `Verify/Inductive/Install/BlockCertificate.lean` | every constant of the source is a constant of the output (`insertConsts_find?_mono_of_fresh`) | installation |
| `BlockCertificate.rebase` | `Verify/Inductive/Install/BlockCertificate.lean` | `BlockCertificate.rebaseAddInductSafe` | installation |
| `BlockCertificate.extendSafeExact` | `Verify/Inductive/Install/BlockCertificate.lean` | same name, via `rebase` and `VEnvs.WF.extendInductExact` | installation |
| `BlockCertificate.extendUnsafeExact` | `Verify/Inductive/Install/BlockCertificate.lean` | `BlockCertificate.extendUnsafeOfHiddenExact`, via `VEnvs.WF.extendUnsafeExact` and `TrEnv'.ignore` | installation |
| `Kernel.Environment.checkDuplicatedUnivParams.WF` | `Verify/Inductive/Install/Ordinary.lean` | same name (`Recursor/Check.lean`) | installation |
| `checkPrimitiveInductive_eq_true_iff` | `Verify/Inductive/Primitive/Shape.lean` | same name (`Primitive/Shape.lean`) | primitive |
| `loweringRun.primitiveNoop` | `Verify/Inductive/Primitive/Shape.lean` | `ElimNestedInductive.run'.primitiveNoopWF` (`Primitive/Lowering.lean`) | primitive |
| `AddInductive.constructorPhase.primitiveWF` | `Verify/Inductive/Primitive/Run.lean` | `AddInductive.formationCore.primitiveClosedWF` (`Primitive/Run.lean`) with `Primitive/{Headers,Constructors,ConstructorCheck,ConstructorParams,BatchInstallation,Constants}.lean` | primitive |
| `AddInductive.run.primitiveSourceAlignedWF` (`Bool.rec`/`Nat.rec` are not primitives) | `Verify/Inductive/Primitive/Run.lean` | `PrimitiveInductiveShape.recursorsNonprimitive` | primitive |
| `loweringRun.types_nonempty`, `loweringRun.ordinary_types_eq_source` | `Verify/Inductive/Lowering.lean` | derived from `loweringRun.WF` (`NestedLoweringOutput.source_nonempty`, `.types_length`, `.ordinary`) | lowering |

`VerifyInductive.NestedInductivePreserves` (`Verify/Inductive/Dispatch.lean`), the named
hypothesis of the nested branch, is the theorem `nestedInductivePreserves`
(`Nested/Install/Dispatch.lean`).

The checker-verification facts `VEnvAt.recursorShapes` (consumed by `ContextWF.initial`, from
`InstalledBlocks` and `VInductDecl.WF`'s `rec_shape`/`rules_ctor`) and
`VEnv.WF.patsAvoidFreshConsts` are proved (see the checker-verification section).

Theory changes for the interface: `VEnv.addInduct`'s stages and
`VInductDecl.RecsOf`/`VRecRule.OfEquation` moved to `Theory/Inductive/AddInduct.lean`;
`ContainersInstalled.cons` (`Theory/Inductive/Compilation.lean`) and `VEnv.InstalledBelow.intro`
(`Theory/Inductive.lean`) install the container by `base.addInduct container = some installed`
with `container.RecsOf block` (and still `block.WF base`), replacing `VInductBlock.install`; the
`InstalledBelow` lookup lemmas moved to `Theory/Typing/InductiveLemmas.lean`. This resolves the
environment model's `InstalledBelow` finding above and the observation model's
`ContainersInstalled` finding. No new `sorry` in `Theory/`.

## Checker verification

Outside `Theory/` there is no `sorry`. The two facts that were open in the checker
verification are proved:

| statement | file | what it says |
|---|---|---|
| `VEnvAt.recursorShapes` | `Verify/TypeChecker.lean` | the recursor and constructor telescopes (`VRecursorShape`, `VConstructorShape` at the constructor's own parameter count) of every visible recursor of a complete model. Recursor reduction needs them to show the constructor application of a well-typed ι redex saturated. In PR #53 they were part of the installed-block invariant (`RecursorAlignmentCore`); `VInductDecl.WF` only records the syntactic `rec_shape`/`rules_ctor` (`CtorShape` does not say the constructor ends in its family at the parameter variables), so they come from the installed-block descriptors (`InstalledBlocks.recursorShapesCoherent`). Every other fact the checker reads (`CheckerEnv`) is `CheckingEnv.Valid` or PR #43's `TrEnv.pats_iota'`. |
| `VEnv.WF.patsAvoidFreshConsts` | `Verify/Typing/ConstSupport.lean` | the `pat` case of `IsDefEq.noConsts`: the fixed parts of a registered rule's right-hand side avoid names absent from the environment. Proved along the history (`VEnv.WF'.patsAvoidFreshConsts`), see the next section for why the `Ordered` form was not provable. Used only by `VExpr.WF.noFreshConsts` (constructor positivity). |

Interface: the checker reads its environment through
`CheckerEnv safety env venv` (`Verify/TypeChecker/CheckerEnv.lean`), which extends
`CheckingEnv.Valid` by `shapes : RecursorShapesCoherent` and `iota : IotaRulesRegistered`
(`TrEnv.iotaRulesRegistered` proves the latter from `TrEnv`). An inductive declaration that runs
the checker in an intermediate environment must supply both there.

## The model's `pat` obligations (`Model.PatValid.iota`, `patsAvoidFreshConsts`, `WF.patCtor_rigid`)

`patsAvoidFreshConsts` and `WF.patCtor_rigid` are proved; `Model.PatValid.iota` is open. The
analyses below record why.

**`VEnv.Ordered.patsAvoidFreshConsts` is not provable from its hypotheses without a new
metatheorem.** `Ordered.pat` only records `PatWF`, whose `PatTyped` types one generic instance
in an *arbitrary* context `Γ` (no `OnCtx Γ`). `IsDefEq.noConsts` needs a context avoiding the
names, and a context mentioning a fresh constant `F` does type terms containing `F` (a `beta`
redex `(λ (x : A). b) a` is typed without typing `A`; `eta` puts the domain of a variable's
type into a term), so the template's constants are not bounded by the environment. Proving the
statement as is needs an inertness theorem (an undeclared constant reaches a typed endpoint only
through the context) that is close to context strengthening. `OrderedStrong` does not help: its
`PatsStrongOn` concerns strongly typed instances in strong contexts, and no such instance is
known to exist. Two fixes: add `OnCtx Γ (env.IsType U)` to
`VEnv.PatTyped` (then the proof is the `Ordered` induction with `IsDefEq.noConsts` on the
generic reduct, about 80 lines), or state the lemma for `VEnv.WF` from the installed blocks'
rule typing (`VInductBlock.WF`'s `df.WF envRecursors` types each equation in the empty context).
The tree takes the second (`VEnv.WF.patsAvoidFreshConsts`).

**`Model.PatValid.iota` needs three things beyond the static facts listed above.**
1. *Index-determined fields under singleton elimination* (applied). `Signature.SingletonElimination`
   admits a non-proposition field `x` when `bvar x` is a bare index of the constructor's result
   (`Acc.intro`'s `x`). In mode C (the major is a proof, so `Km` is empty) `RuleBind` can bind
   such a field neither from `Km` nor by the proof binding; with a dummy at every index position
   of the lead the field could not be bound from its index key either. The clause's lead
   (`iotaLead`, `Model/Interp.lean`) therefore carries the constructor's result indices, so a
   field that is a bare index `bvar x` is bound from its index key, as the stored equations'
   `eqLead` did.
2. *Injectivity of the major's family at the instance.* A pattern instance has arbitrary terms
   at the index holes and at the constructor-parameter holes `Q`. `RuleBind` types each anchor
   at the template's binder type, but the field classes `Km` provides are classes at the
   constructor's field domains instantiated at `Q`, and an index key is a class of the instance's
   index argument. Relating them needs `Q ≡ P` (recursor parameters) and `idx_j ≡ F_x`, that is
   injectivity of the family `I` between the constructor's result type and the recursor's major
   domain. PR #53's stored equations never needed this: their λ-wrapped sides
   shared one variable between both positions (`bvar_dom_cls`). At the instance it must be
   extracted from the sound conversion links of the redex's `HTS` (a `Π`-domain step and a
   rigid-spine argument step, as `forallE_chain` and `rigid_analysis` in `Model/Extract.lean`
   do, but from `SD` links instead of `SoundEnv`). Semantic uniqueness of types would serve too;
   neither exists in the model.
3. *Agreement of the template's binder types with the recursor telescope.* The parameter,
   motive and minor anchors are bound from recursor keys, which are classes at the recursor's
   domains; `RuleBind` and the left-to-right direction need them at the template's binder
   types. `VInductDecl.WF` does not relate the two (`rule_shape` is a count, `rules_wf` is
   `PatTyped` in an arbitrary context). They agree syntactically for the generated equations
   (`Instance.equation`'s domains start with the recursor's `params ++ motives ++ minors`), so the
   facts come from `RecsCompiled`: `CompilationData.equations` and `VRecRule.OfEquation`, with
   `VInductBlock.WF` typing each equation in the recursor-stage environment, whose model is sound
   along the history (`EnvValid` of that stage follows from the pre-block one).

The remaining ingredients are as listed above: the elimination classification
(`Instance.Admissible.elimination`: data families make mode C contradictory through `FamSort`;
small elimination leaves both sides without observations; singleton elimination gives the rule's
uniqueness per recursor and the proof binders, `Model/{FamSort,Singleton,RecursorRule}.lean` on
PR #53), the projection entry of a structure family (eta mode), and `PatsIota` for
uniqueness in the left-to-right direction. All of it is read off `CompilationData`, which for
nested blocks goes through the restoration (`compilationRestoration`, `Inductive/RestorationHead`;
the nested instance provides `CompiledInductive.rule_ctor_cases` and
`RestoredBlock.rules_ofRestoredEquation`, see the nested-interface section). For ordinary
blocks (`auxiliaries = []`) the estimate is 4k to 6k lines: the instance-level directions (the
analogue of `pat_rhs_sub_head`/`pat_lhs_sub`, about 1.5k lines), the two injectivity
extractions, and the ordinary compilation facts ported from PR #53's `Rules/` and `Model/` files
(about 2.5k lines). `EnvValid.lean` must also pass the pre-block `EnvValid` to the pattern case,
which today calls `PatValid.iota hF` with no history data (or the proof recovers the installing
block from `WF'.pats_origin`).

**`VEnv.WF.patCtor_rigid`** (proved, `Model/WFFacts.lean:332`). For an ordinary block the
constructor is `s.constructors[i].name` through `CompilationData.equations` and
`Instance.equation`, a constructor of the block, hence rigid. An auxiliary recursor's rule fires
on a container constructor; `CompiledInductive.rule_ctor_cases` (restored equation's major)
gives that for every rule `ru` of every recursor of an installed nested block, `ru.ctor` is a
constructor of the block or of an installed container (`ContainersInstalled`).
`WF.patCtor_rigid` and `Ordered.patsAvoidFreshConsts` are closed (earlier commits of this
branch). `Model.PatValid.iota` is gone: the history induction (`WF'.envValid`,
`Model/EnvValid.lean`) dispatches each ι rule registered by an inductive step on its compilation
(`VInductDecl.WF.rule_block`). Ordinary compilations (`aux = []`): `Model.PatValid.ordinary`
(`Model/IotaHistory.lean`, sorry-free). Nested compilations: the one open stub
`Model.PatValid.nested` (`Model/PatSound.lean`), stated with the same hypotheses as
`PatValid.ordinary` plus `aux ≠ []` and `ContainersInstalled base aux`.

**Route.** The generic λ-wrapped equation `L ≡ R` of a rule is not derivable in the final
environment without uniqueness of typing (the pattern rule types only instances, at the redex's
type), so the `pat` case is proved directly at the instance
`e = rec m1 (recArgs ++ [ctor lsC ctorArgs])`, `red = (rhs.instL m1) argsR`, read at the argument
valuation `v = argSubst (argsR σ)` of the template's binders (`Model/IotaInstance.lean`). The
generic assembly is `PatValid.of_rule` / `PatValid.of_rule_empty` (`Model/IotaPat.lean`), the
arguments against the template are `iotaArgRel_of` (`Model/IotaArgs.lean`).

**Ordinary blocks** (`PatValid.ordinary`): `IotaStatic` of the generated recursor
(`Instance.iotaStatic`), uniqueness per head (`patUniq_decl`), the stage environments
`envT`/`envR` of `addInduct` are strong and valid in the model of `envF`
(`stages_orderedStrong`, `stages_envValid`, `Model/IotaStage.lean`; this needs `WFPrefix envF env0`,
now carried by `WF'.envValid`), the reduct is typed in `envR` (`block_rules_wf`), the projection
facts of the major's family (`projMajor_decl`, from `WF.installed_projection`), its semantic sort
(`famSort_decl`), and the split on `Admissible.elimination`: never-zero families (mode C absurd,
`C_absurd_gen`), small elimination (`of_rule_empty` with `rhs_empty_motive`), singleton elimination
(proof binders from `SingletonElimination`, uniqueness of the recursor's single rule). The instance
relation (`ordinary_rel`) reads the family's normalized telescope off `TypeShape` and the normalized
constructor type off the correspondence's `IsDefEqU`; its sort typing comes from Π-inversion when the
constructor has binders, and the installed type is used as its own normal form when it has none.

**What `PatValid.nested` needs** (what wave 3's nested blocks must provide, by analogy with the facts
the ordinary case uses): the static data of a restored equation (`IotaStatic` of the restored
recursor's type, including the minor ending in the restored constructor and no later minor ending in
it); uniqueness of the rule per head and constructor; the projection facts and the semantic sort of
the major's family when it is a container family (`ProjMajor`, `FamSort`, as the source branch's
`projMajor_restored`/`famSort_container`); and for `iotaArgRel_of` the container constructor's raw
shape and the relation of its installed type to the restored template's field domains (`hNS`, `hDP`,
`hDF`).

**`VInductDecl.WF` and descriptor facts used by the ordinary case.** `VInductDecl.WF`: `recsCompiled`
(the compiled block, `RecsOf`, `block.WF` and its `rules` typed in the recursor stage; `CompiledInductive`
for `WF.installed_projection` and `addInduct_ctor_resultFamily`), `rec_shape` (the number of indices of
the recursor), `rule_shape` (the number of fields, through `lamArity`), `rules_nodup`, `rules_ctor` (the
constructor's arity, for the projection entry's `numFields`), `recs_wf`, `types_wf`, `ctors_wf`
(strong typing of the stages), `source` (constructor universes). `CompilationData`: `ordinary_rules`,
`ordinary_recursors`, `names`, `model.constructorArity`, `model.nparams`, `nparams`, `model.families`
and `headerPrefix` (expanded types), `correspondence` (`RestoresFamily`: name, indices, result level,
type; constructors up to `IsDefEqU`), `sourceParameters` (`TypeShape`, `RawCtorShape` with
`RawIndAppAt`), `admissible` (`elimination`, `SingletonElimination`). Environment facts:
`WF.installed_projection`, `Ordered.projections_unique`, `Ordered.projection_resultFamily`,
`WF'.inductTypeRigid`, `WF.isCtor_rigid`, `WF.projCtor_rigid`, and `WF.patsStrong` (open, for the
strong stages).

**Import hazards met on the way.** The model cannot import `Confluence/**` (it imports the model
through `HeadInversion`), so `Confluence/StructureMajor.lean`'s structure coherence is restated
for the model (`Model/StructCoh.lean`, `WF.structCoh`). `InductiveSignature.vars_map_liftN_lo`
is declared identically in `Theory/Typing/SignatureVars.lean`,
`Verify/Inductive/Rules/IotaPatTyped.lean` and `Verify/Inductive/Nested/Restoration/SignatureVars.lean`;
Lean accepts the duplicate theorem but not differing auxiliary `simp` lemmas, whose names shift
when the equation lemmas of `vars` are realized in an imported module. `Rules/Compiled.lean` and the
model therefore avoid `simp [vars]` (`InductiveSignature.vars_unfold`); deduplicating the three
copies would remove the hazard.
