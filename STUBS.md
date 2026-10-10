# Stub ledger: verified inductives on the ι pattern calculus

Every `sorry` in `Lean4Lean/Theory/` (the `Lean4Lean.Theory` library builds every file under
that directory), with its owner wave. `lake build Lean4Lean.Theory`, `Lean4Lean.Experimental`,
`Lean4Lean.Tests.IotaShape` and `Lean4Lean.Tests.ShapeDecide` are green at wave 0;
`Lean4Lean.Verify` is not yet imported (waves 1 to 3) and the `lake build` default target
therefore fails on `Verify/` until wave 1. Waves follow `iota-port/PLAN-RECONCILED.md`.

| statement | file | origin | owner |
|---|---|---|---|
| `VEnv.WF.patsStrong` | `Theory/Typing/EnvLemmas.lean` | PR #43 | wave 1D (`patsStrong`), after the 0b spike |
| `VEnv.Model.PatValid.iota` (`-- WAVE 1C STUB`) | `Theory/Typing/HeadInjectivity/Model/PatSound.lean` | new: the `pat` case of `Model.sound` for the registered ι rules (see the wave 1C section) | wave 1C |
| `VEnv.WF.patCtor_rigid` (`-- WAVE 1C STUB`) | `Theory/Typing/HeadInjectivity/Model/WFFacts.lean` | `ConstructorRigidity.lean` on the source branch (`WF.installed_constructor_rigid`) | wave 1C |
| `IsDefEqU.weakN_iff` | `Theory/Typing/UniqueTyping.lean` | master | open on master; the one strengthening principle the checker uses (PORT_PLAN section 5) |
| `NormalEq.parRed` (two `sorry`s, the `extra` cases) | `Theory/Typing/ChurchRosser.lean` | master | wave 4 (confluence retargeted onto `env.pats` supersedes this file) |

Not stubs but conditional results: everything through `VEnv.WF.orderedStrong` (the strong
system, substitution theorems, inversion lemmas) depends on `patsStrong`; everything through
`VEnv.WF.headInversion` and `IsDefEq.uniq` depends on `patsStrong` (through
`VEnv.WF.orderedStrong`, see the wave 1C section) and on the two wave 1C stubs.
`Injectivity.lean` has no `sorry` of its own: PR #43's `IsDefEqU.const_arity_inv` is derived
from `VEnv.WF'.inductTypeRigid` and `headInversion`.

## Wave 1C: the observation model on the ι pattern calculus

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
remove the use, because the extraction's input is a weak chain of the final environment; the
spike's conclusion stands (`SPIKE_PATSSTRONG.md`, section 3).

**What changed in the port.** `Obs` loses `elimRule` and gains `pat` (`Model/Interp.lean`), of
the same `RuleBind` shape as the stored-rule clause `rule`, which stays for the quotient rule
(the one `defeqs` entry with a constructor major); the reduct template `rhs = wrapLams doms
body` is read off `SimplePattern.iotaRHS'`, the generic leading arguments are
`Model.iotaLead` (bound variables for parameters, motives and minors, a non-variable dummy at
the ignored index positions) and the fields `Model.iotaFs`; the recursor's major domain
(`VExpr.RecShape`) supplies the family `I` and its levels `lsI` to the eta binding; in mode C
the clause records that the rule is the only pattern headed by its recursor. `IsCtor` reads
the constructor of a pattern (`VEnv.IsPatCtor`, `Rules/ConstructorMajor.lean`). `HTS`,
`HeadTy` and the spine lemmas are for constant heads only. `DeltaRules` gains a `pats` field
(no pattern is headed by a defined constant) and loses its inductive case (`addInduct` adds no
`defeqs`). `Model.sound` takes `PatValid` for the patterns of `E` (`Model/Sound.lean`);
`EnvValid` has fields `rule`, `proj`, `pat`. `Model/WFFacts.lean` proves the static facts
along the history: `WF'.defeqs_cases`, the quotient facts (`WF.quotConsts`, `WF.quot_rigid`,
`WF.quotMk_rigid`, `WF.quot_not_projection`), `WF.projStatic`, `WF.isCtor_rigid`,
`WF.installedCtor_resultRigid`. `EnvValid` carries `HeadsClosed` and `PatsClosed` (no later
declaration adds a rule or a pattern headed by an existing constant). Dropped: `EnvTables/`,
`Rules/{Coverage,RecursorEquations,RestoredRecursorEquations}`, `Model/{CaseRule,
CaseRuleSound,RecursorRule,RestoredRecursorRule,Singleton,FamSort,EmptyRule,TeleArity,
CtorArity,ProjMajorWF,ProjMajorRules,ProjStaticWF}` (eliminator registry and stored-equation
provenance); `IotaSoundnessLemmas.lean` is not needed (the stored-equation detour collapses to
`IsDefEq.pat`).

| statement | file | what remains |
|---|---|---|
| `VEnv.Model.PatValid.iota` | `Model/PatSound.lean` | The `pat` case of soundness for an instance `rec us args ≡ rhs us pmm fields` of a registered rule, from the semantic typing of redex and reduct (`HTS.spine`, `HTS.lamSpine`) and the static facts of the block: `VInductDecl.WF.rec_shape` (the `dsH`/`I`/`lsI` data of `Obs.pat`), `rules_ctor`, `PatsIota` and `rules_nodup` (uniqueness), the family's recorded sort (`FamSort`, `Model/FamSort.lean` on the source branch, from soundness of the environment before the block), proof binders of a singleton elimination (mode C, `Model/Singleton.lean` on the source branch), the projection entry of a structure family (eta mode). The two directions are `pat_lhs_sub`/`pat_rhs_sub_head` of `Model/RuleSound.lean` with the instance's spine in place of the λ-wrapped generic sides; `pat_rhs_sub_head` is already stated for an abstract head clause `hrule`. Estimated 1.5k to 2.5k lines. |
| `VEnv.WF.patCtor_rigid` | `Model/WFFacts.lean` | The constructor of a registered pattern is a constructor of its block or of a container block (`VInductDecl.RecsCompiled`, `VRecRule.OfEquation`, the compilation's `equation_major_cases`), hence rigid (`WF'.inductCtorRigid`). The source branch's `ConstructorRigidity.lean`. |


## Parked, not deleted

| item | where | why | owner |
|---|---|---|---|
| `Theory/Typing/Confluence/**`, `ChurchRosser`/`FullReduction`/`LevelledReduction`/`FullChurchRosser`/`HeadReduction` of the source branch, `LevelledConfluence.lean`, `NormalSubstitution.lean`, `Inductive/{RecursorData,RecursorPrefixUnfolding,QuotPrefixUnfolding,RecursorEquationHeads,RecursorEquationCoverage,SingletonReconstruction}.lean`, `Typing/{RecursorRegistration,RecursorRuleRegistration,RecursorRegistryInstallation,StoredRuleHeads,PatternCaptures,DefinitionPatterns,DefinitionRegistryInstallation,QuotLiftTelescope,QuotPropInhabitant,ConstructorRigidity,RecursorMajorFamily}.lean`, `PrefixUnfolding/`, `SingletonExtraction/` | source branch only | confluence development, to be retargeted from stored equations to `env.pats` | wave 4 |
| `Theory/Typing/HeadInjectivity/{Model,Rules,Projections}/**`, `EnvTables/`, `Typing/IotaSoundnessLemmas.lean` | source branch only | the observation model behind the two wave-0 stubs | wave 1C |
| `Theory/Typing/Interpretation.lean`, `Inductive/RestorationInterpretation.lean`, `Typing/RestorationShapes.lean`, `Inductive/RestorationHead.lean` | source branch only | the restoration interpretation needs a `PatClause` for `IsDefEq.pat` (PORT_PLAN section 3) | wave 3 |
| `Theory/Typing/Strengthening/**` | source branch only | dropped (PORT_PLAN section 5) | never |
| `Inductive/Case*.lean`, `CaseSchema*`, `ProjNamesAvoid`, `RestorationProjNames`, `Typing/{CaseReduction,CaseMotive,CaseSourceSort,CaseMajorDomain,EliminatorCoherence*,SchemaStructCompat,EliminatorRestorationScope,ProjNamesTyping,ProjectionFamilyArity,ProjectionConstructorFamily,SignatureVars}.lean` | source branch only | the case-eliminator registry, dropped with `VExpr.elim` | never |
| PR #43's `ChurchRosser.lean`, `HeadReduction.lean`, `InductiveParams.lean` | kept and building | `Params.no_projections` makes them the structure-free instance; `toParams`/`inductParams` take the projection-free hypothesis | wave 4 decides whether they stay as the small-environment instance |

## Not a stub: hypotheses of the declaration judgment

`VInductDecl.WF` (`Theory/Inductive.lean`) keeps the recursor typing (`recs_wf`), the rule
typing (`rules_wf : VEnv.PatTyped`), the recursor shapes (`rec_shape`, `rule_shape`,
`rules_nodup`) and the constructor-constant clause (`rules_ctor`) as *fields* discharged by
the checker verification (waves 2 and 3), not as theorems of `RecsCompiled` as PORT_PLAN 1.4
proposed. Deriving `rules_wf` from the typing of the generated λ-wrapped equations needs
uniqueness and Π-injectivity, both stub-backed in wave 0; wave 2 may either prove it or keep
discharging the field directly from `generatorEquationWF`.

## Wave 1E (executable, tests, divergences)

No stubs: the executable and test ports add no `sorry`. Tests that do not build yet are listed
in `Lean4Lean/Tests.lean` (the manifest of the `Lean4Lean.Tests` library, which no longer globs
`Lean4Lean/Tests/`) with the wave that adds them back:

| test | needs | wave |
|---|---|---|
| `AmbientContext` (PR #43) | `Verify.TypeChecker` | 1A |
| closed-form and translation checks of `QuotInit` (removed from the ported test) | `Verify.Environment` (`Environment.addQuot_eq`, `VEnv.addQuot`) | 1B |
| `InductiveTheory`, `TypedInductiveCompilation` | re-expression for the structure `VInductDecl.WF` and `VEnv.pats` | 2 |
| `CorruptRecursorMetadata` | `Verify.Inductive.Recursor` | 2 |
| `CorruptRestoredRecursorMetadata` | `Verify.Inductive.Nested` | 3 |
| `RecursiveFieldClassification` | `Theory.Typing.Interpretation` | 3 |
| `PreludeEq` | `Verify.Inductive.Prelude.EqSyntax`; `VEnv.HasCanonicalEq` only for confluence | 4 |
| `CacheMode`, `SyntacticTranslation` | dropped with the scoped cache mode and the strengthening study | never |

## Wave 1B (environment model)

No `sorry` in `Lean4Lean/Verify/Environment/**`, `Verify/Environment.lean` or `Verify.lean`.
`lake build Lean4Lean.Verify.Environment Lean4Lean.Verify Lean4Lean.Tests.QuotInit` is green
(the `sorry`s it reports are wave 0's and wave 1A's, in `Theory/` and `Verify/TypeChecker`,
`Verify/Typing`).

| statement | file | kind | owner |
|---|---|---|---|
| `InductiveDeclPreserves` | `Verify/Environment.lean` | named hypothesis of `addDecl.WF` (not a `sorry`): a checked inductive declaration, at any fuel, preserves `VEnvs.WF` and extends every safety level | waves 2 and 3 (`addInductiveDeclaration.WF_preserves`) |

Interface notes for the waves that build on this one:

- `VEnvs`, `VEnvs.WF` (now with `blocks : InstalledBlocks safety env (ves.venv safety) .complete`),
  `VEnvs.axiom_of_choice` and `VEnvAt` live in `Verify/Environment/Model.lean`;
  `Verify/TypeChecker.lean` imports it (`-- WAVE 1B COMPAT`).
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

Found while porting (not fixed here, `Theory/` is frozen):

- `VEnv.InstalledBelow` (`Theory/Inductive.lean`) still installs a block through
  `VInductBlock.install`, which adds the generated rules as stored equations (`defeqs`). No
  environment built by `VEnv.addInduct` contains them, so `InstalledBelow` fails for every
  container with at least one generated rule in the environments the checker builds, and with
  it `VInductDecl.NestedFormationWF` (which requires the container to be `InstalledBelow`). The installed-blocks invariant uses
  `VEnv.InductInstalled venv decl := ∃ base installed, decl.WF base ∧ base.addInduct decl =
  some installed ∧ installed ≤ venv` (`Verify/Environment/Blocks.lean`) instead; wave 2/3 must
  restate `InstalledBelow` (or nested formation) on `addInduct`.

Parked:

| item | why | owner |
|---|---|---|
| `Verify/CanonicalEq.lean` | needs `Verify/Inductive/Prelude/EqSyntax.lean` and a `VEnv.HasCanonicalEq` whose `Eq.rec` rule is a pattern; `addDecl.WF` no longer needs it | wave 4 |
| `Verify/QuotInit.lean` | replaced by PR #43's `Verify/Environment/Quot.lean` | never |

## Wave 1A (checker verification)

`lake build` (default targets), `Lean4Lean.Tests` (with `AmbientContext` restored) and
`Lean4Lean.Experimental` are green. Outside `Theory/` the only `sorry`s are these two:

| statement | file | why | owner |
|---|---|---|---|
| `VEnvAt.recursorShapes` | `Verify/TypeChecker.lean` | the recursor and constructor telescopes (`VRecursorShape`, `VConstructorShape` at the constructor's own parameter count) of every visible recursor of a complete model. Recursor reduction needs them to show the constructor application of a well-typed ι redex saturated. On the source branch they were part of the installed-block invariant (`RecursorAlignmentCore`); `VInductDecl.WF` only records the syntactic `rec_shape`/`rules_ctor` (`CtorShape` does not say the constructor ends in its family at the parameter variables), so they must come from the formation data of the installed declaration. Every other fact the checker reads (`CheckerEnv`) is wave 1B's `CheckingEnv.Valid` or PR #43's `TrEnv.pats_iota'` | wave 2 (installed blocks) |
| `VEnv.Ordered.patsAvoidFreshConsts` | `Verify/Typing/ConstSupport.lean` | the `pat` case of `IsDefEq.noConsts`: the fixed parts of a registered rule's right-hand side avoid names absent from the environment. `VEnv.PatTyped` types a generic instance in an arbitrary context, so the template's constants are not bounded by the environment without a further argument. Used only by `VExpr.WF.noFreshConsts` (constructor positivity) | wave 2 (or a `PatWF` that types the template in the empty context) |

Interface for the waves that build on this one: the checker reads its environment through
`CheckerEnv safety env venv` (`Verify/TypeChecker/CheckerEnv.lean`), which extends
`CheckingEnv.Valid` by `shapes : RecursorShapesCoherent` and `iota : IotaRulesRegistered`
(`TrEnv.iotaRulesRegistered` proves the latter from `TrEnv`). An inductive declaration that runs
the checker in an intermediate environment must supply both there.
