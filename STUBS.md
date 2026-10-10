# Stub ledger: verified inductives on the ι pattern calculus

Every `sorry` in `Lean4Lean/Theory/` (the `Lean4Lean.Theory` library builds every file under
that directory), with its owner wave. `lake build Lean4Lean.Theory`, `Lean4Lean.Experimental`,
`Lean4Lean.Tests.IotaShape` and `Lean4Lean.Tests.ShapeDecide` are green at wave 0;
`Lean4Lean.Verify` is not yet imported (waves 1 to 3) and the `lake build` default target
therefore fails on `Verify/` until wave 1. Waves follow `iota-port/PLAN-RECONCILED.md`.

| statement | file | origin | owner |
|---|---|---|---|
| `VEnv.WF.patsStrong` | `Theory/Typing/EnvLemmas.lean` | PR #43 | wave 1D (`patsStrong`), after the 0b spike |
| `VEnv.WF.chainHeadInjectivity` (`-- WAVE 0 STUB`) | `Theory/Typing/HeadInversion.lean` | glued observation model, `HeadInjectivity/Model/EnvValid.lean` on the source branch | wave 1C (port the model with a `pat` clause in `RuleSound`) |
| `VEnv.WF.headSeparationModel` (`-- WAVE 0 STUB`) | `Theory/Typing/HeadInversion.lean` | glued observation model, `HeadInjectivity/Model/Separation.lean` on the source branch | wave 1C |
| `IsDefEqU.weakN_iff` | `Theory/Typing/UniqueTyping.lean` | master | open on master; the one strengthening principle the checker uses (PORT_PLAN section 5) |
| `NormalEq.parRed` (two `sorry`s, the `extra` cases) | `Theory/Typing/ChurchRosser.lean` | master | wave 4 (confluence retargeted onto `env.pats` supersedes this file) |

Not stubs but conditional results: everything through `VEnv.WF.orderedStrong` (the strong
system, substitution theorems, inversion lemmas) depends on `patsStrong`; everything through
`VEnv.WF.headInversion` and `IsDefEq.uniq` depends on the two model stubs. `Injectivity.lean`
has no `sorry` of its own: PR #43's `IsDefEqU.const_arity_inv` is derived from
`VEnv.WF'.inductTypeRigid` and `headInversion`.

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

## Wave 1A

| statement | file | why | owner |
|---|---|---|---|
| `VEnv.Ordered.patsAvoidFreshConsts` | `Verify/Typing/ConstSupport.lean` | the `pat` case of `IsDefEq.noConsts`: the fixed parts of a registered rule's right-hand side avoid names absent from the environment. `VEnv.PatTyped` types a generic instance in an arbitrary context, so the template's constants are not bounded by the environment without a further argument. Used only by `VExpr.WF.noFreshConsts` (constructor positivity) | wave 2 (or a `PatWF` that types the template in the empty context) |
