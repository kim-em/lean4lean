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
