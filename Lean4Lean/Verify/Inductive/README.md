# `Verify/Inductive`: the interface of the inductive refinement proof

This directory verifies the executable inductive checker against the abstract specification of
inductive declarations (`VInductDecl.WF` in `Theory/Inductive.lean`, `VEnv.addInduct` in
`Theory/Inductive/AddInduct.lean`), on top of the checker verification (`Verify/TypeChecker`)
and the environment model (`Verify/Environment`). Each phase of the executable has an interface
structure and a boundary theorem; the tables below list them in pipeline order. Every boundary
theorem is proved; the proofs depend on `sorryAx` only through the accepted open proof of
`OPEN_PROOFS.md`.

## Principle

Interface structures carry the facts their consumers use, stated in the foundation's
vocabulary (`Theory/`, `Verify/Typing`, `Verify/TypeChecker`, `Verify/Environment`). Producers
construct them from directory-internal invariants. A structure may carry fields its consumers
ignore; the boundary theorems' statements are the interface.

## What the pipeline consumes and produces

* From the checker verification: `CheckerEnv safety env venv`
  (`Verify/TypeChecker/CheckerEnv.lean`: `CheckingEnv.Valid` plus `RecursorShapesCoherent` and
  `IotaRulesRegistered`). The pipeline's context `ContextWF c` (`Context.lean`) carries all
  three environment facts, so `ContextSemantics.checkerEnv` gives the checker its `CheckerEnv`
  in every intermediate environment (header, constructor, projection stage).
* From the environment model: `VEnvs`/`VEnvs.WF` (`Verify/Environment/Model.lean`),
  `InstalledBlocks`, `InstalledBlocks.addInduct` and `CheckingEnv.Valid`
  (`Verify/Environment/Blocks.lean`), the translation relations `AddInduct`, `TrIndType`,
  `TrRecursor`, `TrInductDeclCore` and `insertConsts` (`Verify/Environment/Basic.lean`), and
  `VEnvs.WF.extendInductExact`/`extendUnsafeExact` (`Verify/Environment/Extension.lean`).
* To install a block the pipeline produces a `BlockCertificate safety env venv decl outEnv
  outVEnv` (`Install/BlockCertificate.lean`): `decl.WF venv`, the step witness `AddInduct
  safety env.constants venv decl outEnv.constants outVEnv`, and the facts
  `InstalledBlocks.addInduct` reads of the output environment (`MutualInductivesClosed`,
  `ConstructorOwnersPresent`, `InductInfosFromDecl`, cover, recursor majors,
  `ConstructorParameterAlignment`, `KLikeRecursor`). `BlockCertificate.extendSafeExact` and
  `BlockCertificate.extendUnsafeExact` install it into `VEnvs`, replaying the block at the
  other safety levels by `BlockCertificate.rebase`.
* The inductive case of `addDecl.WF` (`Verify/Environment.lean`) is
  `addInductiveDeclaration.preserves` (`Dispatch.lean`): the primitive branch
  (`checkPrimitiveInductive_eq_true_iff`), the ordinary branch (lowering with no auxiliary
  family, `Environment.addInductiveAfterLowering.ordinaryInductiveExtensionWF`) and the nested
  branch (`Environment.addInductiveAfterLowering.nestedInductiveExtensionWF`,
  `Nested/Install/Extension.lean`). `addInductiveDeclaration.spec` is the source-facing form
  (`InductiveExtension`), under `SourceBVarClosed`.

## The phases and their interfaces (in pipeline order)

| phase (executable) | interface structures | boundary theorem | file |
|---|---|---|---|
| context | `ContextWF c` | `ContextWF.initial` | `Context.lean` |
| certificates | `HeaderCertificate`, `ConstructorCertificate`, `FormationCertificate`, `RecursorsWF` | `FormationCertificate.wf` | `Formation.lean` |
| `checkInductiveTypes` | `CheckedHeaders`, `HeaderParameterContext`, `HeaderPhase` | `AddInductive.checkInductiveTypes.WF` | `Header/Check.lean` |
| `declareInductiveTypes` | `HeaderEnvironment`, extending `HeaderData` | `AddInductive.declareInductiveTypes.WF` | `Header/Installation.lean`, `HeaderData.lean` |
| `constructorPhase` (headers, `checkConstructors`, `declareConstructors`) | `ConstructorCheck` (one structure for the ordinary and the primitive path) | `AddInductive.constructorPhase.WF` | `ConstructorCheck.lean`, `Constructor/Check.lean` |
| recursor suffix of `AddInductive.run` | `RecursorCheck R outEnv` (= `RecursorInstallation R outEnv`) | `ConstructorCheck.recursorPhasesWF` | `Recursor/Check.lean`, `Recursor/Installation.lean` |
| rules | `RuleTranslations H` | `RecursorCheck.generatedRuleTranslation` | `Rules/RuleTranslations.lean` |
| assembly | `BlockCertificate` | `RecursorCheck.blockCertificate`, `BlockCertificate.installedBlocks`, `BlockCertificate.rebase`, `BlockCertificate.extendSafeExact`, `BlockCertificate.extendUnsafeExact` | `Install/BlockCertificate.lean` |
| `AddInductive.run` | `OrdinaryInstallation`, `OrdinaryRunResult`, `PrimitiveNamesFresh` | `Kernel.Environment.checkDuplicatedUnivParams.WF` | `Install/Ordinary.lean` |
| `addInductiveAfterLowering` (ordinary) | | `AddInductive.run.extensionModelWF`, `Environment.addInductiveAfterLowering.ordinaryExtensionModelWF` | `Install/OrdinaryExtension.lean` |
| `checkInductiveSources`, `ElimNestedInductive.run` | `SourceSyntaxChecks`, `NestedLoweringOutput` (of `loweringRun`) | `loweringRun.WF`, `Environment.addInductive.WF` | `Lowering.lean` |
| primitive branch | `PrimitiveInductiveShape`, `PrimitiveInstallation`, `PrimitiveRunResult` | `checkPrimitiveInductive_eq_true_iff`, `loweringRun.primitiveNoop`, `AddInductive.constructorPhase.primitiveWF` | `Primitive/Shape.lean`, `Primitive/Run.lean`, `Primitive/Extension.lean` |
| result, dispatch | `SourceAddInduct`, `InductiveExtension` | `addInductiveDeclaration.WF`, `addInductiveDeclaration.spec`, `addInductiveDeclaration.preserves` | `Install/Result.lean`, `Dispatch.lean` |

The installed declaration is `decl.withRecs recs` (`Basic.lean`): the constructor phase fixes
the source part, the recursor phase adds the generated recursors with their `VRecRule`s.
Judgments indexed by the declaration transport by `TrInductDeclCore.withRecs` and
`FormationCertificate.withRecs` (`Formation.lean`).

Directories: `Context.lean`, `Context/**`, `Formation.lean`, `Header/**` (header phase);
`Constructor/**`; `Recursor/**`; `Rules/**`; `Install/**`, `Primitive/**`, `Prelude/**`
(installation, the primitive `Bool`/`Nat` path and the prelude's `Eq`); `Basic.lean`,
`Lowering.lean`, `Dispatch.lean` (shared statements); `Nested/**` (the nested branch, below).

## Dependencies between the phases

The header phase depends on nothing above it. The constructor phase consumes
`HeaderPhase`/`HeaderEnvironment`. The recursor phase consumes the constructor phase's
telescope data (`ConstructorTails`, `ConstructorParameterPrefixes`,
`ConstructorOwnerNormalForms`) as fields of `ConstructorCheck`; the primitive path, which also
produces a `ConstructorCheck`, supplies them too. The rule phase consumes the recursor phase's
internals (rule templates, minor contexts, `canonicalGeneration`, the `RuleAlignment` inputs).
The installation needs the final shapes of all four interfaces; the model installation
(`rebase`, `extendSafeExact`, `extendUnsafeExact`, `installedBlocks`) and `Primitive/Shape.lean`
depend on nothing upstream.

## Interface decisions

* `TrRecursor` is the recursor translation; `VInductDecl.RecsOf` is read off the block
  `RuleTranslations.block`, whose recursors and rules are the generator's
  (`generation.recursors`, `generation.equations`).
* `rules_wf : PatTyped` is a field of `RuleTranslations`; `equationsWF : VDefEq.WF` stands
  beside it because the compiled block's `VInductBlock.WF` (needed by `CompiledInductive`,
  `ContainersInstalled`, `InstalledBelow`) types the equations.
* A container of a nested declaration is certified by `ContainersInstalled.cons` and
  `VEnv.InstalledBelow.intro` from `CompiledInductive base container block`, `block.WF base`,
  `container.RecsOf block` and `base.addInduct container = some installed` with
  `installed ≤ env`. The checker produces these from `VEnv.InductInstalled`
  (`decl.WF base ∧ base.addInduct decl = some installed ∧ installed ≤ venv`):
  `VInductDecl.WF.recsCompiled` gives the block with `CompilesTo` and `RecsOf`, and `block.WF
  base` needs the equations' `VDefEq.WF`.
* For the ι clause of the observation model (`Model.PatValid.ordinary` and
  `Model.PatValid.nested`): every complete installed block exposes its whole `VInductDecl.WF`
  through `InstalledBlocks` (`InstalledBlock.Abstract.installed : VEnv.InductInstalled venv
  B.decl`). Structure eta is a `VEnv.projections` fact through `projectionEntries`
  (`VEnv.addInduct_projections_iff`). The kernel metadata is in `AddInduct.ivals`/`rvals` with
  `TrIndType`/`TrRecursor`.
* `VEnvAt.recursorShapes` (`Verify/TypeChecker.lean`) is consumed by `ContextWF.initial`; it is
  proved from `InstalledBlocks`.
* `ContextWF` has no cache-mode field (there is one cache mode).

## The nested branch

`Nested/**` verifies the nested branch on the same principle. Its entry point is
`Environment.addInductiveAfterLowering.nestedInductiveExtensionWF`
(`Nested/Install/Extension.lean`), which `Dispatch.lean` uses for a lowering result with
auxiliary families. The executable's nested branch is `AddInductive.run` on the lowered block
followed by `Environment.restoreNestedAfterInstall` (restore the source declaration from the
lowered environment, then four validation passes in side environments).

### Pipeline and interfaces (in order)

| phase (executable) | interface | boundary theorem | file |
|---|---|---|---|
| `ElimNestedInductive.run` (`loweringRun`) | `NestedLoweringOutput env fuel nparams sourceTypes lparams res` | `loweringRun.WF` | `Lowering.lean`; consequences in `Nested/Lowering/Basic.lean` and `Nested/Lowering/Output.lean` (`NestedLoweringOutputClosed`) |
| `AddInductive.run` on `res.types` | `LoweredRun Hc nparams indTypes loweredEnv`: the header phase from the source context, the constructor check and the recursor installation of the lowered block | `AddInductive.run.loweredRun` | `Nested/Restoration/LoweredRun.lean` |
| `restoreNestedAfterInstall` | `RestorationRun`: the restoration fold's output, the two side environments and the four passes' `= .ok ()` | `Environment.restoreNestedAfterInstall.WF` | `Nested/Restoration/RestorationRun.lean` |
| the validation passes | checker-facing: under `CheckerEnv safety E V` for the side environment `E`, each pass yields `TrExprS`/typing in `V` | `validateSourceConstructorTypes.run.WF`, `validateRestoredRecursorTypes.check.WF`, `validateRestoredRecursorTypes.run.WF`, `validateRestoredRecursorRules.check.WF`, `validateRestoredRecursorRules.run.WF`, `validateNestedAuxiliaries.WF_typing`, `stripRecursorRules.checkingValid` | `Nested/Restoration/Validation/Passes.lean` |
| restoration | `NestedRun` (the data of a successful nested execution), `RestoredBlock L sourceTypes isUnsafe outEnv` (the source declaration with restored recursors, its translation and nested formation, the specialization list with `ContainersInstalled`, the `CompilationData` of the lowered run's generator, the kernel constants with `TrIndType`/`TrRecursor`, the shape clauses of `VInductDecl.WF`) | `nestedRestoredBlock` | `Nested/Restoration/Run.lean`, `Nested/Restoration/Certificate.lean`, `Nested/Restoration/Restore.lean` |
| rule typing | | `RestoredBlock.rulesWF`, `RestoredBlock.blockWF` | `Nested/Equations/Rules.lean` |
| installation | `RestoredBlock.Installed B` | `RestoredBlock.installedFacts` | `Nested/Install/Installed.lean` |
| result | `NestedCertificate` (the block certificate plus the source translation) | `NestedCertificate.inductiveExtension`, `Environment.addInductiveAfterLowering.nestedInductiveExtensionWF` | `Nested/Install/Result.lean`, `Nested/Install/Extension.lean` |

Theory files of the nested branch: `Theory/Typing/Interpretation.lean` (environment
interpretations; `PatClause` is the obligation for a registered ι rule, with
`PatClause.of_fixed` for rules the interpretation fixes),
`Theory/Inductive/RestorationInterpretation.lean` (the restoration interpretation and
substitution), `Theory/Typing/RestorationShapes.lean`, `Theory/Inductive/RestorationHead.lean`,
`Theory/Inductive/Restoration.lean`, `Theory/Inductive/CompilationMajors.lean` (what
`WF.patCtor_rigid` needs, below).

### What the nested `VInductDecl.WF`/`RecsCompiled` instance provides for the model

The head-inversion model (`Theory/Typing/HeadInjectivity/Model/`) reads two kinds of facts
off an installed block; the nested instance provides them through `RestoredBlock`:

* **`WF.patCtor_rigid`** (`Model/WFFacts.lean`): the constructor of every rule of every
  recursor of an installed block is a constructor of the block or of an installed container.
  Stated in Theory as `CompiledInductive.rule_ctor_cases`
  (`Theory/Inductive/CompilationMajors.lean`): for `CompiledInductive env source block` and
  `source.RecsOf block`, every `ru ∈ r.rules` with `r ∈ source.recs` has `ru.ctor` a
  constructor constant of `source` or `VEnv.IsPatCtor env ru.ctor` (the container's own ι rule
  on that constructor is registered in `env`: `ContainersInstalled.constructor_isPatCtor`). Its
  ingredients are `Instance.restored_equation_major` and
  `CompilationData.constructor_name_cases`. The history induction of `patCtor_rigid` recurses
  on the container's pattern, added strictly earlier.
* **`Model.PatValid.nested`** (`Model/PatSound.lean`): what the ordinary path gets from
  `RecsCompiled` and `VInductBlock.WF` holds for restored blocks too.
  `RestoredBlock.recsCompiled` packages the `CompilationData` of the restored block, so (i)
  every installed `VRecRule` is `OfEquation` of a block equation that is the restoration of a
  generated equation of the lowered run's generator (`RestoredBlock.rules_ofRestoredEquation`);
  (ii) the restored equation's λ-binders agree with the restored recursor's Π-telescope because
  both are `Restoration.expr` of the generator's (`Theory/Typing/RestorationShapes.lean`);
  (iii) the equations are typed in the empty context of the restored recursor stage
  (`RestoredBlock.blockWF`, through `Restoration.equation_wf`); (iv) the auxiliary recursors'
  rules fire on container constructors at the container's parameter count (`rules_ctor` finds
  the constructor in the constructor stage, where the container is installed below). Structure
  eta and the projection entries are generic: `VEnv.addInduct_projections_iff` on
  `decl.projectionEntries`, as for ordinary blocks.

### Directories

* `Nested/Lowering/**`: the lowering refinement, used by `loweringRun.WF` (`Lowering.lean`).
* `Nested/Restoration/Validation/**`, `Nested/Restoration/Uniform/**`: the statements of
  `Validation/Passes.lean` and the parameter uniformity of the lowered recursors.
* The rest of `Nested/Restoration/**`: `nestedRestoredBlock` (`Restore.lean`).
* `Nested/Equations/**`, `Nested/Install/**`: `rulesWF`, `blockWF` (`Equations/Rules.lean`),
  `installedFacts` (`Install/Installed.lean`), the certificate and the entry point
  (`Install/Result.lean`, `Install/Extension.lean`).

### Dependencies between the nested phases

1. The lowering and the validation passes depend on nothing above them; neither reads the
   other's output (the validation statements are checker-facing, over a `CheckerEnv` the caller
   supplies).
2. The restoration consumes `NestedLoweringOutput` and the validation passes (the side
   environments' models are built from the restoration folds and instantiate `Passes.lean`'s
   statements). The Theory facts of `CompilationMajors.lean` depend on nothing upstream.
3. The rule typing and installation consume `RestoredBlock` (rule typing over `B.envR` and the
   lowered run's rule translations; the environment-side facts over `B.addInduct`).

### Interface decisions (nested)

* The restoration inverse is stated up to `Expr.eqv` (`==`)
  (`ConstructorRestorationInverse.restoredType_eqv_source`); consumers translate through
  `TrExprS.eqv`. The zero-auxiliary identity stays literal.
* `NestedLoweringOutput` is syntactic (kernel `Expr`s, `env.find?`); the typing of the cached
  occurrences comes from the validation pass `validateNestedAuxiliaries`
  (`validateNestedAuxiliaries.WF_typing`), not from lowering.
* `RestoredBlock` carries `CompilationData` against the lowered run's generator, so the rule
  typing transports the lowered run's rules along `compilationRestoration decl auxiliaries`
  without re-deriving the generator.
* `Interpretation.Sound.ordered` is `OrderedStrong` (`IsDefEq.instL_r` and `BetaRed.simAt`
  need it); `Sound` has a `pats` clause.
* `RestoredBlock.Installed` is a separate Prop structure so that the environment-side
  reasoning on the output is separate from the restoration data.
