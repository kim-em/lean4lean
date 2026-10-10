# `Verify/Inductive`: the interface of the inductive refinement proof

Wave 2 scaffold (branch `agent/iota-w2-scaffold`). This directory makes the verification of the
executable inductive checker exist on the merged foundation (PR #43's calculus and `addInduct`,
wave 1A's checker verification, wave 1B's environment model) as a buildable skeleton: every
cross-directory statement is in place, every proof that is not yet ported is a named stub listed
in the "Wave 2 scaffold" section of `STUBS.md`. Five agents fill the directories in parallel
without touching each other's files or this interface.

## Principle

Interface structures carry the facts their consumers use, stated in the foundation's
vocabulary (`Theory/`, `Verify/Typing`, `Verify/TypeChecker`, `Verify/Environment`). Producers
construct them from directory-internal invariants, which they port freely from the source branch
(`/home/kim/worktrees/lean4lean/lean4lean-agent-verify-inductives`, commit `0dc2c7b3`). The
interface files below are frozen: an agent may *add* fields to a structure it produces (the
consumers ignore them) and add theorems, but may not rename, remove or retype a field or change
a boundary theorem's statement without the lead. Removals and retypings go through the lead.

## What the pipeline consumes and produces

* From wave 1A: `CheckerEnv safety env venv` (what the checker reads: `CheckingEnv.Valid` plus
  `RecursorShapesCoherent` and `IotaRulesRegistered`) and `VContext`/`MLCtx`/`CheckBase`. The
  pipeline's context `ContextWF c` (`Context.lean`) carries all three environment facts, so
  `ContextWF.checkerEnv` gives the checker its `CheckerEnv` in every intermediate environment
  (header, constructor, projection stage).
* From wave 1B: `VEnvs`/`VEnvs.WF`, `InstalledBlocks` and `InstalledBlocks.addInduct`,
  `CheckingEnv.Valid`, `EquationHeadsCoherent` (through `CheckingEnv.Valid.equationHeads`),
  PR #43's `AddInduct`, `TrIndType`, `TrRecursor`, `insertConsts`, `TrEnv'.induct`,
  `VEnvs.WF.extendInductExact`/`extendUnsafeExact`, `TrInductDeclCore`.
* To install a block the pipeline produces a `BlockCertificate safety env venv decl outEnv
  outVEnv` (`Install/BlockCertificate.lean`): `decl.WF venv` (all of `VInductDecl.WF`'s fields:
  `source`, `formation`, `recsCompiled`, `recs_wf`, `rec_shape`, `rules_nodup`, `rules_ctor`,
  `rule_shape`, `rules_wf : PatTyped`), PR #43's `AddInduct safety env.constants venv decl
  outEnv.constants outVEnv` (stages `stT`/`stC`/`stR`/`stP`, `TrIndType`, `TrRecursor` with
  `VRecRule`s read off the generator's equations, `order`/`fresh`/`map_eq`), and the facts
  `InstalledBlocks.addInduct` reads of the output (`MutualInductivesClosed`,
  `ConstructorOwnersPresent`, `InductInfosFromDecl`, cover, recursor majors,
  `ConstructorParameterAlignment`, `KLikeRecursor`). `BlockCertificate.extendSafeExact` and
  `extendUnsafeExact` install it into `VEnvs` (`VEnvs.WF.extendInductExact`, replaying the
  block at the other safety levels by `BlockCertificate.rebase`; `VEnvs.WF.extendUnsafeExact`
  with `TrEnv'.ignore` for the hidden observers).
* `InductiveDeclPreserves` (wave 1B's exact statement, `Verify/Environment.lean`) is now the
  theorem `inductiveDeclPreserves (hnested : NestedInductivePreserves)`, from
  `addInductiveDeclaration.WF_preserves` (`Dispatch.lean`): the primitive branch
  (`Primitive.checkInductive = .ok true`, `checkPrimitiveInductive_eq_true_iff`), the ordinary
  branch (lowering with no auxiliary family) and the nested branch, the latter being the
  hypothesis `NestedInductivePreserves` (layer-5 style; wave 3 proves it). `addDecl.WF` takes
  `hnested`; `addDecl.WF_of` keeps the `InductiveDeclPreserves` form. `addInductiveDeclaration.WF_spec`
  is the source-facing form (`InductiveExtension`), under `SourceBVarClosed`.

## The phases and their interfaces (in pipeline order)

| phase (executable) | interface structure | boundary theorem (stub) | file | owner |
|---|---|---|---|---|
| context | `ContextWF c` (frozen fields; `initial`, `withEnv` proved) | | `Context.lean` | Header |
| certificates | `HeaderCertificate`, `ConstructorCertificate`, `FormationCertificate`, `RecursorsWF`, `FormationCertificate.wf : decl.WF` (proved), `TrInductDeclCore.*` | `TrInductDeclCore.sourceNames_nodup`, `ConstructorCertificate.withRecs` | `Formation.lean` | Header (`withRecs`: Install) |
| `checkInductiveTypes nparams indTypes k` | `CheckedHeader(s)`, `CheckedHeaders.Describes`, `HeaderParameterContext`, `HeaderPhase Hc nparams indTypes c' Hc' stats` | `AddInductive.checkInductiveTypes.WF`, `Describes.headerCertificate` | `Header/Check.lean` | Header |
| `declareInductiveTypes` | `HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv indTypes outEnv` (decl-indexed; only header data constrained) | `AddInductive.declareInductiveTypes.WF` (`∀ decl, Describes → HeaderEnvironment`) | `Header/Installation.lean` | Header |
| `checkConstructors` | `CheckedFormation` (header env, `TrInductDeclCore`, `FormationCertificate`, `classes`) | `CheckedFormation.signature` (∃ `s`, `s.Models sourceEnv decl ∧ FamilyTypesWF headerVEnv`) | `Constructor/CheckedFormation.lean` | Constructor |
| `constructorPhase` (= headers + checkConstructors + declareConstructors) | `ConstructorCheck` extends `CheckedFormation`: `ivals`, `trTypes : TrIndType`, `map_eq`/`fresh`, `context : ContextWF {c with env := ctorEnv}` over `envP = ctorVEnv.addProjections decl.projectionEntries`, `closed`, `inductInfosFromDecl`, `constructorParameterAlignment` | `AddInductive.constructorPhase.WF` | `Constructor/Check.lean` | Constructor |
| recursor suffix of `runWithStats` | `RecursorCheck R outEnv`: `rvals`, `recs`, `outVEnv`, `recsAdded`, `trRecs : TrRecursor`, `map_eq`/`fresh`, `checking`, the shape clauses `recsWF`/`rec_shape`/`rules_nodup`/`rules_ctor`/`rule_shape`/`rules_closed`, `kLike`, the generator (`signature`, `generation`, `models`, `admissible`, `ihsWellTyped`, `familyTypesWF`, `recursors_eq`, `metadata`) | `ConstructorCheck.recursorPhasesWF`, `VRecRule.OfEquation.ofTr` | `Recursor/Check.lean`, `Recursor/Entries/TrRecursorVal.lean` | Recursor |
| rules | `RuleTranslations H` (Prop): `trRules : TrRecursorRule` coverage, `equationsWF : VDefEq.WF`, `rules_wf : PatTyped`; derived `block`, `compiles` (proved), `blockWF`, `compilesTo`, `recsOf`, `recsCompiled`, `recursorsWF` (proved from the stubs) | `RecursorCheck.generatedRuleTranslation`; `blockWF`/`compilesTo`/`recsOf` (Install) | `Rules/RuleTranslations.lean` | Rules (derived facts: Install) |
| assembly | `BlockCertificate`, `RecursorCheck.outVEnv'` | `RecursorCheck.blockCertificate`, `BlockCertificate.installedBlocks`/`rebase`/`extendSafeExact`/`extendUnsafeExact` | `Install/BlockCertificate.lean` | Install |
| `AddInductive.run` | `OrdinaryInstallation`, `OrdinaryRunResult`, `PrimitiveNamesFresh` (glue proved) | `Kernel.Environment.checkDuplicatedUnivParams.WF` | `Install/Ordinary.lean` | Install |
| `addInductiveAfterLowering` (ordinary) | `OrdinaryInstallation.extend*Exact`, `extensionModelWF`, `ordinaryInstalledModelWF`, `ordinaryExtensionModelWF` (all proved) | | `Install/OrdinaryExtension.lean` | Install |
| `checkInductiveSources`, `ElimNestedInductive.run` | `SourceSyntaxChecks`, `SourceBVarClosed`, `loweringRun`, `Environment.addInductive.WF` (proved) | `loweringRun.types_nonempty`, `loweringRun.ordinary_types_eq_source` | `Lowering.lean` | wave 3 (`Nested/Lowering`) |
| primitive branch | `PrimitiveInductiveShape`, `primitiveAddInductiveContext`, `PrimitiveInstallation`, `PrimitiveRunResult`; extension chain proved | `checkPrimitiveInductive_eq_true_iff`, `loweringRun.primitiveNoop`, `AddInductive.constructorPhase.primitiveWF`, recursor names not primitive (in `primitiveSourceAlignedWF`) | `Primitive/{Shape,Run,Extension}.lean` | Primitive |
| result, dispatch | `SourceAddInduct` (`decl.WF ∧ addInduct = some`), `InductiveExtension`, `NestedInductivePreserves`, `addInductiveDeclaration.WF`/`WF_spec`/`WF_preserves` (proved) | | `Install/Result.lean`, `Dispatch.lean` | shared (lead) |

The installed declaration is `decl.withRecs recs` (`Basic.lean`): the constructor phase fixes
the source part, the recursor phase adds the generated recursors with their `VRecRule`s. The
source fields reduce (`simp` lemmas `withRecs_*`); judgments indexed by the declaration transport
by `TrInductDeclCore.withRecs`, `FormationCertificate.withRecs` (`Formation.lean`).

## Ownership map

* **Header**: `Context.lean`, `Context/**` (new), `Formation.lean`, `Header/**`.
* **Constructor**: `Constructor/**`.
* **Recursor**: `Recursor/**`.
* **Rules**: `Rules/**`.
* **Install**: `Install/**`, `Primitive/**`, `Prelude/**` (absent in the scaffold; `Tests/PreludeEq`
  stays deferred to wave 4), plus the derived facts in `Rules/RuleTranslations.lean`
  (`blockWF`, `compilesTo`, `recsOf`) and `ConstructorCertificate.withRecs` in `Formation.lean`.
* **Shared (lead)**: `Basic.lean`, `Install/Result.lean`, `Lowering.lean` (statements; proofs are
  wave 3's), `Dispatch.lean`, `Inductive.lean`, this file, `Verify/Environment.lean`.

## Dependency order

All five agents can start at once on the bulk of their directories (telescope, binder and
translation lemmas against the frozen foundation). The boundary theorems land in this order:

1. **Header** (`checkInductiveTypes.WF`, `declareInductiveTypes.WF`): nothing above it. The
   Constructor agent needs `HeaderPhase`/`HeaderEnvironment` only as hypotheses, so it can
   proceed in parallel; but the constructor check runs in the header context's parameter
   scope, so internal facts about that scope beyond `HeaderParameterContext` (the source
   branch's `HeaderStatsWF.normalizedShapes`, the concrete index telescopes) are requested
   from the Header agent as *additional fields* of `HeaderPhase`/`HeaderEnvironment`.
2. **Constructor** (`constructorPhase.WF`, `CheckedFormation.signature`): after Header's
   additions. The Recursor agent needs the constructor phase's internal telescope data (the
   source branch's `ConstructorTails`, `ConstructorParameterPrefixes`,
   `ConstructorOwnerNormalForms`, `SourceCtorsCertified`) as additional fields of
   `ConstructorCheck`; the Constructor agent adds them (the Primitive agent, who also produces
   `ConstructorCheck`, must then supply them: Primitive after Constructor).
3. **Recursor** (`recursorPhasesWF`, `VRecRule.OfEquation.ofTr`): after Constructor's additions.
   The Rules agent consumes the recursor phase's internals (rule templates, minor contexts,
   `canonicalGeneration`); the source branch's `RuleRhsTranslations` is stated against them, so
   Rules' boundary theorem lands after Recursor's `RecursorCheck` is final (additional fields:
   `recInfos`, `elimLevel` data, the `RuleAlignment` inputs).
4. **Rules** (`generatedRuleTranslation`): after Recursor.
5. **Install** (`blockCertificate`, `extend*Exact`, the derived `RuleTranslations` facts,
   `Primitive/**`): the assembly needs the final shapes of all four interfaces; the model
   installation (`rebase`, `extendSafeExact`, `extendUnsafeExact`, `installedBlocks`) and
   `Primitive/Shape.lean` depend on nothing upstream and can start immediately.

Wave 3 (nested) discharges `NestedInductivePreserves` and the two `Lowering.lean` stubs.

## Interface decisions for the lead and owners

* `TrRecursor` (PR #43) is used as is for the recursor translation; `TrRecursorRule`/
  `RecursorMetadata`/`TrRecursorVal` of the source branch are kept for the generator side, and
  `VRecRule.OfEquation.ofTr` bridges them (via `TrExprS.unique`). `VInductDecl.RecsOf` is read
  off the block `RuleTranslations.block` with `recursors := generation.recursors`,
  `rules := generation.equations`.
* `rules_wf : PatTyped` is a field of `RuleTranslations` (the Rules agent restates
  `generatorEquationWF` as the generic instance, PORT_PLAN section 2.3); `equationsWF :
  VDefEq.WF` is kept beside it because the compiled block's `VInductBlock.WF` (needed by
  `CompiledInductive`, `ContainersInstalled`, `InstalledBelow`) still types the equations.
* Theory COMPAT (`-- WAVE 2 COMPAT`, commit `17e28233`): `VEnv.addInduct`'s stages and
  `VInductDecl.RecsOf`/`VRecRule.OfEquation` moved to `Theory/Inductive/AddInduct.lean`;
  `ContainersInstalled.cons` and `VEnv.InstalledBelow.intro` now read
  `CompiledInductive base container block → block.WF base → container.RecsOf block →
  base.addInduct container = some installed → installed ≤ env` (the `VInductBlock.install`
  premise replaced by `RecsOf` and `addInduct`); the `InstalledBelow` lookup lemmas
  (`projection`, `familyConstant`, `constructorConstant`) moved to
  `Theory/Typing/InductiveLemmas.lean`. The checker produces these from `VEnv.InductInstalled`
  (`decl.WF base ∧ base.addInduct decl = some installed ∧ installed ≤ venv`): `WF.recsCompiled`
  gives the block with `CompilesTo` and `RecsOf`; `block.WF base` needs the equations' `VDefEq.WF`,
  which is why `RuleTranslations.equationsWF` is kept.
* For wave 1C's `Model.PatValid.iota` stub: every complete installed block exposes its whole
  `VInductDecl.WF` through `InstalledBlocks` (`InstalledBlock.Abstract.installed :
  VEnv.InductInstalled venv B.decl`), hence `rec_shape`, `rules_ctor`, `rules_nodup`,
  `rule_shape`, `recs_wf`, `rules_wf` and the formation data (`FormationWF` →
  `OrdinaryFormationWF`: `TypeShape` for the family sort, `CtorShape`/`CtorTailWF` for the
  singleton proof binders) and `recsCompiled` (the signature: fields, induction hypotheses).
  `PatsIota` is PR #43's theorem on `pats`. Structure eta is a `VEnv.projections` fact through
  `projectionEntries` (`addInduct_projections_iff`). The `BlockCertificate` adds nothing beyond
  `decl.WF` and `AddInduct` at the instance level; if the stub needs the kernel metadata it is in
  `AddInduct.ivals`/`rvals` with `TrIndType`/`TrRecursor`.
* Wave 1A's two stubs stay: `VEnvAt.recursorShapes` (`Verify/TypeChecker.lean`) is consumed by
  `ContextWF.initial`; it is provable from `InstalledBlocks` once `decl.WF`'s `rec_shape`/
  `rules_ctor` are turned into `VRecursorShape`/`VConstructorShape` (Install agent, with the
  Theory shape lemmas). `VEnv.Ordered.patsAvoidFreshConsts` (`Verify/Typing/ConstSupport.lean`)
  is untouched by the pipeline's statements.
* `ContextWF` lost the cache-mode field (cache modes are gone) and gained `shapes`/`iota`.
  `ConstructorTailCertificate.uniform` keeps `VInductDecl.UniformCtorTail`
  (`Theory/Inductive/Normalization.lean`).
