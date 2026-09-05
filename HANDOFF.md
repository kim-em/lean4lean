# Handoff: inductive verification

## Goal

Make inductive verification genuinely complete and sound. The final ordinary,
primitive, and nested-inductive correctness theorems should be free of
`sorryAx`, and every checker step should refine the abstract calculus without
caller-supplied certificates or hypotheses that are never discharged.

## Current state (2026-09-05)

The branch replaces projection expansion certificates with primitive projection
syntax and stages installation as types, constructors, projections, then
recursors. The full default build passes. No new commits exist on the remote
default branch (`origin/master`), so there is nothing to merge.

The final theorems (`addInductiveDeclaration.inductiveFinalResultWF`,
`addInductiveDeclaration.primitiveInductiveFinalResultWF`,
`Environment.addInductiveAfterLowering.nestedInductiveFinalResultWF`) still
report `sorryAx`. A dependency trace (walk the constant graph with theorem
bodies loaded via `ConstantInfo.value? (allowOpaque := true)`;
script in `/tmp/l4l-audit/Audit2.lean` during the session) shows exactly
eleven declarations that introduce `sorry` into that closure:

Theory (the injectivity/strengthening conjectures; `Injectivity.lean`,
`UniqueTyping.lean`; the first four are also open on `master`):

- `VEnv.IsDefEqU.sort_inv`
- `VEnv.IsDefEqU.forallE_inv_stratified`
- `VEnv.IsDefEqU.sort_forallE_inv`
- `VEnv.IsDefEqU.weakN_iff` (strengthening for definitional equality)
- `VEnv.IsDefEqU.fieldType_inv_stratified` (the `proj` case of `IsDefEq.uniq`)
- `VEnv.IsDefEqU.rigidApp_inv`, `VEnv.IsDefEqU.structApp_inv` (injectivity of
  applications of rigid constants; the second is the first for a registered
  structure and becomes redundant once rigidity is carried in the checking
  environment, see `EquationHeadsCoherent`)

Checker (`Verify/TypeChecker/*`):

- `inferProj.WF` (projection type inference)
- `VContext.registryShape` (projection registry facts for a checking context)
- `VContext.recursorRules`, `VContext.quotCoherent` (recursor rule and quotient
  facts for a checking context; `Verify/Environment/Recursors.lean` has the
  predicates, their monotonicity, `AddQuot.quotCoherent`, and
  `EquationHeadsCoherent` for rigidity)

`Params` (Church–Rosser) is never instantiated; `HeadReduction.lean` and
`ChurchRosser.lean` are a parameterized development that already depends on the
injectivity conjectures through `IsDefEq.uniq`, so they cannot currently be
used to discharge them. The `Experimental/` directory holds several attempts
(logical relations, stratification, Coquand–Huber adequacy) at that core
metatheory. Treat the injectivity conjectures as the known open core.

## Design decisions taken in this session

1. Abstract projection computation is a primitive `IsDefEq` rule `projIota`
   (projection of a constructor application reduces to the field), not a
   `VDefEq` rule: the stored rules cannot be pattern-matched by
   `ChurchRosser.lean` anyway, and a primitive rule keeps `reduceProjCore`
   refinement local. The rule carries the typing of both sides as premises so
   that `IsDefEq.hasType` stays structural.
2. Structure eta (`structEta`) and unit-like equality (`unitLike`) are
   primitive `IsDefEq` rules with explicit typing premises, for the same
   reason.
3. The executable `reduceProjCore` and `inferProj` receive small, documented
   guards (constructor must be the unique constructor of the projected
   structure; field index below the constructor's field count). Both are
   redundant on well-typed input and match the newer C++ kernel.
4. Rigid-constant application injectivity is stated as a named conjecture
   next to `forallE_inv_stratified` and used by `uniq` and by
   `reduceProjCore.WF`; it is the one genuinely new theory obligation and is
   of the same class as the existing ones.
5. The projection registry is registered right after the family headers
   (`inductProjectionsEarly`) so that `ProjectionRegistryCoherent` holds in
   every staged checking environment and can live inside `CheckingEnv.Valid`.

## Progress in this session (2026-09-05)

- New abstract rules `projIota`, `structEta`, `unitLike` (Theory/Typing/Basic.lean) with all
  metatheory cases closed (Lemmas, Strong, Verify/Typing); Church–Rosser has three marked
  placeholder cases for them.
- `IsDefEq.uniq`'s projection case is closed via the conjecture
  `IsDefEqU.fieldType_inv_stratified` (Injectivity.lean); rigid-application injectivity is
  stated as `IsDefEqU.rigidApp_inv` / `structApp_inv`.
- Theory/Typing/ProjectionLemmas.lean: typed telescope walks (`InstForalls`), their congruence,
  spine typing against a telescope, substituted-subterm well-formedness, full telescope
  instantiation (`instOuter`) and the instantiated codomain of a valid inductive application.
- Executable guards (all redundant on well-typed input, see divergences.md): `reduceProjCore`
  checks the constructor and arity, `inferProj` checks the field index, `isDefEqUnitLike` the
  parameter count, `tryEtaStructCore` a never-zero structure sort.
- `isDefEqUnitLike.WF`, `tryEtaStructCore.WF`, `reduceProjCore.WF` are proved modulo the
  registry placeholder `VContext.registryShape` (Verify/TypeChecker/Basic.lean).
- Recursor reduction (`reduceRecursor.WF`, Verify/TypeChecker/WHNF.lean) is proved in full
  modulo three environment placeholders in Verify/TypeChecker/Recursor.lean:
  `VContext.recursorRules` (every visible recursor's rules are stored equations of the shape
  `VIotaRuleShape`, its type has the shape `VRecursorShape`, each rule's constructor has the
  shape `VConstructorShape`, the major inductive is rigid, and K-like recursors eliminate from
  a proposition whose parameters type the unique constructor: `RecursorRulesCoherent`,
  Verify/Environment/Recursors.lean), `VContext.quotCoherent` (the quotient constants and the
  `Quot.lift` equation are present and `Quot` is rigid), and `VContext.inductRigid`.
  - Theory/Typing/RecursorLemmas.lean derives iota reduction from the syntactic shape of a
    stored rule alone (`VIotaRuleShape.iota`, `iota_body`): the actual arguments are typed at
    the rule's binders because the pattern variables of the left-hand side are typed at the
    recursor and constructor telescopes (`args_typing`), using unique typing, strengthening
    (`weakN_iff`) and rigid-application injectivity. Both inductive recursors and `Quot.lift`
    are instances (the constructor parameter count `cnparams` is decoupled from the recursor's);
    `Quot.ind` reduces by proof irrelevance (`QuotCoherent.ind_defeq`).
  - K-like conversion (`toCtorWhenK.WF`) is proof irrelevance; structure conversion
    (`toCtorWhenStruct.WF`) is `structEta` with the projections typed by induction along the
    constructor telescope; literals go through `TrExprS.lit`.
  - Executable changes (divergences.md): exact constructor arity in `inductiveReduceRec`, an
    arity guard and loop-free metavariable check in `toCtorWhenK`, `return e` instead of
    `unreachable!` and an arity guard in `expandEtaStruct`/`toCtorWhenStruct`; the pure tail of
    `inductiveReduceRec` and the continuation of `quotReduceRec` are separate definitions.

## Remaining work

- Discharge `VContext.registryShape` from `ProjectionRegistryCoherent` /
  `Ordered.projectionShape` once the registry is a `CheckingEnv` field. That refactor
  (`CheckingEnv.Valid` gains `constructorOwners` and `projectionRegistry`; `c.lparams.Nodup`
  threaded through the constructor phases; early registration) is on branch
  `agent/verify-inductives-P` (worktree `/home/kim/worktrees/lean4lean/l4l-agent-P`, last commit
  `7b098c5`), not merged. Its build still fails at: `Nested/OrderInsensitiveAlignment.lean`
  (`AddConstants.validOfFreshPermutation` needs a registry-aware form of `AddConstants.valid`
  for batches containing constructors), `PrimitiveAtomicInstallation.lean`
  (`StagedContextWF.complete` must supply the two new fields for a partial primitive batch),
  `Run/SemanticFormation.lean` (`declareConstructors.WF` now takes a
  `CheckedConstructorsResult`), and `Nested/ConstructorParameterValidationSoundness.lean`
  (`CheckingEnv.Valid.add` now takes a `ProjectionRegistryStep` for each restored header and
  constructor).
- Discharge `VContext.recursorRules`: carry `RecursorRulesCoherent` in `CheckingEnv.Valid` and
  `VContext` like `projectionRegistry`, and produce it at the inductive installation boundary
  from the recursor certificates (`BoundGeneratedRecursorRule.EquationTranslation` gives the
  wrapped shape and `rhs_residual`; the left-hand side pattern with parameter, motive, minor and
  field variables follows from `sourceLhsBody` and `abstractedParamsUnique`-style lemmas; the
  recursor and constructor type shapes from `RecursorShape` and the constructor certificates).
  The nested path must cover the auxiliary recursors' rules too. `VContext.quotCoherent` is the
  `quot` step of the trace (`TrEnv'.quot`, `AddQuot`); `Rigid` for inductive types and `Quot`
  needs the trace to record that no stored rule is headed by them.
- `inferProj.WF` (Verify/TypeChecker/InferType.lean) is the last checker sorry (in progress in a
  separate worktree at the end of the session).
- Optional cleanup: several executable arity guards (divergences.md) exist only so that the
  verification never needs "an inductive type application is not a function type"; since
  `IsDefEqU.sort_forallE_inv` is already an accepted conjecture of the development, those guards
  could be removed and the arities derived from well-typedness instead.
- Church–Rosser: add the new rules to `ParRed`/`NormalEq` and close the new
  cases; this needs the same injectivity facts as the conjectures.
- Re-run the full build, search for `sorry`, and use `#print axioms` on every
  final exported inductive theorem before claiming completion.
