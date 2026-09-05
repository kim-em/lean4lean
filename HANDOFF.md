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
bodies loaded via `ConstantInfo.value? (allowOpaque := true)`) shows exactly
nine declarations that introduce `sorry` into that closure:

Theory (the injectivity/strengthening conjectures; `Injectivity.lean`,
`UniqueTyping.lean`; also open on `master`):

- `VEnv.IsDefEqU.sort_inv`
- `VEnv.IsDefEqU.forallE_inv_stratified`
- `VEnv.IsDefEqU.weakN_iff` (strengthening for definitional equality)
- `VEnv.IsDefEq.uniq`, `proj` case (needs injectivity of applications of
  rigid inductive type constants, the same class of fact)

Checker (`Verify/TypeChecker/*`):

- `inferProj.WF` (projection type inference)
- `reduceProjCore.WF` (projection of a constructor application)
- `tryEtaStructCore.WF` (structure eta)
- `isDefEqUnitLike.WF` (unit-like types)
- `reduceRecursor.WF` (iota, K, struct-eta major conversion, literals, quot)

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

## Remaining work

- Extend `Aligned`/`CheckingEnv` with recursor-rule provenance so that
  `reduceRecursor.WF` can find the abstract iota equation for every executable
  `RecursorRule`; the equation translations already exist inside
  `Verify/Inductive` (`GeneratedIotaEquationTranslations`) but are not exported
  to the environment invariant.
- Church–Rosser: add the new rules to `ParRed`/`NormalEq` and close the new
  cases; this needs the same injectivity facts as the conjectures.
- Re-run the full build, search for `sorry`, and use `#print axioms` on every
  final exported inductive theorem before claiming completion.
