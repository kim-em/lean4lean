# Handoff: inductive verification

## Goal

Make inductive verification genuinely complete and sound. The final ordinary,
primitive, and nested-inductive correctness theorems should be free of
`sorryAx`, and every checker step should refine the abstract calculus without
caller-supplied certificates or hypotheses that are never discharged.

## Current state

This branch replaces projection expansion certificates with primitive
projection syntax and stages installation as types, constructors, projections,
then recursors. It also removes much of the old compatibility and callback
machinery. The full build has passed, but this is not ready to claim that
inductives are complete: final theorem axiom audits still report `sorryAx`.

## Remaining work

- Check if there is new work on the remote default branch,
  and if so merge that into this branch and adapt/fix as needed.
- Give projection computation sound abstract semantics matching
  `reduceProjCore`; `projDF` types projections but does not justify reducing a
  projection of a constructor to its field.
- Express and discharge a local projection-readiness invariant during staged
  installation. Global `Projectable` is temporarily false.
- Finish dependent metatheory and checker proofs, especially projection
  injectivity, unique typing, Church–Rosser, `inferProj`, and `reduceProjCore`,
  then the remaining recursor, eta, and unit-like termination proofs.
- Re-run the full build, search for `sorry`, and use `#print axioms` on every
  final exported inductive theorem before claiming completion.

Treat the current direct-projection design as a hypothesis, not a constraint.
Be skeptical of every premise and certificate, verify that all are derived at
their call sites, and make a significant refactor or change of approach if it
would make computation and staging actually provable. In particular, do not
encode projection beta as arbitrary `VDefEq` rules unless pattern matching and
Church–Rosser are extended soundly: current patterns cannot match
projection-headed terms.
