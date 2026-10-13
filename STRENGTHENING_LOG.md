# Explicit developments attempt

Branch: `agent/iota-strength-wild`. Objective and completion criteria: `GOAL.md`.

## 2026-10-13: baseline and chosen experiment

The worktree started clean at `a65a246c`. Fetched both earlier attempts. No changes to
the executable, `UniqueTyping.lean`, or downstream verification are planned for this
experiment. The existing `sorry` is still open.

Chosen first experiment: distinguish residuals of initially marked beta-redexes from
created redexes. A marked beta node binds its body, like an explicit let. Substitution
copies existing marks and does not mark an ordinary application whose function becomes
a lambda. A natural-number interpretation will count expansion of marked nodes,
including discarded arguments and annotations, so arbitrary marked development steps
strictly decrease even when ordinary syntactic size increases.

This is intended as an actual finite-development tool, not a claim that every join can
be made beta-normal. The subsequent task is to trace the bad domain comparisons through
the join and see whether newly created bad pairs have a decreasing source certificate.
No smaller sufficient obligation has yet been proved; no route is declared exhausted.

The all-target observation reflection refutation and the older certificate-rank
obstructions are retained as constraints (`IDEAS.md`). In particular a substitution
bound may depend on the substituend: the planned interpretation explicitly does so.

## Checked finite developments

`Lean4Lean/Theory/Typing/Strengthening/MarkedDevelopments.lean` now provides:

* Marked syntax, renaming and substitution, with erasure back to `VExpr` commuting
  with those operations. Only `.beta` is a mark; substituting a lambda into `.app`
  leaves the application unmarked.
* `Step.weight_lt` and `finite_developments`: all development orders terminate. The
  body is evaluated at the argument's weight, so duplication is accounted for;
  separate costs retain discarded arguments and domains.
* `exists_complete`, `Step.develop_eq`, and `complete_unique`: a mark-free endpoint
  exists, and the erasure of every such endpoint is the same computed development.
* `Step.parRed`, `Step.defeq`, `develop_defeq`, and `round_defeq`: the construction
  is connected to the actual calculus and preserves its original typing.

Validation: `lake build Lean4Lean.Theory.Typing.Strengthening.MarkedDevelopments`
passes. Axiom audits of `finite_developments`, `exists_complete`, `complete_unique`,
`Step.defeq`, `develop_defeq`, `round_defeq` contain only `propext`, `Quot.sound`,
and (where used) `Classical.choice`, with no `sorryAx`. Existing dependency build
warnings, including the original open theorem, remain unrelated to these proofs.

Next: test newly created matched-redex pairs, then formulate the comparison-marking
invariant. The finite-development theorem proves nothing about termination of new
marking rounds and is not yet a strengthening result.

## Created-redex regression

`DevelopmentRounds.lean` proves a stronger test than one isolated two-round example.
Let `T₀ = Prop`, `Tₖ₊₁ = Tₖ → Tₖ`, and `Iₖ = λ x : Tₖ. x`. Define
`chain 0 k = Iₖ`, `chain (n+1) k = chain n (k+1) Iₖ`.
Every chain has type `Tₖ₊₁` in every environment and context. A complete development
of all existing beta-redexes changes `chain (n+1) k` to `chain n k`. Thus, for every
fixed `r`, `r` marking rounds on `chain (r+1) 0` leave a beta-redex with a lambda
argument at type `Prop → Prop` (`no_uniform_round_bound`).

This is a restriction on the proposed strategy, not a counterexample to strengthening
or `StrictJoinRepair`: reflexive comparisons can bypass all these redexes, and the
terms normalize after an input-dependent number of rounds. The example uses upward
redex creation, allowed by superdevelopments. Downward creation and the provenance of
domain comparisons must be examined next; rejecting standardisation here would be wrong.

Build: `lake build Lean4Lean.Theory.Typing.Strengthening.DevelopmentRounds` passes.
Axiom audits of `chain_typed`, `round_chain_succ`, and `no_uniform_round_bound` contain
no `sorryAx` (only `propext`, and `Quot.sound` for the last theorem).

Additional literature: inspected the primary Bonelli–Barenbaum paper
https://arxiv.org/pdf/1001.4429, §1. The newer typed-confluence formalisation
https://github.com/thiagofelicissimo/typed-confluence was cloned read-only under
`/tmp/lean4lean-strength-literature/typed-confluence`; its `eq_erased` requires
`Nf`/`Ne`, so it does not supply the needed non-normal annotation coherence.

## Upward creation handled; next case is downward creation

`Superdevelopments.lean` defines a structural pass: first recursively develop both
children of an application, then beta-contract if the resulting function is a lambda,
without recursively processing the substituted result. Checked results:

* `superdevelop_betaRed` gives a finite `VExpr.BetaRed` derivation.
* `superdevelop_simAt` preserves every type in every well-formed context.
* `superdevelop_liftN` proves exact commutation with arbitrary binder insertion.
* `superdevelop_eq_iff` reflects as well as preserves equality for endpoints typed
  below at a common type; `superdevelop_front_failure` transports a hypothetical
  typed-front counterexample through the pass without any strengthening assumption.
* `superdevelop_chain` removes the entire identity spine in one pass, regardless of
  the number of ordinary marking rounds it needed.
* `downwardExample_typed` and `downwardExample_still_hasBeta` check the term
  `(λ f : T₂. f I₀) I₁ : T₁`: its pass yields `I₁ I₀`, still a beta-redex whose
  argument is a lambda. This is substitution into a function position (type III
  creation), rather than upward creation along the existing spine.

`lake build Lean4Lean.Theory.Typing.Strengthening.Superdevelopments` passes; this
build includes all three new modules. Axiom audits of all eight principal results
listed above contain no `sorryAx`, only the standard metatheoretic axioms as needed.
No executable or existing verification source was changed.

Continuation point: connect this pass to the *normal comparison* of a join. Track a
downward-created function lambda back to the substituted argument's lambda-domain
comparison. Its above-context domain equality is already an opaque premise of the
original `NormalEqN.lamDF`; it is not charged by that relation's current index. A
successful invariant must explain why those comparisons can be descended or give a
well-founded provenance order on them. Neither the present development weight nor
the structural recursion of `superdevelop` supplies that order. This is an open next
step, not a new irreducible obligation claimed smaller than `PropFront`.

The goal remains active: the required proof/canonical-Eq counterexample/strictly
smaller sufficient obligation has not been obtained. The first goal turn made
concrete progress (new checked theory and tested strategy limits), rather than waiting
or encountering an external blocker. The research ledger retains the unrefuted routes.

## Recursive domain comparisons: unconditional descent

`DomainNormal.lean` records a recursive normal comparison at every lambda domain,
charging both domain and body to its index. It currently excludes eta constructors,
but permits applications with lambda functions. `DescentSupport.lean` reuses route A's
lift/proofness helpers without importing its front predicates.

Checked: soundness into the existing eta-free `NormalEqF false`, index-preserving
context conversion and homogeneous substitution, and `DomainNormal.descend` along
arbitrary `Ctx.Lift'`. Descent has a common-type mode and an independent mode requiring
only that the left endpoint is not a proof. The latter now includes lambdas. Its
lambda case recursively descends the domain comparison; impredicativity ensures
that a non-proof lambda has a non-proof body. Application descent can therefore
handle a lambda function directly. This is the concrete benefit of charging the
lambda-domain comparison, not a claim that the full confluence join supplies one.

Build: `lake build Lean4Lean.Theory.Typing.Strengthening.DomainNormal` passes.
Axiom audits of descent, substitution, and soundness list only `propext`,
`Classical.choice`, and `Quot.sound`. No executable or original theorem changed.
The earlier study's domain-counted pilot remains relevant: opaque typing witnesses
can reintroduce uncounted alignment during composition/confluence. Next tests are
transitivity, heterogeneous substitution, and whether eta/full confluence can
produce recursive domain certificates. No completeness assumption is being made.
