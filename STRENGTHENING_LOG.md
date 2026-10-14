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

`DomainNormalAlgebra.lean` extends this with index-preserving symmetry and weakening,
transitivity, and heterogeneous substitution (`instN_r`, `instN_lr`). These all build;
axiom audits of symmetry, transitivity, and both heterogeneous substitution theorems
are free of `sorryAx`. In particular, transitivity aligns the middle lambda's body
context using the already recorded domain equality; it does not invent a replacement
domain certificate from that opaque equality. Heterogeneous substitution composes
homogeneous substitution with structural congruence on the typed right endpoint.
The index can grow, as expected; this is preservation, not a termination measure.

## Reduction compatibility of recursive domain certificates

`DomainSuperdevelopment.lean` proves `DomainNormal.contractApp` and
`DomainNormal.superdevelop`. Related function/argument pairs remain related after
contracting matched beta-redexes, and after a complete superdevelopment pass. If a
function comparison is proof irrelevance, the application result is itself a proof;
otherwise the explicit lambda case uses heterogeneous substitution of the body
certificate. Reducing annotations changes binder contexts by the corresponding
checked definitional equality, while retaining the recursive domain certificate.

`DomainBetaSimulation.lean` goes beyond the chosen pass: `beta_simulation` matches
**any finite compatible beta reduction** of the left endpoint by a finite beta
reduction of the right endpoint, with a `DomainNormal` comparison of the results.
The induction includes reductions inside lambda and Pi annotations, beta contraction,
and arbitrary finite composition. It assumes a typing for the original left endpoint
and context well-formedness; no strengthening or canonical-Eq assumption is used.

Both modules build. Axiom audits of contraction, superdevelopment preservation, and
beta simulation contain only `propext`, `Classical.choice`, and `Quot.sound`.
This establishes stability through downward redex creation, rather than giving a
well-founded bound on repeated repair of the original opaque comparisons.

The earlier `alignment_can_be_hidden` example still applies to proof leaves: their
common type can hide an arbitrary conversion. The present descent theorem does not
claim independent descent for proofs, and its application case first descends the
non-proof function and obtains convertible argument types below. Thus that example
is not a counterexample to the checked invariant. The remaining completeness issue
is producing these certificates from the original unrestricted normal comparisons,
especially opaque lambda-domain conversions and eta. No smaller sufficient obligation
or full proof has yet been obtained.

## Concrete boundary: eta hidden in an eta-free comparison

`DomainCertificateBoundary.lean` refutes the naive completeness bridge from
`NormalEqF false` to a beta join modulo `DomainNormal`. In the well-formed context
`f : Prop → Prop, P : (Prop → Prop) → Prop`, set

* `D = P f`, `E = P (λ x : Prop. f x)`;
* `l = λ h : D. Prop`, `r = λ h : E. Prop`.

`DomainBoundary.normal` checks `NormalEqF false l r`: the old lambda constructor
accepts the declarative equality `D ≡ E`, which uses eta internally. Both endpoints
are beta-normal and are not proofs. `no_certificate` proves there is no
`DomainNormal l r`: a structural domain comparison would require a comparison of
`f` with its eta expansion, which the eta-free recursive relation cannot supply.
`no_beta_certificate_join` then proves that no finite beta reductions of either
endpoint can repair it. The general lemma `beta_eq_of_not_hasBeta` checks that such
reductions are identities. Axiom audits of all three principal results are clean.

This is a specific refutation of **beta-only global certificate repair**, even for
an eta-free input normal comparison. It is not a counterexample to strengthening,
to route A's strict comparison repair, or to a strategy that handles eta. In this
example the strict relation can simply compare the two outer lambdas at a common
type; it does not require certifying their domains recursively. Thus requiring a
`DomainNormal` certificate everywhere is stronger than the intended selective repair.

Continuation: retain the proved certificate algebra/beta simulation for matched
function lambdas, but investigate a hybrid with the existing strict relation (which
already handles eta at common types), or certificates tied to the original equality
derivation. Do not assume that removing explicit eta constructors removes eta from
opaque typing/domain premises. The objective is still open and all other unrefuted
ledger routes remain live.

## Selective certificates with eta-aware descent

`HybridNormal.lean` adapts route A's checked strict relation and descent proof. At an
application, the functions must either both be non-lambdas, or additionally carry a
`DomainNormal` comparison. The ordinary recursive hybrid comparison remains present;
its index continues to support the original eta/spine induction. All other rules,
including opaque lambda domains and eta, retain route A's behavior.

`HybridNormal.descend` is checked along arbitrary context lifts, in the original
common-type and non-lambda/non-proof modes. The new application branch invokes the
stronger `DomainNormal.descend` for its function certificate, then aligns argument
types below and uses the hybrid common-type induction for the arguments. Thus
lambda functions with certified domains are admitted without eliminating all beta
redexes or requiring global recursive certification.

`DomainNormal.toHybrid` embeds all of the recursive comparisons. The local theorem
`HybridNormal.descend_join` checks that full reductions performed below, followed by
a selective comparison of their lifts, suffice to descend the original equation.
It explicitly leaves construction of those joins open and makes no claim that this
condition is irreducible or strictly smaller than the typed front.

`DomainBoundary.hybrid` directly handles the previous counterexample at index one,
confirming that global certificate failure is not an obstruction to this selective
relation. The boundary module and all its dependencies build; axiom audits of the
hybrid descent, join descent, embedding, and boundary example have no `sorryAx`.

Next substantive test: substitution and confluence for the hybrid relation. A
non-lambda function can become a lambda after substitution. Homogeneous substitution
may be recoverable by variable-spine rigidity; heterogeneous substitution of hybrid
arguments can expose uncertified lambda functions and will require selective beta
repair. The checked `DomainNormal.instN_lr` and beta simulation cover substitutions
whose arguments already carry domain certificates, not arbitrary hybrid arguments.
Do not silently use the stronger closure statement. The full objective remains active.

## 2026-10-13 continuation: substitution of the selective relation

The previous goal turn made authoritative progress (five pushed commits and checked
positive/negative results); it was not a wait or an external blocker. Revalidated a
clean worktree at `46099237` before continuing.

`HybridAlgebra.lean` proves symmetry and weakening with unchanged indices, plus
`variable_inv_lift`: a non-proof variable compared with a non-lambda is syntactically
identical to it, even after arbitrary context extension. Eta-both comparisons are
peeled with the existing spine lemma until the comparison index decreases.

`HybridSubstitution.lean` proves `HybridNormal.instN_lr` for arguments related by
`DomainNormal`, and homogeneous substitution as a corollary using a reflexive argument
certificate. In an application, substitution can expose a function lambda only at a
variable. Variable rigidity then identifies the two original function terms, and
`DomainNormal.instN_r` supplies a certificate for their instances. Proof functions
produce proof applications, handled by proof irrelevance. Existing function certificates
are transported by the already checked heterogeneous domain substitution theorem.
Eta and context-conversion cases are included.

Build: `lake build Lean4Lean.Theory.Typing.Strengthening.HybridSubstitution` passes.
Axiom audits of variable rigidity, symmetry, weakening, and both substitution results
contain only `propext`, `Classical.choice`, and `Quot.sound`. This does not establish
substitution with arbitrary hybrid arguments: the recursive argument certificate is
an explicit hypothesis. Next, test whether that restriction is essential or can be
removed by direct comparison; if direct closure fails, reduction repair is required.

## Certificate reflection and the actual substitution boundary

Strengthened the existing descent proof to `DomainNormal.reflect`: given typings
below, it reconstructs a recursive comparison below, in common-type mode or for a
non-proof endpoint. `DomainNormal.descend` is now the immediate declarative corollary.
This replaces its former proof rather than maintaining two copies of the induction.
No arbitrary typing-strengthening claim is involved. Rebuilt all affected domain,
hybrid, substitution, beta-simulation, and boundary modules successfully; both
reflection and declarative descent have clean axiom audits.

The boundary example now extends its context by `h : D`. Substituting the related
functions `l = λ h : D. Prop` and `r = λ h : E. Prop` into the reflexive source body
`g h` yields `l h` and `r h`. `unrestricted_substitution_fails` proves that these
instances have **no hybrid comparison**, despite the hybrid comparison of the
arguments and the reflexive comparison of the source. Their result type is `Sort 1`,
which rules out proof irrelevance and eta-both at the application root. Application
congruence would require a recursive certificate for the two lambdas; reflection
would give the already refuted certificate in the original context.

`application_repaired` verifies that one beta contraction on each side yields the
same `Prop`, with a reflexive hybrid comparison. Thus direct heterogeneous closure
for arbitrary hybrid arguments is refuted; closure **up to finite reduction** is
still live and is the next necessary test. This is not a counterexample to
strengthening. Both boundary theorems have clean axiom audits.

## Typed loops refute arbitrary finite beta-only selective repair

A stronger test than the finite identity spines is now checked.
`RecursiveDomainEnvironment.lean` installs the recursive family
`R : (Prop → Prop) → Sort 1` with value `λ f. (R f → Prop)` using
`VDecl.WF.mutualDef`. The value is checked in the temporary constant environment,
**before** its defining equation is installed. `extended_wf` proves that any
well-formed base extends at a fresh name, and `extended_canonicalEq` preserves the
canonical Eq hypothesis. This is an actual declaration construction, not an assumed
recursive type equation.

In `RecursiveDomainLoop.lean`, take `f : Prop → Prop`, set `D = R f`,
`E = R (λ x : Prop. f x)`, `δ_D = λ x : D. x x`, and `Ω_D = δ_D δ_D` (likewise E).
The installed equation types `Ω_D : Prop`; the same-body lambda comparison and domain
eta equality type `Ω_E : Prop` and give `NormalEqF false Ω_D Ω_E`.
Both terms are non-proof propositions. A hybrid application comparison would require
a domain certificate for the diagonals, hence a recursive comparison of `f` and its
eta expansion, which is impossible. Eta-both at the root is excluded because the
loop's type is a sort.

`omega_beta_eq` proves that **every finite compatible beta reduction** of either
loop returns exactly itself: its annotations and lambda bodies are beta-normal, and
the root contraction reproduces the same self-application. `no_beta_hybrid_join`
therefore rules out every finite beta-only repair, not just a fixed number of rounds.
`canonical_beta_only_failure` instantiates this result with the constructed extension
of an arbitrary canonical-Eq environment at a fresh name, including both endpoint
typings and the old normal comparison. This is a counterexample to a proposed repair
strategy, **not** to strengthening.

The repair is also checked. `LambdaReannotation.lean` proves that a typing
`λ x : D. b : Π x : A. B` yields a full reduction to `λ x : A. b`: expand eta at
that chosen function type and beta-contract under the new binder.
`RecursiveDomain.full_repair` uses this to reannotate the right diagonal to the left
one, and hence reduce `Ω_E` to `Ω_D`, without normalizing the loop. This validates the
need to consider eta-aware repair rather than treating the beta-only obstruction as
a reason to reject the whole developments/confluence route.

Build: `lake build Lean4Lean.Theory.Typing.Strengthening.RecursiveDomainLoop` passes.
Axiom audits of the declaration, environment WF, Eq preservation, canonical beta-only
failure, full repair, and generic lambda reannotation are free of `sorryAx`.
The executable and the original open theorem remain unchanged.

Next: generalize the reannotation repair where a common function typing is available,
and track how such typings are supplied at matched lambda arguments. The original
frontier still lacks a common function type *below* when only the enclosing
application has a common type. Reannotation does not manufacture that missing type
alignment; its explicit typing premise must not be hidden in a claimed solution.

## 2026-10-13 continuation: ambient full joins are domain-certified

Revalidated the clean branch at `12642acd`. The previous turn was progress: it
changed the checked theory and refuted arbitrary finite beta-only repair while
proving a full eta-aware repair of that same loop example.

`DomainJoin.lean` proves `normal_domain_join` by induction on the existing normal
comparison. Applications and projections combine the inductive reductions. A lambda
pair is reannotated at its common domain witness, then its body comparison is repaired.
Pi domains are repaired recursively and body contexts are converted using the checked
domain reductions. Eta-left, eta-right and eta-both become explicit eta expansions
followed by repaired body comparisons. Proof-irrelevance leaves remain leaves.
This construction is finite even for non-normalizing endpoints.

Composing this repair with `WF.church_rosser` gives `domain_join_complete`: **every
declarative equality in a canonical-Eq environment has a finite full-reduction join
modulo `DomainNormal` in its ambient context**. Its axiom audit, and that of
`normal_domain_join`, contain no `sorryAx`. The module builds successfully.

This is not strengthening. The construction may choose common lambda-domain witnesses
or eta-both domains that mention the extra binder. Even if the final syntax is a lift,
the theorem supplies only ambient-context typings and reductions. `DomainNormal.reflect`
requires endpoint typings below; `HybridNormal.descend_join` requires reductions below.
Neither condition follows from this new completeness theorem. The unresolved step is
now explicitly the choice/lowering of the repaired reductions and their typings, not
existence of finite domain-certified joins in the larger context. No claim of a
strictly smaller irreducible obligation is made.

## Scope-preserving eta-free reannotation

`EtaScope.lean` separates two issues. A full eta step can introduce an unused
variable into its chosen domain annotation: eta-expand the lifted identity at a
domain `(λ (_ : Q↑). Prop) #0`, convertible to Prop but containing the new binder.
`scope_failure_and_cleanup` includes the extension's well-formedness, the full step,
its target's failure to skip the new binder, and a finite beta cleanup. This refutes
scope preservation for arbitrary full reducts, not strengthening or scope repair.
Conversely, `eta_lift_descend` proves an eta step descends when its target is a lift
and both endpoints have a common typing below. Target typing remains explicit.

`LeftReannotation.lean` improves eta-free normal repair. It holds the left endpoint
fixed and reannotates each right lambda with its displayed left partner's domain.
Its syntactic relation `Reannotates` commutes backwards through arbitrary lifts,
including binders. Thus `normal0_lift_reannotation` produces a lifted final endpoint
and a `DomainNormal` certificate at exactly the original normal-comparison index.
This removes the arbitrary common annotation witness from eta-free repair.

Both the right-hand reduction and the certificate still live in the larger context.
The theorem does not establish typing of the repaired endpoint below or reduction
of the original right endpoint below. At a reannotated lambda, the right body was
typed under its original domain; moving it to the left domain needs precisely a
justified domain conversion. In applications, a common whole-term type does not
supply that function-domain conversion. No smaller sufficient obligation is claimed.

Both new modules build. Axiom audits of their principal results, including the
syntactic lift inversion, contain only `propext`, `Classical.choice`, and `Quot.sound`
(or a subset); no `sorryAx`. The executable and the open theorem are unchanged.

## Reannotation reflection already contains the entire proposition front

`ReannotationBarrier.lean` now checks the cost of a tempting follow-up lemma.
For `domainProbe A = λ (_ : A). Prop`, `domainProbe_reduction_iff` proves that a full
reduction from the A-probe to the B-probe is equivalent to declarative conversion
of A and B. The reverse implication is typed eta reannotation; the forward
implication uses subject reduction, uniqueness, and Pi-domain injectivity.
Both probe endpoints are independently typable whenever their domains are types.

Consequently `probeReflection_iff_propositionFront` proves an exact equivalence,
at fixed Params, between proposition strengthening and reflecting full reductions
of these probes from a one-binder extension. It needs no canonical-Eq hypothesis.
The lowered final syntax and a reflexive `DomainNormal` certificate below are
already supplied by `domainProbe_repair_certificate`. Thus those two conditions,
even together with independent endpoint typings below, cannot make unrestricted
reannotation-reduction reflection a strictly smaller obligation.

The module builds; all three results are audited without `sorryAx`. This is a
barrier to an overstrong local lemma, not a counterexample to strengthening.
A derivation-sensitive repair remains live. Recovering Pi shape below may help
choose eta annotations but does not itself align the domains of matched lambdas.

## Annotated proof erasure: a different reduction representation

The old `ProofAware.untyped_erasure_reflection_false` was reread at the pinned tag.
It refutes independent reflection for *heterogeneous proofs*, and assigning one
ordinary `VExpr` token every proof type. It does not refute reflection at a common
type, or independent reflection when the left endpoint is a non-proof.

`ProofErasure.lean` implements a separate `ProofShape` syntax with one proof marker
and all ordinary constructors, retaining every non-proof lambda annotation.
`proofErase_reflect` proves that equal erasures give a `DomainNormal` certificate in
exactly those two modes. The proof uses function equality to align application
argument types, and domain equality to align binder contexts. It does not compare
heterogeneous top-level proof tokens. `proofErase_defeqCtx` handles context conversion.

`ProofErasureSubstitution.lean` proves commutation with arbitrary typed
single-variable substitution, including under binders and for proof arguments;
proofness is unchanged by such substitutions. Erasure also commutes with arbitrary
binder insertion, whose action on erased syntax is injective. Hence equality of
erased lifted terms reflects below when the original endpoints are typed there.
These are structural equalities of erasures, not arbitrary erased convertibility.

Both modules build with their principal theorems axiom-clean. The next step is
replaying reductions of erased syntax on typed originals. Beta is the first case;
eta, declaration computation, singleton extraction, and quotient guards still need
sound and complete treatment. This route does not yet supply any global front or
strictly smaller sufficient obligation.

## Erased beta paths replay and descend

`ProofErasureBeta.lean` defines compatible finite beta reduction on `ProofShape`.
`proofErase_beta_replay` reconstructs an original beta path for every erased path
from a typed source. Lambda and Pi cases convert the body's erasure context after
the annotation reduction; beta uses the checked erasure/substitution theorem.
No intermediate erased typing is assumed. Original subject reduction supplies all
reconstructed endpoint typings in the starting context.

`proofErase_beta_join_reflect` then reflects erased beta joins at a common type.
`betaRed_lift_inv` syntactically lowers any original beta path from a lifted source,
and `proofErase_beta_join_descend` combines this with replay and typed erasure
reflection to descend an erased beta join from an extension. The new module builds
and all four results are axiom-clean. This is still a beta-join theorem, not full
conversion completeness; the existing beta-only repair obstructions remain valid.

The next test concerns eta: erasure can hide occurrences of the eta binder inside
proof payloads. An erased eta contraction may therefore create a proof marker for
which no original proof is supplied below. Exact target replay needs a separate
argument; beta replay cannot simply be reused for eta.

## Eta can expose an unfilled proof marker

`ProofErasureEta.lean` checks the proposed eta extension against
`F : Q → Q → Prop`, with Q a proposition. The typed source `λ h : Q. F h h`
erases to `λ erase(Q). (F ⋆)↑ ⋆`. The first occurrence of h has vanished inside
the erased function, so this is an apparent eta redex in the proof-erased syntax.

`target_representative_iff` proves that the proposed short form `F ⋆` has **any**
typed original representative in the starting context exactly when Q has an
inhabitant there. Inverting erasure forces every representative to be `F q`;
typing inversion and uniqueness force `q : Q`. Conversely any such q supplies a
representative. `source_eq_of_inhabitant` proves the original source equal to
`F q` by proof irrelevance under the binder followed by ordinary typed eta.

`target_not_replayable` makes the uninhabited case explicit, with uninhabitedness
as a premise. This does not instantiate a consistent canonical-Eq environment,
refute typed erased-conversion reflection at existing endpoint typings, or refute
strengthening. It prevents treating exact beta replay as an automatic eta replay
lemma. A typed repair can retain or restore eta binders instead of demanding an
original for each short erased intermediate. That remains a live direction.

The module builds without new warnings. All principal results, including the
inhabitation equivalence and its positive repair, are axiom-clean. The executable
and `UniqueTyping.lean` remain unchanged. No goal deliverable is claimed yet.

## 2026-10-13 continuation: recursive eta-aware domains with explicit modes

Revalidated clean HEAD `2ba33c6b`. The previous turn was progress: it committed
structural proof-erasure reflection, typed substitution/weakening, beta replay and
descent, and an exact conditional eta-replay obstruction. No external blocker.

`BidirectionalNormal.lean` introduces `BiNormal mode n`. Common-type mode permits
eta and the ordinary opaque-domain lambda rule. Independent mode has a lambda
rule whose domains are recursively compared in common-type mode and whose bodies
are compared independently. Applications always compare functions independently
and arguments at a common type. An independent comparison can be promoted to
common-type mode. Ordinary normal soundness, index-preserving context conversion,
and embedding of `DomainNormal` are checked.

`BidirectionalDescent.lean` proves the intended descent theorem for arbitrary
context lifts. Common-type mode requires convertible endpoint types below;
independent mode only requires that the independently typed left endpoint is not
a proof. The latter includes lambdas. Sort-level alignment for a domain comparison
is reflected from the ambient equation by universe injectivity, then the recursive
common-type domain certificate descends. A nonempty variable-spine lemma peels
eta-both to an independent comparison without choosing its domain below.

`BidirectionalLoop.lean` proves a direct independent-mode certificate, index 10,
for the recursive-family self-application loops that defeated every beta-only
hybrid join. Their domain comparison now admits the eta-related family argument
at its common function type. This tests actual added coverage; no reduction of the
loops or assumption of normalization is used.

All three modules build without new warnings, and their principal results are
axiom-clean. This is not full strengthening or a smaller sufficient obligation.
Transitivity and heterogeneous substitution need care: the ordinary normal
transitivity proof applies a common-mode comparison in function position under an
eta binder, where this calculus requires independent mode. Typed application up
to reduction, rather than an invalid mode coercion, is the next local repair to
investigate. Global completeness and lowering of full repair paths remain open.

## Common-mode application and the beta-simulation boundary

`BidirectionalApplication.lean` proves mode- and index-preserving homogeneous
substitution. `BiNormal.apply_same_arg` applies a common-mode function comparison
to one typed argument, obtaining a beta join of common-mode certificates. The
lambda cases contract the displayed redexes; eta cases instantiate the compared
bodies. `BiBetaJoin.descend` lowers such joins using syntactic beta-path inversion
and subject reduction below. This does not assume heterogeneous substitution or
transitivity of beta joins.

`BidirectionalBetaBoundary.lean` checks the next closure question. In context
`f : Prop → Prop`, independently compare `(λ x. x) f` with `(λ x. x) (λ y. f y)`.
The left root beta step exposes `f`. The right side has exactly two beta reducts,
its source and its eta-expanded argument; neither has an independent comparison
with the non-proof variable. `beta_simulation_failure` proves this even with
common endpoint typings. `full_repair` supplies the explicit eta/beta join. The
example is uniform in Params and needs no recursive declarations. It refutes
independent beta simulation, not common-mode beta-join completeness or full repair.

Both modules build, and substitution, application, beta-join descent, the failure,
and its full repair have only the standard propext/Classical.choice/Quot.sound
axioms. The strengthening goal remains open. Full repair must handle exposure of
common-mode eta comparisons in independent positions; copying the eta-free beta
simulation proof cannot establish the needed closure.

## Guarded eta loops refute beta-only bidirectional completeness

The independent-simulation failure did not by itself refute common-mode beta
joins. A stronger checked example now does, including at proposition endpoints.

`GuardedEtaEnvironment.lean` installs `D := D → (Prop → Prop)` by the existing
mutual-definition rule. Its value is typed in the temporary constant environment
without its own equation. The extension is well formed and preserves canonical Eq.
Let `d = λ x : D. x x` and `dη = λ x : D. λ y : Prop. (x x) y`. Both diagonals
have type D, and `d d` and `dη dη` have an ordinary normal comparison at
`Prop → Prop`.

`GuardedEtaSyntax.lean` defines a beta-stable grammar: every D-domain lambda has
an extra Prop-domain lambda at the start of its body. It contains `dη dη` and all
its finite beta reducts. Meanwhile `d d` has only itself as a beta reduct.
`GuardedEtaComparison.lean` rules out independent comparison of any application
spine headed by d with guarded syntax. Its lambda case either tries to equate D
with Prop (contradicting the recursive Pi equation and head separation), or must
compare an application body with a lambda in independent mode. Common-mode eta
only extends the spine, eventually requiring the impossible independent function
comparison. This is a finite induction on certificates, with no normalization
assumption or restriction on the number of beta contractions.

`GuardedEtaLoop.no_beta_join` therefore excludes joins in both modes, and
`canonical_beta_only_failure` realizes the common-mode failure in the actual
canonical-Eq extension. `GuardedEtaPropositions.canonical_proposition_failure`
applies both loops to a proposition variable in context `[Prop]`. The resulting
terms are typed propositions with an ordinary normal comparison and still admit
no common-mode beta-only join. Thus the failure occurs at the PropFront sort,
not merely at unrelated function endpoints.

`full_repair` and `propositions_full_repair` explicitly expand each diagonal body
by typed eta, then use congruence. The terms are already equal below; this is not
a strengthening counterexample. It rejects beta-only completeness of BiNormal,
while leaving its proved descent and full scope-controlled repair live. Adding
recursive eta-aware domain comparisons solved the old domain-loop test but does
not remove the need to repair eta in independently compared lambda bodies.

All five new modules build without new warnings. The grammar invariant,
environment extension, comparison exclusions, canonical instances, and positive
full repair are axiom-clean. No executable or UniqueTyping change was made.
The next unresolved issue is full repair with annotations and typings available
below, not another beta development bound or beta-only simulation lemma.

## Full computation preserves scope; eta annotations are the remaining syntax checks

Revalidated clean HEAD `d007ceb6`. The previous turn was progress: the application
lemma and the guarded recursive counterexample were committed and pushed. This
turn investigates full repair, since beta-only completeness is now refuted.

`GeneratedScope.lean` inverts arbitrary `liftN` insertions in both singleton and
quotient prefix generators. Raw substitution of a syntactic dummy removes each
inserted binder from the supplied arguments; regenerating and renaming back gives
the original program by determinism. No typing is asserted for the dummy. The
checked unfolding's template scope then proves that its generated RHS is a lift.
This is syntactic scope preservation, not descent of its `UnfoldingCheck`: source,
capture, major-constructor, and spine-alignment typing checks remain ambient.

`FullScope.lean` proves scope preservation for core parallel reduction without
assuming a smaller-context source typing or reflection of its guards. It defines
`ScopedFullStep`/`ScopedFullReduction`, retaining every full-reduction rule and
adding scope checks only on a function-eta domain and structure-eta parameters.
Such paths preserve scope throughout and return a lowered target syntax for any
lifted source. Conversely every actual full path below weakens to a scoped full
path above (`FullReduction.weakN_scoped`). The generator checks and all existing
typing premises are retained; no executable rule changes.

`ScopedReannotation.lean` tests whether this stronger path invariant removes the
known reannotation barrier. It does not: `lambda_reannotation_scoped` checks the
eta/beta repair whenever its target annotation is scoped, and
`scopedProbeReflection_iff_propositionFront` proves that reflecting even these
fully scoped probe paths remains exactly PropositionFront. All their intermediate
terms can omit the removed binder, yet the function typing needed for reannotation
below is still the missing information. This strengthens the earlier endpoint-only
barrier and prevents treating scope preservation as a sufficient new obligation.

All three modules build without new warnings; generator inversion, core/full scope,
scoped weakening, target lowering, and the equivalence audit are axiom-clean.
The goal is not complete. Scope is now isolated from typing: a full repair route
must construct/recover the needed typings below, rather than merely keep generated
annotations free of the extra variable. The declaration replay checks also require
separate justification; their descent is not inferred from syntactic generation.

## Finite observations recover Pi exposure through beta and function eta

Revalidated clean HEAD `6d030ae2`; the previous turn was progress. Scope preservation
alone was shown insufficient, so this turn addresses a missing typing ingredient:
recovering a function-type shape below without replaying the ambient eta annotations.

`PureObservation.lean` introduces a small class-free finite-demand interpretation.
Its observations are Pi heads, sort heads, and function demands on finite lists of
argument observations. Lambda annotations are ignored. This is a head-exposure
model, not an equality model: annotation erasure is not claimed to reflect conversion.
Operational realization uses actual finite beta paths for Pi/sort heads. The
fundamental lemma proves that each observation realizes its operational meaning
under any realizing substitution, giving beta head exposure at the empty valuation.

`PureObservationEta.lean` proves subsumption, valuation monotonicity, renaming in
both directions, and backwards soundness of arbitrary function-eta expansion.
`PureObservationSubstitution.lean` proves substitution inversion and finite support.
Compacting the demand on one substituted variable gives a finite lambda demand,
which proves backwards beta soundness. No normalization hypothesis, type classes,
or typed short eta representative is required.

`PureHeadExposure.lean` combines these into a compatible beta/function-eta relation.
`BetaEta.pi_exposure` and `sort_exposure` show that any finite mixed path ending at
a Pi/sort has an actual beta-only path from its source to that kind of head. The
exposed domain/body may differ from the mixed path's final annotations. Syntactic
beta-path inversion then proves `pi_exposure_below` for arbitrary lifts.
`function_type_below` uses beta subject reduction to reconstruct a function typing
in the smaller context from such a trace on its lifted type; `function_eta_below`
performs a genuine typed eta expansion below at the recovered domain. This is a
new constructive bridge for the beta/function-eta fragment, not full Pi exposure
from arbitrary ambient declarative equality.

`PureHeadExamples.lean` includes the guarded recursive loop's finite eta trace,
checks that it does not falsely acquire a Pi head, and demonstrates a mixed path
with a captured eta annotation whose original source still has beta-only Pi
exposure. `lambda_head_boundary` rules out extending the theorem to lambda heads:
eta expands a variable to a lambda although the variable has no lambda beta reduct.
The captured-annotation test is syntactic; no typing of its arbitrary annotation
is claimed.

All five modules build without new warnings. Realization, eta soundness, finite
support/substitution inversion, head exposure, reconstruction below, and the
boundary examples are axiom-clean. The strengthening goal remains open. Next:
extend this operational model to actual closed declaration unfolding, then address
pattern/projection computation and structure eta. The model currently has no
constant or projection observations, and an arbitrary ambient equality does not
yet supply the required beta/eta head trace.

### Closed declaration equations in finite head observations

Generalized the existing finite-demand model over a `Definitions` relation with
closed right-hand sides. This is a parameterization of the same checked proofs,
not a duplicated model. Constant observations contain a finite observation of the
body at the empty valuation. There is no termination or acyclicity assumption;
recursive and nondeterministic equations are allowed. The previous beta-only
results are retained by specializing to `Definitions.empty`.

`DeclarationHeadExposure.lean` proves valuation independence for closed bodies,
backwards observation closure under beta/delta, and `Compute.lift_inv` for any
lift. `ComputeEta.pi_exposure` and `sort_exposure` remove function eta from finite
head-exposing paths. `pi_exposure_below` extracts a computational Pi path below an
arbitrary lift, without requiring the intervening eta annotations to be scoped.
This is still a syntactic head-exposure result, not equality reflection or a
sufficient obligation for strengthening. Actual environment instantiation and
typed replay are next; pattern/projection computation and structure eta remain.

The generalized model, all previous pure examples, and the new exposure module
build. Axiom checks of realization, substitution inversion, finite support, eta,
lift inversion, and both exposure results contain no `sorryAx`.

### Typed replay of closed declaration head exposure

`DeclarationHeadTyping.lean` instantiates the model from actual stored equations
whose instantiated left side is a constant. `Definitions.ofEnv_sound` uses the
existing `extra` rule. `Compute.simAt` replays beta/delta computation at every
source type using subject reduction and uniqueness; there is no strengthening
premise. `ComputeEta.function_type_below` reconstructs a Pi typing below, and
`function_eta_below` supplies the resulting genuine full eta expansion there.

`DeclarationHeadExamples.lean` checks this against the admitted recursive equation
D := D → (Prop → Prop). `canonical_recursive_head` packages the well-formed
canonical-Eq extension, a computational Pi exposure, the absence of every beta Pi
exposure, and reconstruction for functions typed at D. `captured_alias_exposure`
checks a mixed eta/beta/delta trace with an unscoped intermediate annotation. No
typing of that arbitrary intermediate annotation is asserted.

Both modules compile, and principal definitions/replay/reconstruction/example
results are axiom-clean. The original strengthening sorry remains open. Full
conversion still includes proof irrelevance, pattern/projection computation, and
structure eta; none of those is covered by this fragment theorem.

### Boundary: proof irrelevance and untyped higher-order demands

`ObservationProofBoundary.lean` checks a concrete obstruction to a direct
extension of preservation to *all* definitional equalities. In the well-formed
context Q : Prop, h : Q, the equal proofs λ x : Q. x and λ x : Q. h differ at the
finite demand `app [pi] pi`: the identity has it and the constant proof has no
observation at the empty valuation. `no_defeq_observation_preservation` holds for
every environment and every definition collection, hence also under canonical Eq.

The obstruction is precisely to arbitrary untyped function demands. Conversely,
`Obs.proof_no_pi` and `proof_no_sort` use the new typed computational replay to
exclude base-head observations of actual proofs for any sound declaration
collection. Neither result is a strengthening counterexample. This also does not
refute the current full-reduction head-exposure route: `FullStep`/`ParRed` have no
proof-irrelevance reduction constructor. The confluence route can potentially
use full computational paths and only head-shape inversion of the final normal
comparison, rather than preserving every observation through declarative equality.
Typed demands or restricted preservation remain alternative refinements.

The boundary, both base-head exclusions, and their axiom audits pass. Continue
with pattern/projection computation and structure eta, while keeping the model's
head-exposure purpose separate from arbitrary equality reflection.

### Computational projections lower with reconstructed field typings

`ProjectionComputation.lean` adds registered saturated-constructor projections to
beta and closed declaration computation. `ProjectionCompute.lift_inv` lowers
complete compatible finite paths through arbitrary lifts without any typing
premise. `ProjectionCompute.simAt` replays each projection using the existing
`HasType.projIota_field`, reconstructing its dependent field typing from the source
projection typing and the saturated constructor arity. `descend` combines these:
only the original source typing below is needed, not any ambient field typing.
`function_type_below` now covers computational Pi exposures through these paths.

The saturation premise is explicit. Eta elimination for this enlarged operational
relation is not yet proved; the earlier finite observations still lack field and
constructor observations. This is computational replay infrastructure for that
extension, not full head-exposure adequacy or a sufficient strengthening residue.
All new main results and the reused field-typing theorem are axiom-clean, and the
module builds. Next: projection cancellation of structure expansions with arbitrary
parameters, followed by their integration into the finite head observations.

### Eliminating captured parameters from nested structure expansions

`ProjectionEtaCancellation.lean` introduces `RecordExpansion`, a finite nesting of
root structure expansions with independently chosen levels and parameters at each
node. `cancel_projection` removes the whole nesting by actual saturated projection
computations. No intermediate typing or scope assumption is needed. The typed
corollary replays cancellation at the expanded projection's exact type when that
source typing is supplied. Further applications preserve the cancellation.

`ProjectionEtaExamples.lean` exhibits a registered structure expansion with a fresh
variable in its parameter list. Its syntax fails `Skips 1 0`, yet projecting a
valid field computes exactly to the original lifted projection. This is a syntactic
scope test, not an assertion that the deliberately arbitrary captured parameter is
well typed. Nested cancellation uses the finite expansion derivation, not a fixed
number of development passes.

`ProjectionHeadRigidity.lean` proves that beta/delta/projection paths preserve a
non-unfolding constant head. Actual registered constructor heads satisfy this
premise by `WF.projectionCtorRigid`. Thus a displayed structure expansion cannot
itself compute to a Pi or sort in this operational fragment. A surrounding
eliminator is essential; the local projection case is now checked.

All three modules build without new warnings; cancellation, the captured-parameter
example, and head rigidity are axiom-clean. Full eta elimination remains open:
local cancellation of nested root expansions is not a proof about arbitrary
interleaved compatible paths. Next, extend finite observations with field demands
and constructor observations so the beta/substitution/eta argument can account for
these computational eliminators. Pattern/prefix computation remains outside the
current projection relation. The strengthening goal is still open.

### Finite field observations and constructor demands

`FieldObservation.lean` extends the finite-demand syntax with field observations
and curried constructor observations, using actual `ProjectionCompute` paths as
its operational interpretation. Constructor observations select a demanded field
argument at the registered saturated arity. `Obs.realizes` proves operational
adequacy under realizing substitutions, including constructor and projection cases.

`FieldObservationEta.lean` and `FieldObservationSubstitution.lean` carry the
renaming, subsumption, function-eta, substitution-inversion, and finite-support
proofs over the richer syntax. `FieldComputationObservations.lean` proves backwards
closure for every beta/delta/projection path. Its `Obs.ctor_spine` constructs a field
observation from only the selected field's observation; unrelated arguments can
have empty demands. No typed quotient classes or normalization assumptions enter.

This extends the previously checked operational model while retaining its API in
the original modules. Structure-eta soundness is next: it requires inversion of
constructor observations and the actual environment's constructor rigidity.
The four new modules compile without new warnings, and realization, eta,
substitution, finite support, constructor observations, and backwards computation
closure are axiom-clean. The strengthening goal remains open.

### Both eta expansions eliminated from projection head exposure

`FieldStructureEta.lean` proves `Obs.struct_eta_back`. Inverting the constructor's
curried observation leaves one field demand; constructor-family uniqueness aligns
it with a projection of the original value, and subsumption composes the payload
demands. Actual constructor rigidity rules out the alternative declaration-body
case. Parameters and levels may be arbitrary, and neither the value nor the new
parameters require typing or scope premises for this syntactic result.

`FieldHeadExposure.lean` combines computation, function eta, structure eta, and
all syntax congruences in `EtaCompute`. `pi_exposure` and `sort_exposure` recover
actual beta/delta/projection paths from arbitrary finite mixed paths. The Pi path
lowers through an arbitrary lift; `function_type_below_ofEnv` reconstructs a genuine
Pi typing below for actual environment equations, and `function_eta_below` supplies
a typed full eta step there. `of_etaPar` embeds every actual parallel eta step from
the full confluence presentation, including changed domains/parameters. The earlier
beta/delta/function-eta fragment also embeds.

`FieldHeadExamples.lean` checks a registered one-parameter, one-field constructor
whose function and structure expansions both use a fresh variable. The intermediate
fails scope, but the mixed trace still gives computational Pi exposure below.
Arbitrary annotations in this syntactic test are not claimed well typed. The
`variable_no_pi` boundary confirms that unrestricted eta does not manufacture a Pi
head from a free variable in this fragment.

All new modules build without new warnings. Structure eta, mixed-path preservation,
head exposure, smaller-context typing, the examples, and the actual EtaPar embedding
are axiom-clean. This is now a head-exposure theorem for both eta forms and actual
projection computation, not just a local cancellation. Pattern and singleton/quotient
prefix computation remain absent, and full head exposure still would not alone
settle the remaining matched-lambda comparison repair. The original strengthening
goal remains open. Next: add observations and operational realization for recursor
computation, including how structure majors compute through singleton prefixes.

### Closed Quot.lift unfolding replaces all quotient-prefix replay checks

Inspection of the remaining rules distinguishes two cases: existing singleton
prefix unfolding is restricted to proposition-valued majors, whereas unfolding a
structure major in Type through its projections requires a separate reconstruction
argument. The latter is still open. For the quotient, however, the checked
five-argument rule is sufficient to derive a closed equation.

`ClosedQuotUnfolding.lean` opens the first five binders of Quot.lift's exact constant
type, applies `QuotPrefixUnfold.atFive` at fresh variables, and closes the equality
by eta. `equation` proves Quot.lift.[u,v] equal to a closed lambda value whenever
u is equivalent to zero. This uses only QuotRegistered, environment WF, and the
universe guards. `generated_zero_rhs` identifies that value with the zero-prefix
generator result, and `generated_prefix_beta`/`value_prefix_beta` prove that supplying
any admissible prefix beta reduces it to the exact generated RHS. Generation and
beta replay here have no occurrence-specific typing premises.

`QuotHeadComputation.lean` adds this proved equation to the declaration collection.
Its soundness in arbitrary contexts is ordinary weakening of the closed equality;
constructor rigidity is preserved because Quot.lift's stored rule prevents its
being a projection constructor. `prefix_compute` embeds EVERY checked quotient
prefix as one closed constant unfolding followed by beta. This discharges the
whole quotient-prefix family in the mixed field head-exposure model, not merely
the five-argument prefix.

`prefix_descend` reconstructs the computational equality below an arbitrary lift
from the original source typing alone. `prefix_reflect` is the exact equation when
both endpoints are supplied below. It does not descend `UnfoldingCheck` fields;
the closed equation bypasses those occurrence-specific checks. `function_type_below`
uses the augmented collection with all soundness and rigidity conditions discharged.

Both modules build without new warnings, and the closed equation, generated beta
replay, model soundness, prefix descent/reflection, and head reconstruction are
axiom-clean. This is a new checked strengthening result for the quotient-prefix
reduction family, not the full strengthening deliverable. Ordinary recursor patterns,
index-sensitive singleton prefixes, structure-major reconstruction, and the general
comparison-repair argument remain open. Do not infer that unaligned Eq.rec admits
a checked zero-prefix unfolding from this quotient-specific construction.

### Uniform pattern checks and context-independent core computation

`PatternTypingChecks.lean` adapts the quotient alignment proof from route A's
`CoreDescent.lean`, with explicit attribution. This is reuse of the earlier core
result, not a new solution of that alignment problem. The new packaging is
`CheckFromTyping`: for a fixed pattern, rule, and universe instance, EVERY matching
source in EVERY well-formed context passes the checks whenever it is typed.
`ConcretePattern.checkFromTyping` obtains this uniform certificate from any enabled
concrete rule. Definitions have no checks; ordinary recursors have only universe
guards; quotient parameter and relation alignment is reconstructed by rigid Quot
head injectivity at the new occurrence.

`PatternComputation.lean` extends `ProjectionCompute` by registered pattern steps
carrying this uniform certificate. `of_parRed` embeds every actual concrete core
parallel step, including parallel computation of its captures, without needing
source typing or ambient context WF. `subst` survives arbitrary raw substitutions;
`lift_inv` lowers entire paths syntactically. The certificate does not mention the
original source/captures/context, so these operations retain it unchanged.
`simAt` then reconstructs intermediate typings from the source in the replay
context. `descend`, `reflect`, and `function_type_below` combine these two layers.
In particular, `core_reflect` reflects actual core steps between lifted endpoints
using only source typing and context WF below. It does not need an ambient context
WF premise or a relation between the two contexts.

Both modules build, and the uniform-check theorem, raw substitution, concrete
embedding, lift inversion, typed replay, reflection, and Pi-type recovery pass the
axiom audit (only propext, Classical.choice, and Quot.sound, or subsets). No executable
changes. The declaration collection remains a parameter, so the previously checked
closed quotient equation is available in these larger paths as well.

Remaining work is not discharged by this operational extension. The finite field
observation model still uses ProjectionCompute; backwards preservation and eta
elimination for PatternCompute need constructor/recursor observations. Constructor
argument demands must share one exposed constructor tuple to avoid assuming that
separately exposed fields can be joined. Projection constructors need special
handling because structure eta can introduce their head. Index-sensitive singleton
prefixes and the general matched-lambda comparison repair also remain open. This
is a checked extension of the research infrastructure, not a smaller sufficient
obligation or a completed strengthening proof.

### Finite constructor tuples integrate ordinary iota into mixed head exposure

The preceding turn's PatternCompute supplied operational replay but no backwards
observation theorem for patterns. This turn fills that part for every iota rule
whose major constructor is not a registered projection constructor. No restriction
on the shape of the pattern RHS is imposed.

`ConstructorObservation.lean` adds `Ob.ctor name keys`. Its realization exposes ONE
constructor application and realizes all argument demands in that same application.
This avoids requiring a confluence theorem to join separately exposed arguments.
Only non-projection constructors introduce these tests; projection constructors
retain their field-only interpretation. `RHSRealizes` is a uniform semantic
certificate: every assignment of captures satisfying the finite demand map realizes
the instantiated RHS. `Realizes.recursor` combines this certificate, one constructor
tuple, the ordinary recursor argument demands, and the uniform check certificate
from the previous turn. The new primitive is independent of occurrence valuations.

`ConstructorObservationEta.lean` and `ConstructorObservationSubstitution.lean`
extend the checked finite-support, renaming, function-eta, substitution-inversion,
and backwards-beta arguments. Constructor demand subsumption needs only reflexivity;
function and field subsumption remain as before.

The key additional construction is `Obs.apply_pat_inv` in
`ConstructorComputationObservations.lean`. Induction on the actual RHS observation
extracts a finite demand list for each capture and a RHSRealizes certificate. Fixed
parts use closedness and operational adequacy; variable parts demand the observed
key; application merges the function demands and the finitely many argument demand
maps. Thus the recursor primitive's semantic premise is established from every
actual reduct observation, not left as an external assumption. `Obs.iota_back`
uses the extracted certificate and a common constructor tuple to preserve all
observations backwards through the rule.

`ConstructorStructureEta.lean` retains backwards structure eta. Constructor tests
cannot arise at a projection constructor, and recursor primitives cannot arise
there because actual pattern heads have stored rules whereas projection constructors
are rigid. Constructor-family uniqueness then reduces the remaining observations
to the original field argument, as in the preceding model.

`ConstructorHeadExposure.lean` puts these results together: finite compatible paths
mix beta, closed declarations, projections, non-structure iota, arbitrary function
eta, and arbitrary structure eta. `of_iota` embeds actual enabled concrete rules,
including further mixed paths in their captures. `pi_exposure_below` recovers an
actual PatternCompute path below the lift; `function_type_below_ofEnv` reconstructs
its typing from the original source. `of_quotPrefix` and
`function_type_below_quot` carry all previously checked quotient-prefix computation
into this larger model, with soundness and rigidity discharged for its closed
quotient equation.

All six modules build without new warnings. The operational recursor certificate,
adequacy, both eta proofs, finite capture extraction, iota preservation, concrete
embedding, Pi exposure below, and smaller-context typing pass the axiom audit:
only propext, Classical.choice, and Quot.sound (or subsets), with no sorryAx.
The executable remains unchanged.

The remaining cases have not been hidden in a completeness claim. Structure-major
iota needs a field-based computational replay (including the typing of any
reconstructed constructor); index-sensitive singleton prefixes remain open.
Even full head exposure would not yet settle the matched-lambda comparison repair.
This is progress on the active computational route, not the full strengthening
deliverable or a newly sufficient obligation smaller than PropFront.

### Dependent structure reconstruction and projected-iota replay

Inspection of `projDF` exposed a necessary distinction: its source-sort guard is
IsNeverZero, whereas the ordinary large-eliminating iota guard is only failure of
level equivalence to zero. A universe parameter can satisfy the latter while failing
the former. Similarly, non-proof fields of a Prop structure cannot simply be
projected. The reconstruction therefore keeps the actual field guard, rather than
assuming that every typed structure major has a typed eta expansion.

`StructureReconstruction.lean` extends the declaration/parameter argument from
`HasType.unitLike_constructor` to structures with arbitrarily many dependent fields.
`projection_args_typed` walks the constructor telescope by strong induction: it
instantiates each domain using the already typed parameters and earlier projections,
identifies that domain with fieldType, checks its projection guard, and types the
next projection. `structure_constructor` first recovers the constructor parameter
typings from the family's normalized parameter telescope and the declaration's
common parameter context. It then applies the constructor to the entire typed
projection spine and identifies its result with the original unindexed family.
No typing of the expanded constructor is assumed.

`structure_constructor_neverZero` discharges every field guard for a never-zero
source universe. `structure_eta_neverZero` gives an actual typed eta equation from
source typing at the family alone, without any expanded-endpoint typing premise.
The general guarded theorem also permits proof-valued fields through the other
branch of projDF's guard.

`StructureIotaReplay.lean` uses this reconstruction to replay a pattern after eta
expansion in the smaller context. `projected_iota` then uses Params.pat_iota_params:
the rule RHS ignores the constructor parameters and levels. Consequently the raw
matching witness may contain arbitrary dummy constructor parameters and levels;
they need neither typings nor scope. The proof replaces them with the major's
actual family parameters while establishing typing and then returns the exact
original RHS. `projected_iota_neverZero` discharges its field-guard premise.

Both modules build without new warnings. Reconstruction, typed eta, pattern replay,
and projected-iota parameter replacement pass the axiom audit with only propext,
Classical.choice, and Quot.sound. No executable changes or strengthening axiom is
used.

This does not yet add structure-major iota to ConstructorObservation.EtaCompute.
The replay currently takes the major's registered family typing below and the
projection guards as explicit premises; the generic raw computation model needs
those recovered uniformly. A promising next step is to reconstruct at the generic
recursor telescope and close the result into a constant equation, following the
successful closed quotient unfolding. That still requires matching the registered
recursor's major-family metadata and discharging the field guards at the generic
instance. Prop-source structures, potentially-zero universes, index-sensitive
singleton prefixes, and the final matched-lambda comparison repair remain open.
The full goal is not complete.


### Closed structure equations and raw iota simulation

`StructureFamilyArity.lean` proves that a typed saturated registered family has
exactly its parameter-plus-index arity. The proof identifies its normalized
signature and uses sort-head rigidity; it does not use strengthening.

`ClosedStructureUnfolding.lean` supplies deterministic pattern captures and a
closed lambda program for a registered structure recursor. At the generic recursor
telescope, the registered major-type theorem and family arity recover the exact
parameter list. The preceding projected-iota replay then applies, and eta closes
its equation in the empty context. `canonical_equation` chooses the telescope from
the registered recursor type automatically. Its assumptions concern the registry,
the enabled rule's uniform typing check, well-formed universe arguments, zero
indices, and a never-zero source universe; there is no occurrence-specific typing
or expanded-major typing premise.

`StructureHeadComputation.lean` adds these closed equations to arbitrary sound,
constructor-rigid definitions, preserving soundness and rigidity. It embeds the
entire earlier EtaCompute relation, including non-structure iota, function and
structure eta, and existing closed quotient equations. Saturation of the new
constant equation computes by finite beta reduction to its supplied body.
Smaller-context function-type reconstruction is available both over ordinary
stored definitions and over the earlier quotient extension.

`StructureUnfoldingSupply.lean` identifies that supplied body with the pattern RHS
on projections of the raw major. For an actual constructor match, all field
projections compute to its field suffix. Checked iota parameter independence
restores the original parameter captures and levels from the closed dummy values.
`iota_compute` consequently simulates every raw match of a covered rule by the
augmented ProjectionCompute relation, with no source or argument typings.
`iota_etaCompute` embeds this directly into the mixed observation model.
`concrete_iota_etaCompute` obtains the uniform check certificate from an actual
enabled concrete rule.

All four modules build successfully (265 dependency jobs). The family arity,
closed equation and closedness, definition soundness and rigidity, prior-model
embedding, raw supplied computation and iota simulation, concrete-rule wrapper,
and smaller-context function-type wrappers pass the axiom audit with only
propext, Classical.choice, and Quot.sound (or subsets). No executable changes.

This closes the previously explicit integration gap for unindexed structures
whose instantiated source universe is never zero. It does not cover a source
universe that merely fails to be identically zero, nor Prop structures with
non-proof fields. Extending the generic equation to admissible proof-field guards
is still live; arbitrary registered structures must not be assumed eta-expandable.
Index-sensitive singleton prefixes and matched-lambda comparison repair remain
open. The full strengthening goal is still active; these are checked fragments,
not a new sufficient obligation claimed smaller than PropFront.


### Proof-field certificates extend closed structure replay

The prior never-zero condition has been generalized to `ClosedStructure.Admissible`:
either the source universe is never zero, or every constructor field domain is
proved to be a proposition in its own closed prefix telescope. The latter is the
new `StructureReplay.ProofFields` certificate. It has no occurrence parameters,
major, or reconstructed-endpoint typing. `of_telescope` shows that one displayed
constructor telescope suffices; `of_decl_telescope` specializes evidence proved
at the declaration's universe parameters to any well-formed universe instance.

Inside `projection_args_typed`, the strong induction already establishes typings
for the supplied parameters and earlier projections. These instantiate the closed
proof-field typing at the current field. Type uniqueness identifies its sort with
the sort obtained from general telescope formation, proving the zero-sort branch
of projDF's guard. `structure_constructor_proofFields` therefore reconstructs the
whole constructor at any source universe with this certificate. The original
occurrence-specific guard remains an alternative in the general reconstruction
and projected-iota theorems.

The certificate is threaded through the generic recursor closure, augmented
closed definitions, finite saturation computation, raw iota simulation, concrete
rule wrapper, and mixed-model function-type reconstruction. All previous
never-zero cases remain via the first branch of Admissible. Zero-field structures
have a vacuous certificate at every universe. `StructureProofFieldExamples.lean`
checks the conjunction-shaped telescope [Prop, Prop, bvar 1, bvar 1] directly using
variable typing, establishing its two fields as propositions independently of the
constructor result or source universe.

The complete example target builds (266 dependency jobs) without new warnings.
The extended pipeline and all new certificate constructors pass the axiom audit:
only propext, Classical.choice, and Quot.sound, with no sorryAx. Executable code
is unchanged.

These are projection-admissibility results for enabled rules. A large-eliminating
ordinary iota rule disabled at a zero-source universe does not acquire a uniform
check merely because its fields are proofs. Its singleton-prefix computation
still requires a separate argument. Likewise, the certificate has not yet been
recovered automatically from all applicable singleton registration metadata.
Potentially-zero sources with non-proof fields, indexed singleton prefixes, and
the final matched-lambda comparison repair remain open. No completion or smaller
sufficient obligation is claimed.


### Generic reconstruction of unindexed singleton prefixes

The next obstacle is the confluence engine's singleton-prefix computation at a
Prop source, where its ordinary iota rule is guarded off. This differs from the
environment's actual stored iota pattern: `PatEquation` still realizes the
installed equation at typed instances. The prefix check must establish a typed
reconstructed major, a typed equation-capture telescope, and exact recursor-spine
alignment. An arbitrary indexed family does not supply those alignments at fresh
indices, so a blanket zero-prefix closure would be unjustified.

`SingletonProofReconstruction.lean` removes the pre-existing field-instance premise
from proof-only extraction. With no data slots, the instantiated cast substitution
is the identity on its arguments and the extraction's cast arguments equal its
reconstructed fields. The proof-field step of `PropElim.occ_typed` can therefore
be replayed without comparison to an original field list. `SingletonProof.occ_typed`
derives the cast and field telescope typings from the typed parameters, indices,
and major alone. `slots_none` obtains the all-proof condition for an unindexed
well-scoped layout, and `unindexed_eta` then invokes singleton eta with the newly
constructed field instance. No original constructor instance or index-alignment
premise is supplied. Canonical Eq is used by the existing proof extraction typing.

`SingletonUnindexedTelescope.lean` connects this result to actual registration.
`type_shape` identifies the specialized recursor's exact parameter, motive/minor,
and major telescope with the extraction family. `generic_major_args` derives the
parameter and major instances in that fresh telescope. `registered_reconstruction`
obtains `PropElim.WF` from the registered large-eliminating singleton, checks that
there are no index slots, and provides the generic context, typed prefix, typed
extracted fields, and reconstruction equation. Its premises are environment WF,
canonical Eq, registration, the Prop-source specialization, universe WF/count,
an owned constructor, extraction metadata, and zero indices. It does not take
occurrence typings or a caller-provided reconstruction certificate.

`captures_typed` inserts the motive/minor arguments between parameters and fields
while preserving dependent field typings. `lhs_instOuter` proves the exact raw
substitution of that capture list into the unindexed equation's left side.
The existing `singleton_equation_syntax` theorem now also identifies its two-entry
middle telescope with the actual motive/minor list; its `zero_join` consumer is
updated and remains checked.

Both new modules build without new warnings. All new reconstruction, telescope,
capture, and syntax theorems, plus the changed syntax theorem and its existing
zero_join consumer, pass the axiom audit with only propext, Classical.choice, and
Quot.sound (or subsets). No strengthening axiom or executable changes are used.

The full generated zero-prefix check and resulting closed constant equation are
not yet assembled. After that, successful generation at every arity and the
existing singleton supply-one theorem should provide all-prefix beta simulation,
as for the quotient construction. Indexed singleton alignment, remaining ordinary
structure cases, and full matched-lambda comparison repair remain open. The main
goal is active; this is supporting progress, not a claimed sufficient obligation
smaller than PropFront.


### Closed equations for every unindexed singleton prefix

`ClosedSingletonUnfolding.lean` assembles the preceding generic reconstruction
into an equation of the bare recursor constant in the empty context. The proof
identifies the exact registered equation and its motive/minor telescope, types
its captures using the extracted fields, and computes the instantiated left side
syntactically. It replaces the fresh major by its typed reconstructed constructor,
applies `PatEquation.instOuter`, and closes the resulting body equation by eta.
A separate syntactic calculation identifies the closed value with the actual
program returned by `singletonUnfolding` at the empty prefix. Thus the proof does
not assume a zero-prefix check or a caller-supplied unfolding equation.

`zero_equation_exists` constructs the zero program from registry data and an
owned constructor. `zero_equation` recovers that constructor from successful
generation and uses determinism to obtain the equation for the supplied program.
`zero_closed` follows from the empty-context equality. `generated_template_closed`
recovers the registered equation body's scope at every prefix. Using the existing
supply-one theorem, `generated_prefix_beta` proves finite beta specialization from
the zero program to every generated prefix. This last syntax theorem also permits
indices; it is the closed zero-prefix equation that currently needs zero indices.

`SingletonHeadComputation.lean` adds the closed singleton programs to arbitrary
sound, constructor-rigid definitions. Actual stored iota heads establish that
these recursors cannot be projection constructors, preserving the rigidity needed
by backwards structure eta. The complete previous mixed path relation embeds.
`generated_compute` simulates every generated unindexed singleton prefix on raw
arguments by one closed unfolding and finite beta computation. `prefix_compute`
discards the occurrence-specific checks of an actual checked prefix after
selecting its unindexed registry entry.

`prefix_descend` and `prefix_reflect_ofEnv` give exact smaller-context replay from
source typing below, with no ambient capture or major checks assumed to descend.
The combined `function_type_below_quot_structures` wrapper retains stored equations,
non-structure iota, all covered structure-iota equations, every quotient prefix,
every unindexed singleton prefix, and both eta forms.

The complete new head target builds (270 dependency jobs), without new warnings.
The closed equation, generated scope, all-prefix beta specialization, closedness,
definition soundness and rigidity, previous-model embedding, raw simulation,
exact prefix descent/reflection, and combined head-exposure wrapper pass the axiom
audit: only propext, Classical.choice, and Quot.sound, with no sorryAx. No executable
changes. This uses canonical Eq substantively through proof extraction, not just
through confluence.

Indexed singleton prefixes still require an argument for their actual alignment
checks; the closed zero-prefix equation is not claimed for arbitrary fresh indices.
Ordinary structure iota with potentially-zero sources and non-proof fields also
remains outside the covered projection construction. A related next refinement
is to carry the actual zero-index guard in the raw structure-eta model, allowing
constructor tests at indexed projection constructors which cannot undergo actual
structure eta. Full head exposure would still leave matched-lambda comparison
repair. The main strengthening goal remains active; no new sufficient obligation
strictly smaller than PropFront is claimed.


### Indexed constructor tests with the actual structure-eta guard

The constructor-observation model previously excluded every projection constructor
from tuple tests, because its raw eta relation allowed expansions for arbitrary
projection metadata. Actual typed structure eta requires zero indices. The model
now retains that guard and replaces `NotProjectionCtor` with `NotEtaCtor` in the
tuple and ordinary-iota rules. Ordered-environment constructor-family uniqueness
shows that indexed metadata cannot have a second unindexed registration, so
`NotEtaCtor.of_indexed` admits every indexed projection constructor.

`EtaCompute.of_etaPar` still embeds every actual eta step. The closed structure
and singleton definition extensions preserve the refined mixed relation, and
`of_nonProjection_iota` retains the old ordinary-iota assumptions. The indexed
entry points `iota_indexed` and `of_indexed_iota` discharge the new criterion from
metadata alone; the latter retains arbitrary mixed paths in captured arguments.
The ordinary rule's enabled universe check remains necessary.

`IndexedConstructorExamples.lean` checks the semantic boundary. Empty tuple
demands observe a testable constructor without inspecting its arguments.
Consequently `indexed_eta_excluded` rules out a raw path from a free variable to
its indexed structure expansion under constructor-rigid definitions: backwards
observation closure would put a constructor observation at a variable in the empty
valuation. This is a boundary of the computational model, not a counterexample
to typed strengthening. The previous raw model's unrestricted indexed eta paths
do not embed; every actual typed eta path does.

The example target and combined model build successfully (271 dependency jobs).
The axiom audit covers indexed eligibility, semantic realization, finite pattern
capture extraction, iota and structure-eta backwards closure, actual eta and
indexed-iota embeddings, head exposure and function-type recovery below, both
boundary examples, the combined quotient/structure/singleton wrapper, and exact
singleton-prefix reflection. Dependencies are only propext, Classical.choice,
and Quot.sound (or subsets), with no sorryAx. Executable code is unchanged.

This removes indexed *ordinary iota* from the constructor-test restriction. It
does not justify a closed zero-prefix singleton equation with arbitrary fresh
indices or discharge the generated prefix's alignment checks. Unindexed structure
iota outside the current projection admissibility criterion and full
matched-lambda comparison repair also remain open. The main goal remains active.

### Exact admissibility of typed structure expansions

`StructureEtaAdmissibility.lean` now checks. `projection_result_prop` compares the
source family's universe at the projection's inferred instance with the supplied
major typing. If that source universe can be zero, the projection guard forces
its result type to be a proposition. `proofFields_of_expansion` applies this to
every projection in a typed constructor expansion, instantiates the closed
constructor telescope, and uses sort uniqueness to recover the proposition typing
of each field in its original closed prefix. It does not strengthen an occurrence
typing. `expansion_typed_iff` pairs this necessity result with the existing
reconstruction theorem, yielding an exact criterion.

The module builds (218 dependency jobs); all three new theorems have only
propext, Classical.choice, and Quot.sound as axioms, without sorryAx. No executable
changes. This is progress beyond the previous checkpoint, not a solution of the
main front. The next model refinement must retain constructor universe instances:
the new eta criterion is universe-sensitive, while existing tuple observations
forget constructor levels. Indexed singleton alignment and matched-lambda repair
remain open.

### Universe-sensitive tuple tests and complete ordinary-iota coverage

Constructor tuple observations now retain the actual constructor universe list.
`NotEtaInstance` excludes only unindexed instances with a closed eta-admissibility
certificate. Its exact classification for a registered projection constructor is
proved by `iff_registered`: indexedness or failure of that certificate. The mixed
structure-eta rule carries the certificate, and `EtaCompute.of_etaPar` derives it
for every actual eta path from a typed source. The source typing also supplies
well-formed contexts under binders; the previous embedding's arbitrary untyped
source presentation has accordingly been narrowed. Actual typed eta is retained.

`StructureEtaUniverses.lean` proves context conversion for pointwise level
variants, transports ProofFields across equivalent well-formed universe lists,
and aligns a typed constructor's actual universe list with its major-family
instance. These are context conversion and uniqueness arguments, not context
strengthening. The raw observation/replay relation needs no occurrence typings.

`StructureIotaCoverage.iota_typed` covers every typed registered structure-iota
match. Indexed instances use tuple tests. An admissible unindexed recursor
instance uses the already-proved closed projection equation. In the remaining
case universe alignment proves that the actual matched constructor is itself
eta-inadmissible, so its tuple test applies. No projection certificate is assumed
from the caller, and the ordinary rule's enabling guard is retained.

`OrdinaryIotaCoverage.concrete_iota_coverage` removes the registry, family and
arity premises as well. The concrete pattern table supplies the recursor; a typed
major identifies any projection registration with the recursor's rigid family
and recovers its full constructor arity. Quotient constructors cannot have
projection metadata. Thus every enabled concrete ordinary iota occurrence is
covered from source typing alone, including structures at potentially-zero
universes with non-proof fields. The singleton extension imports the result and
preserves the refined model and all earlier closed computations.

The combined example target builds (275 dependency jobs). Eighteen axiom audits
cover the universe transport, tuple semantics, iota preservation, typed eta
embedding, head exposure and reconstruction, complete concrete iota coverage,
combined singleton wrapper, and both guard-boundary examples. All use only
propext, Classical.choice, and Quot.sound; no sorryAx. No executable changes.

The new `inadmissible_eta_excluded` example verifies that dropping the new guard
would incorrectly put a constructor observation at a free variable. This is a
boundary of the raw model, not a counterexample to strengthening. Remaining work
includes embedding the complete typed core/full paths, indexed singleton-prefix
alignment, and the matched-lambda comparison repair. No proof, canonical-Eq
counterexample, or smaller sufficient obligation for the main front is claimed.

### Actual typed core paths, eta interleavings, and Pi recovery below

`CoreHeadExposure.lean` connects complete core derivations to the refined model.
`definition_compute` identifies a concrete constant pattern with its stored
closed equation, recovering the actual universe instance from source typing.
`concrete_pattern_compute` combines that with complete concrete iota coverage.
`core_compute` then inducts on actual ParRed derivations. In the pattern case,
source typing recovers typings for every capture, so all parallel recursive
capture reductions embed; binders similarly supply their own context typings.

`CoreEtaTrace` is the finite closure of actual ParRed and EtaPar. Its `compute`
theorem carries the source type through the trace using existing subject
reduction and embeds the whole trace into the observation model.
`function_type_below_core_eta` applies this to a lifted type under an arbitrary
Ctx.LiftN insertion. The finite observation theorem removes eta, syntactic descent
lowers the recovered computational exposure, and replay gives a Pi typing below.
Eta annotations need not avoid the inserted binders. This requires no canonical-Eq
hypothesis, because ordinary core rules retain their universe guards; the special
zero-source singleton computations are not claimed here.

The target builds (270 dependency jobs), and all five bridge/recovery theorems
have only propext, Classical.choice, and Quot.sound as axioms. No sorryAx and no
executable changes. The model API's consumers were checked by source search; all
occur in the dependency closures of the combined example and core targets built
in this turn. This turn made authoritative progress and pushed the checkpoints.

Completion remains unproven: weakN_iff is still open, there is no canonical-Eq
counterexample, and no new sufficient obligation strictly smaller than PropFront
has been established. CoreEtaTrace deliberately excludes projection-iota and
prefix steps; their existing model simulations still need a unified typed trace
bridge. Indexed singleton prefixes still lack their alignment argument. The
matched-lambda comparison repair remains after full head exposure. These are
live work items, not rejected routes or a blocked state.

### Unified full-reduction bridge with indexed replay isolated

The prior turn is classified as progress: its commits and checked core/eta bridge
are present at the start of this turn. The worktree was clean at bf4dbdde.

`FullHeadExposure.lean` combines stored equations, conditionally registered
quotient unfoldings, closed structure equations, and closed unindexed singleton
equations into one sound, constructor-rigid collection. Equation inclusion lifts
computation and mixed paths, so the checked complete core simulation embeds.
Quotient registration is recovered from each actual quotient-prefix step; the
model works in canonical-Eq environments without Quot as well.

`step_of_indexed` inducts on the actual FullStep relation. Projection inversion
and typed major-family alignment recover projection-iota's complete constructor
arity. Typed structure expansions recover their closed admissibility certificate.
Unindexed and quotient prefixes use their existing closed computations. Only
registered indexed singleton prefixes use the named `IndexedPrefixReplay`
hypothesis. `reduction_of_indexed` threads actual subject reduction through finite
full traces, and `function_type_below_of_indexed` then recovers a Pi type below an
arbitrary binder insertion.

The full target builds (276 dependency jobs), and eight axiom audits cover model
soundness and rigidity, the three unconditional computational embeddings, both
full bridges, and conditional Pi recovery. Only propext, Classical.choice, and
Quot.sound occur. No executable changes and no sorryAx. The isolated replay
premise is a model-specific obligation, not a newly established sufficient
obligation strictly smaller than PropFront. Its truth for the current raw model
still needs testing; it must not be conflated with the more general typed head
exposure problem.

### Checked free-major boundary for indexed proof elimination

`IndexedPrefixBoundary.lean` tests the model premise instead of assuming it will
follow from more metadata. A recursor's registry entry fixes the major offset of
every ordinary pattern at that head. When no closed equation unfolds the head,
a Pi observation at the fully supplied spine must use a recursor observation.
Such an observation demands a constructor tuple from its major. A free variable
in the empty valuation supplies none. `recursor_variable_no_pi` therefore excludes
all mixed computational/eta paths from such a spine to any Pi, even when its
preceding arguments can compute. This uses finite observation inversion, not a
normalization assumption.

`eqRec_no_stored_unfold` shows that canonical Eq.rec has no stored constant
unfolding: the canonical iota pattern and stored-definition heads are disjoint.
`canonical_cast_boundary` combines the obstruction with `IsDefEq.typeCast_refl`.
Given the actual Eq.rec registration with major offset five, a typed Pi term, its
type, and a free proof of reflexive equality of that type, canonical Eq proves the
cast equal to the Pi. The stored-definition/guarded-iota/projection/eta model has
no corresponding path. Registration and all typing premises are retained; no
concrete environment witness or strengthening counterexample is asserted.

This refutes direct indexed K simulation in that precise model. It does not yet
refute the newer full equation collection, because the no-unfolding premise must
also exclude its derived structure and singleton equations. Nor does it refute
typed head exposure: the example already has the required Pi equality below.
It shows why the free major cannot simply be treated as an ordinary constructor
tuple. Further indexed work must change the model or justify additional closed
computations; repeatedly trying to derive tuple demands from the empty valuation
would repeat a checked obstruction.

The combined boundary target builds (277 dependency jobs). Its five key theorems
have only propext, Classical.choice, and Quot.sound (or subsets) as axioms, with no
sorryAx. No executable changes. Full strengthening, a canonical-Eq counterexample,
and a smaller sufficient front remain unestablished; the goal remains active.

### Nonlinear canonical cast computation with source-only replay

The preceding checkpoint remains progress, not a completed strengthening proof.
`ReflexiveCastReplay.lean` inverts the complete canonical Eq.rec telescope of an
arbitrarily typed type cast. It recovers the universe and typings of both endpoint
types, the equality proof, and the payload. This allows canonical K replay at any
source typing when the endpoints are syntactically identical, including a free
proof variable.

`CastComputation.lean` adds that nonlinear rule to concrete pattern computation.
Arbitrary substitution preserves the repeated endpoint. Binder insertion reflects
it: applying the lift retraction recovers the complete cast shape, and application
injectivity recovers the output payload. The compatible/transitive closure thus
lowers through arbitrary lifts and replays entirely from source typing below.
No ambient typing, equality guard, or scope premise is imported into replay.

The target builds (239 dependency jobs); six axiom audits contain only propext,
Classical.choice, and Quot.sound, or subsets. There is no sorryAx dependency and
no executable change. This is a sound extension of computational descent, not a
proof of full head exposure: eta can potentially create a nonlinear endpoint
match, and general indexed prefixes have more alignment than this one cast rule.
The next test is whether eta removal survives even this restricted extension.

### Raw eta elimination fails for nonlinear K

`CastEtaBoundary.lean` checks the next test in the minimal beta/K fragment.
The two cast endpoints are a neutral application F f and F (λ x. f x). The
payload is a Pi. Both copies of the short endpoint (the explicit endpoint and
the one in the cast motive) eta-expand to the long one, enabling reflexive K.
A decidable normal certificate shows that the original source has no beta or
syntactically reflexive cast redex anywhere. Induction over the full compatible,
transitive beta/K relation proves that every reduct is the original source.
Thus the raw eta-enriched path reaches a Pi and the eta-free relation cannot.

The theorem is deliberately limited to this raw fragment. No source typing or
canonical environment witness is asserted, and extra declaration computations
might repair the example. It does rule out extending the previous *untyped*
eta-removal argument with nonlinear K and no other change. This is not a
strengthening counterexample. The target builds (240 jobs); the boundary's axiom
audit contains only propext and Quot.sound.

### Typed universe alignment repairs an outer cast

`CastTypedReplay.lean` establishes a typed alternative to raw nonlinear matching.
`cast_eq_of_common_typing` first observes that a cast and payload at a common
type force conversion of their endpoint types by uniqueness, hence canonical K.
The stronger `cast_type_eq` needs only that each is a type below. If their sort
levels are v and w, the cast endpoint universe u is convertible to both succ v
and succ w. Universe injectivity gives v ≈ w, so the common-typing theorem
applies. There is no ambient equality premise, use of strengthening, or syntactic
endpoint equality.

A computational Pi exposure of the payload supplies its required typehood:
replay from the payload's recovered source typing, invert the resulting Pi's
typing, and transfer that sort typing back along the computation. This proves
`cast_pi_exposure_below` for a lifted payload computation. `CastHeadExposure.lean`
then removes both eta forms from an existing mixed payload trace, invokes this
bridge, and recovers a function's Pi type below when its original type is the
outer cast. The generic sound/rigid definition collection may be the full
combined collection, so all existing ordinary iota, projection, stored equation,
quotient, and unindexed singleton computations remain available in the payload.

This is a local typed head-exposure bridge, not an embedding of arbitrary cast
steps into EtaCompute. In particular, a cast in function position may transport
between different function types; its argument typings cannot be discarded.
A nested cast payload need not itself be a type below merely because it is
well-formed. Extending the typed reconstruction through those cases and actual
indexed singleton programs remains the live direction. The original matched
lambda-domain comparison also remains unresolved. No claim of a smaller
sufficient PropFront obligation is made.

The combined target builds (280 dependency jobs). Five replay/head-recovery axiom
audits contain only propext, Classical.choice, and Quot.sound; no sorryAx occurs.
No executable changes. Full strengthening remains open and the goal stays active.

### Propositional extraction of data-slot equality witnesses

The preceding goal turn is classified as progress: three checked commits through
7a8aefc4 are present and the worktree was clean at this turn's start. The local
cast bridge does not apply directly to the existing singleton occurrence program.
That program fills data-slot telescope binders with Eq.refl and therefore already
requires endpoint alignment. Merely adding cast head replay would leave that
requirement in place.

The new direction retains transports and generates their proofs from the major.
`SingletonPropElimination.lean` factors closed propositional elimination for an
arbitrary body in the generic parameter/index/major context and its constructor
branch. `SingletonStepWitness.lean` proves every reconstruction-telescope domain
is a proposition. In constructor branches, proof slots return the field variable;
data slots return Eq.refl, justified there by uniqueness of the two typings of
the same literal field variable. Those branch equalities require no occurrence
alignment.

`SingletonStepExtraction.lean` packages these motives and branches as closed
`stepValue` functions. `stepValue_typed` covers every slot, including data slots,
and accepts arbitrary occurrence indices in its argument telescope. The future
occurrence program can call this function to obtain an equality proof rather than
inserting an unjustified reflexivity proof. This uses canonical Eq beyond its
role in confluence.

The target builds (170 jobs). Six axiom audits contain only propext,
Classical.choice, and Quot.sound, with no sorryAx. All changes are in metatheory.
Next: instantiate these functions along their own recursively generated witness
telescope, obtaining typed transported fields at arbitrary major occurrences.
Then relate the transported program to aligned singleton prefixes and examine a
uniform recursor equation. None of those later steps, or full strengthening, is
claimed yet.

### Arbitrary-occurrence transported fields and aligned comparison

`SingletonTransportedOccurrence.lean` recursively calls each closed witness
function with the parameters, arbitrary indices, major, and earlier witnesses.
`transportedWitnesses_typed` types the resulting list along the cast telescope
without assuming a constructor instance or any endpoint alignment. Instantiating
the symbolic cast fields at that list gives `transportedFields_typed`. The
constructor at those fields is typed at its own computed indices by
`transportedConstructor_typed`; its type is stated explicitly, without identifying
those indices with the major's original ones.

`ProofTelescopeIrrelevance.lean` proves that two typed instances of a dependent
proposition telescope induce definitionally equal substitutions over any
well-formed base context. At each binder, the previous substitution equality
aligns the two domain instances before proof irrelevance compares the arguments.
All singleton reconstruction domains satisfy this proposition-telescope invariant.
Consequently `SingletonTransportComparison.lean` proves the reconstructed fields
independent of the chosen telescope witnesses. `transportedFields_eq_occ` and
`transportedFields_eq_aligned` identify them with the existing aligned program
and with any supplied aligned constructor field instance.

This completes the proposed repair of field extraction typing. It does not remove
the result-index obligation. `SingletonIndexAlignmentBoundary.lean` checks this
precisely for Eq with an explicit rigid-family premise: Eq.refl A a has requested
type Eq A a b iff a and b are definitionally equal. Eq has no fields to repair,
so uniformly typed field extraction cannot alone produce a constructor at every
original major type. A whole-recursion replacement would need a further justified
transport/computation argument. Propositional equality to a transported program
would not suffice to install it as a definitional constant equation. That next
step remains a research question, not an assumed consequence of these lemmas.

The combined target builds (174 jobs). Audits of witness typing, field and
constructor typing, proof-telescope substitution, both aligned comparisons, and
the Eq boundary contain only propext, Classical.choice, and Quot.sound. There is
no sorryAx dependency and no executable change. The requested strengthening
proof, canonical-Eq counterexample, or strictly smaller sufficient irreducible
front is still unestablished; the goal remains active.

### Substitution of transported reconstruction

The previous goal turn is progress: commit 81a5501d and its predecessors are
present, pushed, and the initial worktree was clean. The next experiment is to
transport the reconstructed constructor between its own family proposition and
the requested one, using another propositional elimination from the major.

`SingletonTransportNaturality.lean` proves raw substitution of witness lists and
reconstructed fields. `substHat_subst` handles the casts and dependent field
substitutions; the witness functions are fixed because their closed typings
imply closed syntax. No occurrence typing is needed for this naturality result.
`SingletonOccurrenceContexts.lean` supplies the generic identity occurrence,
constructor occurrence, family proposition typing, and specialization of the
generic transported fields. The target builds (175 jobs); the naturality axiom
audit contains only propext, Classical.choice, and Quot.sound, or subsets.

### Reconstruction at the original family by propositional transport

`SingletonFamilyTransport.lean` completes the proposed family-transport test.
`transportedFamily_at_constructor_eq` instantiates the existing symbolic
constructor-branch cast computation at the new witness list, then transports the
closed constructor-family typing along the resulting equal field substitution.
It establishes actual definitional family conversion in the constructor branch.
No global field-slot length condition is needed: the proof uses `tel_branch`
only at valid field positions, rather than assuming alignment at unused slots.

`familyWitness_typed` uses this branch to extract an Eq proof between the
reconstructed family's proposition and the original family's proposition.
`familyWitness_at_typed` specializes it to arbitrary well-typed occurrence
indices. The outer cast is at universe zero: its payload is the reconstructed
constructor proof, and its target is the original major's proposition.
`castedConstructor_typed` supplies this typing without alignment assumptions.
Proof irrelevance then proves `transported_singleton_eta`: every major is
definitionally equal to its casted reconstructed constructor at the original
family. Thus the former result-index gap in *typing a reconstructed proof* is
closed when the outer cast is retained.

The computational distinction remains exact.
`bare_constructor_iff_family_conversion` proves that equality of the major to
the bare reconstructed constructor is equivalent to definitional conversion of
the reconstructed and original family propositions. The forward implication
uses typing uniqueness; the reverse uses proof irrelevance after conversion.
The newly extracted propositional equality cannot simply replace this condition.
In particular, this work supplies neither a bare constructor for ordinary iota
nor an unconditional closed equation replacing an indexed recursor. The next
live obligation is computation of indexed recursors through the retained family
cast, or a typed head-observation mechanism that accounts for that cast. The
full matched-lambda comparison remains open too.

The combined target builds (176 dependency jobs). Seven axiom audits, including
family witness typing, casted constructor typing, transported singleton eta, and
the exact bare-constructor boundary, contain only propext, Classical.choice,
and Quot.sound, or subsets. No sorryAx occurs and no executable changed. The
original strengthening proof, canonical-Eq counterexample, or strictly smaller
sufficient irreducible obligation is not established; the goal remains active.

### General canonical K replay from source typing

The preceding goal turn is progress: 9a3f03e0 and 2b91a49b are present and pushed,
and the worktree was initially clean. Testing computation through the retained
family cast requires distinguishing general equality elimination from the
special identity motive of a type cast.

`EqRecReplay.lean` recovers every argument typing of a canonical Eq.rec source:
its carrier, both endpoints, dependent motive, minor, and proof. Given endpoint
conversion, `eqRecApp_simAt` replaces the major by reflexivity using proof
irrelevance and invokes the actual registered iota rule. The equality is replayed
at every supplied source type, even when the motive depends on the proof.
`reflexive_eqRec_simAt` requires only source typing when the endpoints are
syntactically identical.

`CastCompute.eqRec` integrates this general K rule into the existing compatible
computation relation. Raw substitution preserves it; applying a lift retraction
recovers the source shape and repeated endpoint. Consequently the relation's
substitution, lift inversion, source-only replay, and descent theorems now cover
general dependent motives, in addition to the earlier identity-motive casts.
The combined build, including both existing cast head-exposure wrappers and the
family reconstruction target, succeeds (292 jobs). The replay/descent audits
contain only propext, Classical.choice, and Quot.sound, or subsets; no sorryAx.

### Common result typing cannot recover general Eq.rec endpoints

`EqRecResultBoundary.lean` checks the proposed extension of the special type-cast
argument. `constantEqMotive_typed` and `constantEqMotive_app` build and beta-reduce
a constant motive independently of endpoint alignment. `constant_eqRec_typed`
then types the complete recursor at its minor's type using any well-typed major
proof; it does not use definitional equality of the endpoints.

The test endpoints are Prop and (Prop -> Prop), both at Type. In the context
containing a variable proof of their propositional equality, the recursor with
constant Type motive and minor (Prop -> Prop) is itself a type at Type. The
context is well formed by canonical Eq typing. Nevertheless, existing head
separation proves that Prop and (Prop -> Prop) are not definitionally equal,
even in this context. `common_result_does_not_align` packages the context,
source and minor typings, and that nonequality.

Thus source/minor common typing cannot discharge the endpoint premise of
`eqRecApp_simAt` for arbitrary motives. This is a checked refutation of the
endpoint-alignment argument, not a nonequality theorem about the recursor and
its minor, and not a strengthening counterexample. The special cast argument
remains valid because its identity motive exposes the endpoints as the two
result types. The retained family cast in singleton reconstruction still needs
a computation argument that keeps track of indices or a different observation
invariant. General K descent alone cannot lower an ambient endpoint-conversion
premise, and eta can still create nonlinear matches.

The boundary is included in the 292-job combined build. Eight audits across the
new inversion/replay, extended computation, constant-motive boundary, and existing
cast head recovery have no sorryAx dependency. Only metatheory and the two
research logs changed. Full strengthening and every requested alternative final
deliverable remain unestablished; the goal stays active.

### Arbitrary equality-constructor exposure has the same endpoint boundary

The previous checkpoint consists of pushed commits c88f362c and 4ce20a72.
`EqConstructorBoundary.lean` closes a possible escape from the fixed-constructor
boundary: changing the reconstructed constructor's carrier, universe, or endpoint.

First, `HasCanonicalEq.rigid` derives Eq rigidity from its registered canonical
iota pattern and constructor-result provenance. No independent rigidity premise
is needed. `eqReflApp_typings` recovers the constructor's supplied argument
typings, and `eqRefl_typed_endpoint_conversion` compares its own reflexive result
with an arbitrary requested equality type. Rigid family injectivity then forces
conversion of the requested endpoints.

`eqProof_constructor_iff` gives the exact characterization: a typed equality
proof converts to some reflexivity constructor if and only if its endpoints
convert. Full subject reduction gives `eqProof_no_constructor_reduction`, which
covers every finite actual full reduction, including generated prefixes,
projections, and both eta expansions. The constant-motive test specializes both
results to every proof of its equality; transported reconstructions are included
whenever they have that same type.

This refutes constructor exposure as a way to bypass nonconvertible endpoints.
It does not show that the enclosing recursor cannot convert to its minor by
some other argument, nor does it refute strengthening. Indexed-prefix replay
and matched-lambda comparison remain open.

The target builds with 248 dependency jobs. Seven axiom audits contain only
propext, Classical.choice, and Quot.sound; no sorryAx appears. No executable
changed. The requested final deliverable is still unresolved and the goal
remains active.

### Remove metadata and typing side assumptions from the stored-model test

`CanonicalEqRegistry.lean` derives the registry entry of Eq.rec directly from
its canonical iota pattern, including its major offset of five. Independently,
`RecursorRegistered.eqRec_numIndices` compares the installed recursor type with
the generated result spine: canonical Eq's motive has two arguments, so every
registration at that name has exactly one index. This also proves that no added
unindexed singleton unfolding can have Eq.rec as its head.

`canonical_cast_boundary_registered` removes the registration and offset
premises from the previous stored-model boundary. `canonical_cast_counterexample`
constructs all remaining context and argument typings: a free proof of reflexive
type equality casts a Pi type to itself. Canonical K gives the actual typed
equation, while the stored-equation/guarded-iota/projection/eta head model cannot
expose its Pi. Thus this model's inadequacy holds in every well-formed
canonical-Eq environment without additional existence assumptions.

This still concerns the stored-equation collection. Excluding unindexed
singleton unfoldings does not exclude the structure-unfolding extension; no
refutation of the full `IndexedPrefixReplay` hypothesis is claimed here. Neither
the strengthening theorem nor an alternative requested final deliverable has
been established.

The target builds with 278 dependency jobs. Five axiom audits contain no
sorryAx, only propext, Quot.sound, and (where used) Classical.choice. Commit
5eae047a contains the preceding constructor-exposure boundary and is pushed.
Two independently appearing workspace changes, SingletonIndexAlignmentBoundary
and UnalignedEqMajor, are left untouched and excluded from this commit.

### The full current indexed-prefix replay premise is false

`CanonicalEqHeadBoundary.lean` completes the previously missing analysis of the
closed-equation additions. Constructor provenance identifies any projection
constructor of Eq with Eq.refl. Its two-argument telescope, compared with the
three-argument family arity, forces nonzero projection indices. Separately,
reading the sixth domain of the installed Eq.rec telescope identifies its
registered major family as Eq. Therefore the closed structure equations, which
require an unindexed family, cannot unfold Eq.rec. Combined with the stored-rule,
Quot-name, and singleton-index exclusions, `eqRec_no_full_unfold` covers the
entire `FullHead.definitions` collection.

`canonical_cast_full_boundary` now excludes every Pi exposure of a reflexive
cast through a free proof major in the complete current mixed head model.
The actual typed K equation still holds. To connect this semantic equation to
that exact proposed simulation premise, `normal_pi_right` checks normal-comparison
head shape and `defeq_pi_full_exposure` applies canonical confluence and Pi
reduction inversion. It obtains an actual finite full reduction from the cast
to some Pi, without an explicit singleton-prefix generation calculation.

If `FullHead.IndexedPrefixReplay` held, the existing full-reduction bridge would
simulate that path in the model, contradicting the observation obstruction.
`not_indexedPrefixReplay` proves its negation in every well-formed canonical-Eq
environment, with no additional registration, typing, or existence premises.
The FullHeadExposure documentation and idea ledger now mark this premise as
refuted. Its conditional theorems remain valid, but cannot establish full head
recovery for the present model.

This rejects one model obligation, not strengthening or a smaller sufficient
front. A model with a new indexed computation mechanism remains live; the
existing nonlinear K replay provides one ingredient, while its eta/observation
adequacy and matched-lambda comparison remain unresolved. The executable is
unchanged. Six axiom audits, including the final refutation and its confluence
dependency, contain no sorryAx.
The final target build succeeds with 299 dependency jobs. The independently
appearing CanonicalEqHeadMetadata file is also left untouched, together with
the two earlier unrelated workspace changes.

### Consolidate canonical Eq rigidity

Canonical rigidity now lives in SingletonIndexAlignmentBoundary, allowing
`eqRefl_typed_iff_endpoint_eq` to drop its separate rigidity premise.
EqConstructorBoundary reuses the same theorem. The parallel metadata and
unaligned-major scratch files were redundant with the now-committed registry
and arbitrary-constructor boundary, and have been removed. The complete head
boundary target builds; audits of rigidity, the simplified iff, and the full
model refutation have no sorryAx. The strengthening goal remains open.

### Source typing does not repair beta/K eta removal

`CastEtaBoundary.Compute` now includes general syntactically reflexive Eq.rec
computation. The existing certified-normality proof and untyped cast test remain
valid for this larger fragment. `EqRecEtaBoundary` supplies a typed test: a
neutral function and its eta expansion are the endpoints, a constant motive
returns Type, and the minor is a Pi type. A free equality assumption supplies the
major in a well-formed context. All typings follow from canonical Eq.

Expanding the short endpoint enables K without changing the motive. Without eta,
the source is beta/K-normal and every path is the identity. Thus source typing
alone cannot restore this raw Pi-exposure theorem, even for type-valued sources.
The counterexample applies to the specified beta/K fragment, not every rule of
CastCompute or FullReduction. `source_eq_minor` also checks the positive typed
repair using endpoint eta, so this is not a strengthening counterexample.

The target builds with 243 dependency jobs. Four audits, including both old and
new eta-removal failures, contain no sorryAx. No executable changed. A typed
alignment mechanism, or a raw model with additional adequate matching, is still
needed; the requested strengthening deliverable remains unresolved.

### Recursive typed endpoint certificates for K computation

The previous turn made progress by refuting raw beta/K eta removal even with
source typing. This turn follows its positive repair: preserve a finite typed
comparison certificate instead of requiring literal equality after eta removal.

`GuardedKComputation.lean` defines a compatible computation relation with an
explicit endpoint-matching predicate. It contains every CastCompute path and
adds general Eq.rec contraction guarded by that predicate. Its syntactic
`lift_shape` theorem shows all intermediate and final terms remain lifts.
`simAt_below` then replays the entire compatible path below an arbitrary binder
insertion if common-typed matching certificates descend. In the K case, source
inversion supplies endpoint typings; in transitivity, the first replay supplies
the intermediate typing. Applications, lambda domains/bodies, Pi domains/bodies,
and projections are all covered. Output typing below is never postulated.

`CertifiedKComputation.lean` supplies an explicit family of certificates that
satisfies this premise. Depth zero is HybridNormal. At each successor depth,
both endpoints may compute using previous-depth certificates before their final
HybridNormal comparison. Induction on depth replays those two computations below
and invokes hybrid descent at their now-typed results. Thus finite nesting of
K guards, beta/delta/iota/projection computations, and eta-aware endpoint matching
is supported; the depth does not bound ordinary path length. Certificates and
computations also survive finite binder insertion.

`CertifiedKExamples.lean` checks the earlier typed eta counterexample with a
depth-zero guard. That source itself becomes an endpoint of an enclosing,
well-typed Eq.rec, which computes with a depth-one certificate. Its proof is
constructed from the checked inner equation; no additional endpoint-alignment
hypothesis is supplied. The nested path weakens through arbitrary binder
insertions.

The target builds with 249 dependency jobs. Six audits, including general replay,
recursive certificate descent, Pi exposure, and the typed nested example, have
no sorryAx. The executable is unchanged. Full indexed-prefix coverage and hybrid
comparison completeness are not proved, and this is not a smaller sufficient
obligation than PropFront. The strengthening goal remains active. An independently
appearing HeterogeneousProofSubstitution file was left untouched.

### Delayed proof arguments: independently typed common-template instances

The previous goal turn was progress: 4367bfc5 is present and pushed, with the
full-model refutation checked. This turn revisits route A's delayed-substitution
proposal. The persistent beta-pair obstruction remains; the new result addresses
the benign same-template pairs created when proof arguments are substituted.

`HeterogeneousProofSubstitution.lean` defines `ProofSubstRel`: substitution
entries may agree literally, have a recursive domain certificate, or both be
proofs, without any prior alignment of their propositions. The literal case
permits arbitrary unused entries. The relation lifts under binders.

`subst_certificate_nonproof` compares independently typed non-proof instances
of a raw template, producing another DomainNormal certificate.
`subst_certificate_common` includes proof results when their types align below.
The open template need not be typed in the smaller context. In an application,
the function comparison aligns its domain, which supplies the proof-irrelevance
premise for proof arguments. Lambda annotations are recursively compared and
retained. This avoids assuming a common proposition for every substitution
entry and preserves the comparison invariant rather than only declarative equality.

`inst_proofs_certificate` specializes to one proof variable, and
`beta_proofs_same_template` uses beta subject reduction to obtain the body-instance
typings. It constructs a bidirectional beta join even when the two original
lambda domains differ. This closes the shared-template proof-argument case;
there is no claim of arbitrary beta-join completeness or lambda-argument repair.
The next step is to transport the proofness bridge through genuinely suspended
comparisons, using typed substitutions in the ambient context.

The target builds with 217 dependency jobs. Four axiom audits contain only
propext, Classical.choice, and Quot.sound, with no sorryAx. No executable changed,
and the original strengthening deliverable remains unresolved. Independent
workspace commits through d900dc31 were preserved without modification.

### Typed substitution preserves recursive K certificates

`CertifiedKSubstitution.lean` closes the homogeneous substitution law needed to
use these computations beneath beta reduction. The generic guarded relation
inherits substitution when its matching certificates do. Source typing supplies
valid contexts under lambdas and Pis; replay supplies the intermediate typing in
a transitive path. Consequently no additional typing premises for interior nodes
are necessary.

The concrete KCertificate family satisfies that matching property by induction
on depth. At the leaves, HybridNormal.instN handles lambda arguments and the
redexes they create. At successor depth, the two certified endpoint computations
are substituted recursively. Certificate depth is unchanged, while the hidden
hybrid comparison index may increase. This is homogeneous typed substitution;
no claim of arbitrary raw or heterogeneous substitution is made.

The target builds with 247 dependency jobs. Four audits have no sorryAx, only
propext, Classical.choice and Quot.sound. The requested full strengthening result,
a canonical-Eq counterexample, or a strictly smaller sufficient front has still
not been established. The goal stays active.

### Ambient substitution squares for delayed comparisons

`SuspendedSubstitution.lean` supplies the previously missing proofness bridge:
a typed substitution from the original comparison context into an ambient target
commutes with the raw template substitution and the actual weakening below.
`SubstLiftSquare.proof_reflect` then reflects proofness for any independently
typed smaller instance. No typing for an open smaller template is assumed.

The square extends under a chosen lower domain using only its ambient alignment,
and can add an ambient-only binder. `DomainNormal.suspended_reflect` descends
recursive domain certificates through two such squares and a ProofSubstRel.
`suspended_proof_inst` pushes a pair of proof arguments onto these delayed
substitutions, without requiring their propositions to agree below.
`suspended_eta_left` handles one-sided eta with a recursively certified body;
type uniqueness aligns the short function's ambient domain with the lower choice.

The target builds with 218 dependency jobs. Six axiom audits contain only
propext, Classical.choice and Quot.sound, with no sorryAx. The executable is
unchanged. Full bidirectional suspension descent, including eta on both sides,
and arbitrary lambda-argument repair remain open. This is progress on the
existing delayed-substitution route, not yet a sufficient smaller front.
The independently appearing CertifiedKApplication file was left untouched.

### Application of computational certificates through displayed beta redexes

The previous goal turn was progress: recursive certificate replay and typed
substitution are committed and pushed. The current application test preserves
the distinction between common-type hybrid comparisons and the independent
function comparisons needed by direct application congruence.

`CertifiedKApplication.lean` proves `HybridNormal.apply_domain_arg`. When its
function comparison displays lambdas, it beta-contracts those applications and
uses heterogeneous substitution of domain-certified arguments in the body
comparison. Eta cases instantiate the same body certificates. Other function
shapes use direct congruence; proof-valued functions use proof irrelevance.
There is no normalization of recursively unfolding terms.

`KCertificate.apply_domain_arg` first replays the two function computations to
recover their common Pi typing and then applies this local rule. Prepending
those computations preserves the same positive certificate depth. The extension
`apply_computed_domain_args` permits arguments to compute through nested K steps
before their DomainNormal comparison; replay supplies their result typings.
`apply_same_arg` requires only the shared argument's typing, even for a lambda.

The target builds with 248 dependency jobs. Four axiom audits have no sorryAx.
The remaining different-lambda-argument case still has only a hybrid comparison,
not a domain certificate. Thus these application laws are not full application
closure or completeness, and no requested final strengthening deliverable is
claimed. No executable changed; the goal remains active.

### Separate ambient realizations close suspended eta descent

`SuspendedBidirectional.lean` generalizes the two-square invariant: the left and
right instances may use different ambient contexts and weakenings. This permits
an arbitrary typed source prefix to be realized independently on each side.
`SubstLiftSquare.extend` constructs those realizations. The smaller context and
its substitution stay fixed. Sort uniqueness in each target, via `sort_level`
and `suspended_sort_types`, supplies the common-mode universe comparisons.

`BiNormal.suspended_reflect` now preserves every mode-indexed constructor,
including common lambdas and all three eta cases. Eta on both sides uses source
spine inversion, then independently extends both ambient realizations over the
resulting source-only prefix. It requires no Pi exposure below and no open
smaller typing for the template. The conclusion is a BiNormal certificate,
not merely declarative equality.

`BiNormal.suspended_proof_inst` extends the result over another proof-argument
pair. `suspended_beta_proofs` combines it with beta subject reduction for distinct
bodies and arbitrary lower lambda annotations. The proofs can inhabit different
propositions below, provided their lifted ambient instances have the source
binder types. Arbitrary lambda-argument repair and completeness remain open.
This is not yet one of the requested final deliverables.

The target builds with 219 dependency jobs; six axiom audits contain only
propext, Classical.choice and Quot.sound. The executable is unchanged. Independent
workspace work through 3cb66fee and the PureBodyComputation file was preserved.

### Pure computational bodies retain beta behavior under every K guard

The previous turn made progress on application of recursive certificates. This
turn tests whether strengthening the matching predicate could also supply the
body-eta repair of the old recursive-loop obstruction.

`PureBodyComputation.lean` allows arbitrary expressions and computation in lambda
annotations, but requires body nodes to be variables, applications, or lambdas.
Annotation erasure commutes with binder insertion and substitution. Every closed
constant, projection, pattern, syntactic-K, and guarded-K computational path
preserves the body grammar and erases to a finite ordinary beta path. Constant
patterns cannot match these bodies; K cannot introduce a constant-headed body
redex. The final theorem works for any matching predicate, not only finite-depth
certificates, and any declaration collection, without a soundness premise.

`CertifiedKLoopBoundary.lean` applies the invariant to the recursive ordinary
loop: its erased body is beta-fixed, so all guarded computations retain exactly
that body. Its known eta repair has a different erased body. The canonical
recursive extension supplies typings and an actual finite FullReduction to that
repair, while every GuardedKCompute predicate and collection misses that target.
This is an exact-repair obstruction, not a proof that no different final hybrid
join exists, and not a strengthening counterexample.

The target builds with 265 dependency jobs. Five axiom audits have no sorryAx.
The next mechanism to test is body eta with function-type synthesis certificates
that reconstruct the chosen Pi type below; arbitrary ambient typing annotations
remain insufficient. No executable changed, and the original goal remains open.
The independently appearing suspended/heterogeneous-substitution files were
left untouched.

### Opaque lower equalities in suspended comparisons

`HeterogeneousSubstitutionEquality.lean` separates preserving a comparison
certificate from preserving its declarative consequence. DefEqProofSubstRel
allows arbitrary already-proved lower equalities, as well as unrelated proof
pairs and literally identical unused entries. Structural comparison of two
independently typed instances of a shared raw template yields lower equality;
the raw template still needs no open smaller-context typing.

`BiNormal.suspended_defeq` extends this to distinct source templates with a
mode-indexed certificate. The independent ambient contexts, sort uniqueness,
and eta-prefix extension from the previous result still apply. Substituted
arguments are used as opaque equality leaves, so their lambda domains need
not acquire new recursive certificates. `suspended_beta_eq` packages contraction
of distinct bodies with already-convertible arguments of any syntactic form.

The qualifier is essential: the argument conversion must already hold below.
This does not derive equality for independently typed lambda arguments whose
types have not aligned. Nor does the equality conclusion claim unrestricted
BiNormal substitution closure, which the existing boundary refutes. Producing
adequate source comparisons and resolving the original matched-lambda pair
remain open; no final strengthening deliverable is claimed.

The target builds with 220 dependency jobs. Five axiom audits contain only
propext, Classical.choice and Quot.sound, with no sorryAx. No executable changed.
Independent workspace commits through 64bcd094 were preserved. The goal remains
active.

### Compatible body eta with source-typed function-type recovery

The preceding turn made checked progress by showing that stronger K guards cannot
supply the recursive loop's body eta. This turn constructs a distinct mechanism
for the missing step, without permitting arbitrary ambient eta annotations.

`TypeRecovery.lean` records a finite reconstruction of a particular type from
variables, constants, sorts, lambdas, applications, Pis, and certified computation
on an already recovered type. Its replay premise is only source well-formedness.
For application, recovering the function's Pi type and using ordinary typing
uniqueness supplies the argument typing; there is no separate argument-conversion
hypothesis. Lambda domains come from source syntax. Pi universe choices descend
by sort uniqueness, which does not require equality strengthening.

`TypeRecovery.descend` reconstructs both the entire output type syntax and its
typing below arbitrary binder insertion. The relation also weakens. The present
syntax has no projection-recovery constructor, and makes no claim to reproduce
every arbitrary declarative typing.

`RecoveredEtaComputation.lean` adds eta steps whose Pi typings carry those recovery
certificates to the existing certified K computation. Its compatible closure
includes applications, domains and bodies of lambdas/Pis, projections, and finite
transitivity. `descend` produces an exact lower result and equality at the original
source type. In an eta step, it reconstructs the chosen domain below instead of
assuming the expanded result was typed there. Intermediate typings follow from
replay. Pi exposure and weakening are also checked.

`RecoveredEtaLoop.lean` recovers the recursive loop body's function type by a
variable lookup, one stored delta step at D, and application. Two compatible eta
expansions give exactly the earlier repair. The canonical environment test pairs
this new computation and its replayed equality with the old theorem excluding
that target under every guarded-K matching predicate. Conversely,
`captured_eta_not_recovered` excludes the known ambient eta step whose domain
captures the removed binder. Thus arbitrary exact-target simulation remains
impossible; general coverage must choose scoped repairs rather than copy every
ambient eta annotation.

The final target builds with 288 dependency jobs. Six final axiom audits, plus
the earlier soundness/Pi-recovery audits, contain no sorryAx. Projection recovery,
recursive staging with these new eta computations, and full comparison/indexed
prefix coverage remain open. No executable changed, and no requested final
strengthening deliverable is claimed. Independent suspended-substitution files
were preserved without modification; the goal remains active.

### Computational joins and a checked conditional-entry obstruction

The previous goal turn was progress: its three commits, ending at 1c618b20,
are present and pushed. This turn first extends the suspension invariant over
concrete computational joins. `SuspendedCastJoin.lean` combines CastCompute's
scope inversion and raw substitution with typed replay and the preceding
bidirectional reflection theorem. Reduct typings below are derived, not supplied.
Proof substitutions preserve a CastBiJoin certificate; arbitrary known lower
equalities give declarative equality. This includes the current sound closed
pattern equations and syntactic K, without asserting full reduction coverage.

The central lambda-argument residue suggests weakening entry equality to
agreement only when lower types align. `ConditionalSubstitutionBoundary.lean`
refutes that proposal concretely. Let D = Prop → Prop and E = D → Prop.
The left argument is λP : Prop. P : D; the right is λf : D. (∀P : Prop, P) : E.
The two functions are λx : D. Prop and λy : E. D. Their applications both have
sort 1, but beta-reduce to Prop and D, which sort/Pi disjointness separates.

A source context has a hidden variable T : sort 1, a function T → sort 1, and
an argument of type T. Its application has a reflexive common-mode BiNormal
certificate. The two typed ambient substitutions realize T as D and E. The
raw template renaming skips T. Both resulting squares commute and are fully
typed. For each used substitution entry, having convertible lower types is
impossible by uniqueness and Pi inversion, so CommonEntryRel holds. Unused
entries agree literally. `common_entry_descent_failure` packages the complete
counterexample. It works for every Params environment and therefore also under
canonical Eq. It is not a strengthening counterexample: the hidden source type
is instantiated differently. It rules out this specific way of avoiding the
unconditional argument-equality premise, even when both arguments are lambdas
and the whole result types agree.

The two targets build with 250 and 221 dependency jobs. Five axiom audits have
only propext, Classical.choice and Quot.sound, with no sorryAx. No executable
changed. The original strengthening result and a strictly smaller sufficient
obligation remain unproved; the goal stays active.

### Projection recovery completes expression-constructor coverage

`ProjectionTypeRecovery.lean` reconstructs a well-formed projection's typing
from a recovered type of its major, provided that type is the registered family
applied to arguments and the field-selection query succeeds. The original source
typing supplies its own parameters, source major, field type and elimination
guard. Typing uniqueness and rigid-family injectivity align the two family
applications. Field congruence then transports the original projection typing
to the recovered field type. Neither a new elimination guard nor the target
field's typing is assumed.

Field selection commutes with arbitrary binder insertion and reflects it using
a raw syntactic retraction. The new `TypeRecovery.proj` case combines this with
major-type descent. The complete field type and its projection typing are
reconstructed below. Recovery now covers every expression constructor, while
conversion remains restricted to its explicit certified computation relation.
In particular this closes projection as a syntactic gap, not the completeness
or indexed-computation gaps.

The RecoveredEtaLoop target builds with 289 dependency jobs, preserving both the
recursive-loop eta repair and the exclusion of captured ambient annotations.
Eight axiom audits cover the projection helper, field-selection reflection,
updated recovery weakening/soundness/descent, eta descent and both boundary
examples; none contains sorryAx. No executable changed. The final strengthening
result and a strictly smaller sufficient obligation remain open. Independent
worktree files were left untouched; the goal stays active.

### Recovered types unlock independent comparison of eta bodies

The previous goal turn was progress: 913d4ca6 is present and pushed. The new
`RecoveredComparison.lean` tests type recovery inside comparison rather than
requiring an eta computation first. A common-mode comparison can enter an
independent function slot if the two endpoint types are recovered and compared
recursively. A separate shared-type constructor omits the redundant type
comparison. Application nodes compose these certificates; BiNormal remains the
base relation. This does not claim arbitrary compatible or transitive closure.

The descent proof reconstructs each endpoint type below using TypeRecovery.
Those types are themselves typed below, so the independent type-comparison
child descends; its equality supplies the common-mode child premise. In the
shared-type case, injectivity of weakening identifies the two recovered types
syntactically. Soundness and weakening are also checked.

`RecoveredComparisonLoop.lean` recovers exactly the same Pi type for the ordinary
and eta-expanded diagonals. Their already available common-mode comparison can
therefore be used independently in the loop's function position. Both original
loops, and their proposition-valued applications, compare directly. The actual
canonical-Eq extension pairs this certificate with the old no-finite-beta-join
theorem. Thus it handles the existing guarded-loop obstruction without any root
normalization or preliminary change of either endpoint.

The target builds with 292 dependency jobs. Five axiom audits contain only
propext, Classical.choice and Quot.sound. General comparison/recovery completeness
and substitution of these new certificates remain open. No executable changed;
no final strengthening deliverable is claimed. Concurrent projection-recovery
edits were left untouched.

### Exact recovery substitution fails; output re-synthesis repairs the example

Before using recovered comparisons in the delayed-substitution invariant,
`RecoverySubstitutionBoundary.lean` tests the required recovery substitution law.
A variable declared at the captured Pi type has a lookup recovery certificate.
The lifted identity has an ordinary typing at exactly that declaration, so the
one-variable substitution and both source contexts are valid. Its substituted
output type still contains the unused binder inside a beta-redex domain.

`identity_captured_not_recovered` rules out every recovery certificate for that
exact output: TypeRecovery.descend would make the captured Pi syntax a lift.
`exact_recovery_substitution_failure` packages the well-formed source, typed
argument, context-instantiation witness, source certificate, and missing target
certificate. Thus ordinary typed substitution alone is insufficient for exact
recovery preservation, even homogeneously and under canonical Eq.

The test also checks the repair. `substituted_identity_plain_recovery` recovers
the ordinary Prop → Prop type, and `captured_pi_computes_plain` computes the old
captured output to it. This does not establish a general re-synthesis theorem.
The live choices are substitution with explicit argument-recovery evidence,
or re-synthesis of convertible output types after substitution. No claim is made
that RecoveredComparison itself lacks a different post-substitution certificate.

The target builds with 272 dependency jobs. Four axiom audits have no sorryAx;
only propext, Classical.choice and Quot.sound occur. The executable is unchanged,
and the strengthening goal stays active. Concurrent recovery-core and staged-eta
work was preserved without modification.

### Recovery-certified arguments preserve exact substitution

`CertifiedRecoverySubstitution.lean` proves the first live repair of the preceding
counterexample. `TypeRecovery.lookup_instN` replaces the substituted variable by
its supplied argument-recovery certificate and weakens it beneath subsequent
binders. `TypeRecovery.instN_of_recovery` extends this to every recovery rule,
including projection field types and conversion by certified K computation.
The source term's well-formedness supplies the intermediate recovered-type typing
used by computational substitution. The selected output type is preserved exactly.

`RecoveredComparison.instN_of_recovery` preserves both comparison modes with the
same argument hypothesis. It derives the endpoint typings required by recovery
substitution from the common-mode child. Arguments may be lambdas and may create
redexes; no normalization or syntactic restriction is imposed. This is homogeneous
substitution with explicit recovery at the argument's declared source type.
The captured-type counterexample shows why ordinary typing cannot replace that
premise. General re-synthesis, heterogeneous substitution, and comparison
completeness remain separate live obligations.

The substitution target builds with 255 dependency jobs; the combined loop,
boundary, and substitution targets build with 296. Three substitution axiom audits
contain only propext, Classical.choice and Quot.sound. The existing loop and
boundary results still build after the concurrent recovery-core refactor.
No executable changed and no final strengthening deliverable is claimed.

### Generic recovery and eta descent interfaces

The preceding goal turn was progress: projection recovery was committed and
pushed as 8ed15568. This turn factors its recovery proof into `TypeRecoveryCore`.
`ComputeDescent` requires exact target reconstruction and typed replay from a
lower source typing. `ComputeWeakening` requires finite binder insertion. These
are interfaces for concrete computation relations whose instances are proved;
neither supplies descent of arbitrary equality. `TypeRecoveryWith` retains all
syntax rules, with conversion parameterized by the computation. Its monotonicity,
weakening, soundness and descent are checked.

`RecoveredEtaCore` similarly parameterizes compatible recovered eta. The existing
`TypeRecovery` and `RecoveredEtaCompute` names specialize these constructions to
certified K computation, retaining their theorem interfaces and constructor
aliases. Existing loop, recovered-comparison and recovery-substitution boundary
modules build after the refactor. New staged clients and their audits are
recorded next. No executable changed.

### Finite eta/K interaction inside recovered types

`StagedEtaComputation` starts from certified K computation. Each successor stage
has compatible recovered eta over two base alternatives: the preceding stage,
and guarded K whose endpoints compute at the preceding stage to a hybrid normal
comparison. `ComputedComparison.descends` lowers both endpoint computations and
then their comparison, deriving the reduct typings from replay. `NextComputation`
therefore inherits exact typed descent. Induction proves descent and weakening
for every finite stage, along with stage monotonicity and staged type recovery.
There is no bound on ordinary reduction-path length and no normalization claim.

`StagedEtaLoop` exercises the interaction rather than just lifting old
certificates. At stage one the recursive omega term eta-computes to its repaired
endpoint. Stage two uses this pair as the guard of a type-valued constant-motive
Eq.rec whose minor is Prop → Prop. A variable declared at that cast type
recovers the Pi by stage-two computation, then eta-expands at stage three.
`canonical_staged_cast_eta` derives the entire context's well-formedness and
checks the expansion's equality at the original cast type in the actual
canonical-Eq-preserving recursive extension.

`StagedEtaScope` proves that every stage still excludes the captured eta target
and the captured identity type. Thus increasing the depth cannot repair exact
recovery substitution; general substitution must permit re-synthesized output
types or provide stronger argument certificates. It also cannot copy every
ambient eta annotation in a coverage theorem.

The staged loop and existing comparison/substitution-boundary targets build
with 298 dependency jobs; the uniform scope target builds with 276 jobs. Twelve
axiom audits cover the generic interfaces, all-stage descent and weakening,
staged recovery, the actual three-stage example, both scope exclusions, and old
consumer theorems. Only propext, Classical.choice and Quot.sound occur. No
executable changed. General indexed-prefix and comparison coverage, and the
final strengthening deliverable, remain open. The goal stays active.

### Substitution across computational bases

The previous goal turn made progress: generic recovery and finite eta/K staging
were committed and pushed as 3571316a and f1cfe4eb. This turn addresses substitution
through those stages. `ComputeSubstitutionTo` fixes an argument and its declared
type, allowing computation to move from one relation to another after typed
substitution. `RecoverySubstitutionCore` proves exact recovery and compatible eta
preservation when the argument recovers its declaration in the target base.
Lookup uses that certificate; conversion uses the computation transformation;
transitive eta paths use source replay to type their intermediate terms.

`GuardedKCompute.instN_to` likewise permits the endpoint comparison relation to
change. Its original same-relation substitution theorem is retained as a
specialization. The existing TypeRecovery lookup and substitution theorems now
specialize the generic proof, and RecoveredComparison substitution still builds.
No executable changed. The all-stage bound and its exact boundary are recorded
in the next entry.

### Additive-stage beta substitution and its exact-output boundary

`StagedRecoverySubstitution` proves the bound r+n: a stage-n computation survives
substitution of an argument whose declared type is recovered at stage r.
Induction transforms both alternatives of the next computational base. The K
alternative substitutes its endpoint computations and hybrid normal comparison;
the eta alternative maps argument recovery into the larger base before applying
the generic substitution theorem. Type recovery itself satisfies the same bound.
No finite-interaction depth is assumed sufficient for arbitrary typed arguments.

`StagedEtaCompute.beta_inst` prepends a displayed beta contraction to the
substituted body path. `StagedBetaLoop.loopCast_beta_eta` checks the nonzero-bound
case: the argument is a variable declared at the recursive cast type, recovered
at Prop → Prop using stage-two eta-dependent K. The body is a stage-one eta
expansion of an ordinary function variable. Substitution and beta give the exact
stage-three output, whose typed equality is replayed at Prop → Prop.

`StagedSubstitutionBoundary.staged_exact_substitution_failure` tests the possible
shortcut of dropping recovery while allowing any larger stage. A variable at a
captured Pi declaration has a stage-one eta certificate. The lifted identity is
a valid typed substitution argument. Its exact substituted target is the old
captured eta expansion, excluded by every stage's source-typed scope reflection.
Thus unbounded finite stage growth cannot give arbitrary exact typed
substitution. Choosing a different scoped output remains necessary for that
route; this is not a strengthening counterexample.

The combined old-substitution, staged-beta and boundary build succeeds with
302 dependency jobs. Ten axiom audits contain only propext, Classical.choice and
Quot.sound, with no sorryAx. Both new arguments and the original specialized
substitution theorems are covered. No executable changed. General comparison
coverage, indexed-prefix coverage and the final strengthening deliverable remain
open; the goal stays active. Independent worktree files were left untouched.

### Re-synthesis existence has exactly two local head obligations

The previous goal turn was progress: the three commits through 3d38bb54 are
present and pushed. This turn follows the remaining arbitrary-argument route
without assuming the refuted exact-output substitution property.

`RecoveryExistence.lean` defines RecoveryExists for recovery at some chosen
output, rather than at every supplied typing. Its RecoveryHeads structure has
two explicit unresolved clauses: recover a Pi for the function of a well-formed
application, given some recovery of that function; and recover a usable family
and selected field for the major of a well-formed projection, given some recovery
of that major. All other expression constructors synthesize directly from source
well-formedness.

The characterization is exact. Structural induction proves sufficiency;
`TypeRecoveryWith.app_inv` and `proj_inv` strip trailing output conversions to
prove necessity from recovery of the whole application/projection. Thus
`recoveryExists_iff_heads` neither assumes exact typing completeness nor hides
additional syntax cases. The application clause may choose a different Pi,
and the projection clause may choose different family parameters and levels.

`TypeRecoveryWith.resynthesize_instN` uses these clauses after ordinary typed
substitution, then uniqueness identifies the new output with the old substituted
type up to definitional equality. No argument-recovery certificate is required.
`RecoveryHeads.of_type_exposure` supplies a more operational sufficient condition:
compute an inferred type to some Pi or usable projection family. The original
Pi at the application is used only to establish the inferred-type equation by
uniqueness. These computational completeness premises are still unproved for
the staged model. This is a characterization of the re-synthesis gap, not a
claim that either premise alone suffices for full strengthening or is a strictly
smaller sufficient front.

The target builds with 243 dependency jobs. Five axiom audits have no sorryAx;
only propext, Classical.choice and Quot.sound occur. No executable changed.
Concurrent staged computation/substitution work was preserved without modification.
The original strengthening deliverable remains unresolved and the goal active.

### Projection recovery needs family exposure alone

`ProjectionRecoveryTotality.lean` proves that any family typing of the major
of a well-formed projection admits field selection. The original typing bounds
the field index; rigid-family injectivity fixes level and parameter counts; the
registered constructor telescope supplies the selected field. Combining this
with existing projection replay gives its typing at the recovered field.

`FamilyRecoveryExistence.lean` removes selection and registration witnesses from
the unresolved projection clause. Under ComputeDescent, recovery existence is
exactly equivalent to Pi recovery at applications and family recovery at
projections. Computational family exposure is likewise equivalent to the former
projection-exposure premise including successful selection. This discharges an
auxiliary requirement, but the head-exposure obligations remain unproved for the
staged computation, and this is not a smaller sufficient strengthening front.

The combined target builds successfully (245 dependency jobs). Five axiom audits
contain only propext, Classical.choice and Quot.sound. No executable changed;
the original strengthening sorry remains unresolved. Concurrent staged-prefix
work was left untouched. The goal remains active.

### Nonuniform finite recovery and closure of all eta/K stages

`FiniteRecovery.lean` takes the existential union of StagedEtaCompute stages at
a fixed original K-depth. ComputeDescent and ComputeWeakening survive this union.
`TypeRecoveryWith.finite_stage` proves compactness: every recovery certificate
whose computations individually choose finite stages can be collected into one
finite stage. Conversion takes a maximum; all other recovery constructors retain
the stage of their recovery premise. `finite_recovery_iff` records both directions.

The union admits compatible application, lambda, Pi and projection computation,
composition, eta from union-based recovery, and K guarded by union-based computed
comparisons. `finite_staged_fixedPoint` proves closure under the entire next-stage
operation, RecoveredEtaWith (NextComputation D ...). Thus no further finite
alternation of those same rules provides an additional capability beyond the
union. This statement does not assert coverage of arbitrary equality, eta
annotations, indexed prefixes, or computational heads.

The head-exposure premises can now be stated without requiring a global stage
bound. `finite_recovery_of_head_exposure` yields a stage and an output depending
on the typed expression. `resynthesize_finite_instN` then supplies a finite-stage
recovery at a type convertible to the original substituted output under arbitrary
typed substitution. It does not require recovery of the argument at its declared
type. The two exposure premises are explicit and still open; no unconditional
substitution result or strengthening front is claimed.

The combined build with the existing substitution boundary and recovered looping
comparison passes (304 dependency jobs). Seven further axiom audits contain no
sorryAx; only propext, Quot.sound and, in replay results, Classical.choice occur.
No executable changed, and concurrent prefix-computation files were untouched.
The original goal remains unresolved and active. The next question is coverage
of the finite union, particularly whether its computed-comparison guards need
the stronger recovered application comparisons already checked for looping terms.

### Recoverable telescope opening for indexed Eq prefixes

The previous goal turn made progress: c7dd0d52 and fc3f4256 are committed and
pushed. This turn inspected the indexed-prefix replay boundary. Generated prefix
syntax already reflects finite binder insertion in GeneratedScope; the hard
part is replaying occurrence-specific typing and alignment. The new work first
handles the canonical Eq telescope through staged eta and K.

`StagedPrefixComputation` proves that supplying a literal telescope preserves
recovery of its residual type. Recovery also opens the remaining telescope with
fresh variables. The corresponding eta computation costs one additional stage
regardless of the number of binders. A body computation can then be closed under
the displayed domains. No arbitrary ambient eta annotation is copied.

`eqRec_prefix` uses the canonical declaration, its syntactic supply calculation,
and the exact six opened arguments. A preceding-stage comparison of the two
opened endpoints supplies K inside the telescope. `EqRecPrefixComputation`
checks the concrete prefix before the major at an arbitrary carrier universe,
and the prefix before the endpoint when the carrier is a proposition. In the
latter case the fresh endpoint comparison follows from proof irrelevance.
These results require certificates for data endpoint alignment and do not claim
complete simulation of every registered singleton prefix program.

### A closed indexed unfolding at propositional carrier universes

`ClosedProofEqUnfolding` strengthens the concrete prefix result: if the carrier
universe w is equivalent to zero, the bare Eq.rec.{v,w} constant itself unfolds.
The fresh carrier variable has type Prop, so its two fresh inhabitants are
proof-irrelevant. Staged telescope opening followed by K produces the closed
six-binder value that returns the minor premise. `equation` proves this equality
at the original canonical recursor type in the empty context.

The new definition collection adjoins exactly these universe-restricted
indexed equations to any preceding collection. Its soundness follows by
weakening the closed proof. Its constructor rigidity follows from the canonical
Eq.rec iota pattern, which excludes that head from projection constructors.
The equation therefore works in both the staged computations and the earlier
constructor-sensitive head model. Every supplied argument arity inherits a raw
compatible unfolding to the closed value applied to those arguments.

The final target builds with 278 dependency jobs. Nine axiom audits cover
residual recovery, telescope opening, both concrete prefixes, the closed
equation, soundness and rigidity. No sorryAx occurs; only propext,
Classical.choice and Quot.sound are present. No executable changed. General
data-index alignment, complete registered singleton-prefix simulation and the
final strengthening deliverable remain open. The goal stays active. Independent
comparison-core edits were preserved without modification.

### Recovered application comparison can guard staged K

The previous turn made checked progress through 8b6b23bc. This turn factors the
existing application comparison into `RecoveredComparisonWith C` in
`RecoveredComparisonCore.lean`. Its descent needs only ComputeDescent C; its
weakening needs ComputeWeakening C. The old fixed-K relation is a specialization
with its public interface retained. The looping comparison and certified
substitution clients still build; the latter uses explicit specialization names
for recovered argument substitution after the refactor.

`ComparedEtaComputation.lean` allows computed endpoints to be compared with
recovered types at application nodes. Reconstructing both computed endpoints at
the source common type supplies the premises for generic comparison descent.
The new stage operation retains old hybrid guards and adds this guard. Every
finite stage descends and weakens; `of_staged` embeds the preceding staged model
without changing either depth bound. This does not prove strict enlargement
over the old union or coverage of arbitrary equality.

`ComparedEtaLoop.lean` checks a concrete use: the recursive loop pair directly
guards K at stage one, without endpoint computation. The resulting cast-type
recovery enables variable eta at stage two in an actual canonical-Eq-preserving
extension and a well-formed context. The preceding example used a stage-one eta
computation, stage-two K, and stage-three variable eta. The new certificate is
shorter, rather than evidence that the old finite union missed the equation.

The example builds with 300 dependency jobs; the original comparison/substitution
clients build with 297. Seven axiom audits contain no sorryAx, only propext,
Classical.choice and Quot.sound. Concurrent closed Eq-prefix work was preserved.
No executable changed. Head-exposure completeness and the original strengthening
deliverable remain open; the goal remains active.

### Substitution transforms recovered comparison guards

`ComparedRecoverySubstitution.lean` proves the generic comparison transformation
`RecoveredComparisonWith.instN_to`: a source computational base may change under
a fixed typed substitution, provided the argument recovers its declaration in
the target base. This transforms every recovered type inside independent and
common comparison modes. The original certified comparison substitution theorem
is now a specialization rather than a second induction.

The transformation extends through computed endpoints and both alternatives of
the new K guard. A simultaneous stage induction proves the same additive bound
as before: substituting an argument recovered at stage r into a stage-n path
produces a stage-(r+n) path. `beta_inst` carries a displayed beta contraction and
its body computation through that substitution. Recovery inside a K endpoint
comparison is included; it is not treated as a frozen ambient certificate.

The combined new-substitution, old-specialization, canonical-loop and finite-union
build passes with 308 dependency jobs. Five further axiom audits contain only
propext, Classical.choice and Quot.sound, with no sorryAx. The argument-recovery
premise is retained, so this does not evade the exact-output counterexample or
prove arbitrary re-synthesis. No executable changed; the strengthening goal stays
active. General head exposure and equality coverage remain the substantive gaps.

### Dependent proof indices remove singleton family transport

`ProofIndexReconstruction.lean` extends the propositional-carrier Eq observation
to arbitrary singleton layouts whose dependent index telescope consists of
propositions. Parameters remain arbitrary and may include data. The new suffix
substitution theorem compares typed index lists after the same parameter
instance, using previous proof equalities to align each subsequent domain.

`WF.specializedCtorIndices` substitutes a typed field instance through the
constructor's declared indices. Together these facts prove
`proof_indices_family_conversion`: the transported reconstruction's family is
definitionally the requested family. Thus `proof_indices_bare_constructor`
removes the outer family cast at an arbitrary typed major occurrence, without
assuming a preexisting aligned constructor instance.

The result also reaches the original generated occurrence. Componentwise index
equality and literal-slot typing align the transported fields with the requested
indices; `proof_indices_singleton_eta` invokes the checked original singleton
eta theorem with these derived premises. Its slot-bound premise is the ordinary
layout condition already proved for registered singletons. It assumes neither
aligned fields nor ambient index equations. The general data-index family
conversion obstruction and full registered-prefix replay remain open.

The targeted build passes with 177 dependency jobs. All nine new theorem axiom
audits contain only propext, Classical.choice and Quot.sound, with no sorryAx.
No executable changed. This is a checked fragment theorem, not a solution or a
new sufficient irreducible front for the strengthening goal, which stays active.

### Confluence supplies literal projection-family heads

The previous goal turn was checked progress through c1155c3b. This turn addresses
the declarative side of head exposure. `RigidFullExposure.lean` proves that a
sort-typed term equal to a rigid, sort-headed family application fully reduces
to a literal application of the same head. It normalizes eta expansions of the
family side with EtaSpine, transports that reduction through the confluence
join, and applies normal-comparison spine exposure. Sort typing excludes both
the proof-irrelevance and lambda alternatives. Levels and arguments may change.

`StructureReplay.family_head_telescope` extracts the normalized sort telescope
from projection metadata uniformly in the context. The earlier `family_arity`
now follows from that helper, preserving its statement without duplicating the
declaration-shape proof. This discharges the sort-headed premise for projection
families. `projection_type_full_exposure` therefore covers every inferred major
type at a well-formed projection, with no syntactic header assumption.

`RecoveryFullHeads.lean` identifies the remaining operational requirements:
repair a full Pi-exposing path to some certified Pi, and repair a full family
path at a projection to some certified family. Under canonical Eq these are
exactly equivalent to the previous exposure premises. Confluence supplies all
required full paths. Neither repair clause is proved for the staged models;
this is not asserted to be a smaller sufficient strengthening front.

Seven axiom audits have no sorryAx and contain only propext, Classical.choice
and Quot.sound. The combined existing-model/closed-Eq-unfolding build passed
with 354 dependency jobs at this checkpoint. No executable changed; concurrent
proof-index reconstruction work was preserved.

### Recovery is complete over full reduction; exact type-head descent is false

`RecoveryReplay.lean` separates ambient ComputeReplay from scoped ComputeDescent.
A direct induction replays TypeRecoveryWith using only the former. The local
head-exposure construction likewise requires ambient replay alone. This avoids
assuming strengthening merely to prove existence of a synthesized type.

`FullRecoveryExistence.lean` instantiates that weaker interface with actual full
reduction. Canonical confluence supplies Pi exposure; the new rigid-spine theorem
supplies family exposure, and field totality supplies selection. Consequently
`full_recovery_exists` is unconditional under canonical Eq and well-formedness.
`full_recovery_complete_up_to_conversion` returns a recovery certificate, its
actual typing, and equality of its output with any originally supplied type.
The output is chosen, not required to equal an arbitrary original annotation.

This establishes a complete synthesis baseline, but its computational base
cannot be used directly for strengthening. `not_computeDescent` refutes exact
scope reflection with the checked captured eta step. `FullHeadScopeBoundary`
sharpens this beyond function terms: a sort-typed Pi source fully reduces to a
Pi target whose domain captures the added binder inside a beta-erased argument.
`full_pi_target_scope_failure` proves this exact target is not a lift. Restricting
sources to types, or both endpoints to Pi heads, therefore does not rescue exact
replay. Head repair must be allowed to choose different annotations.

The final combined build passes with 358 dependency jobs. Eight additional axiom
audits cover ambient replay, full recovery completeness, and both scope failures;
none contains sorryAx (only propext, Classical.choice and Quot.sound). No
executable changed. Concurrent proof-index files were left untouched. The open
work is to repair the full-reduction recovery into a descending computational
model and establish sufficient comparison coverage. The original strengthening
sorry and requested final deliverable remain unresolved; the goal stays active.

### Closed registered unfoldings with dependent proof indices

`ProofIndexTelescope.lean` identifies the exact complete indexed recursor type
from registration, retaining the index binders inserted after motive and minor.
Its generic telescope provides both the equation prefix and the extraction's
parameter/index/major instance. `registered_reconstruction` now derives typed
generated fields and constructor eta at that generic occurrence under the
propositional-index premise. Two reusable alignment/field-typing lemmas were
factored out of the preceding reconstruction proof.

`ClosedProofIndexUnfolding.lean` applies the actual registered equation to those
generated fields. The fresh indices match the constructor's indices by dependent
proof irrelevance; `ConstSpineDefEq` transports the complete recursor application
before iota. Eta closes the checked body. The resulting value is identified
exactly with `singletonUnfolding ... []`, so `zero_equation` proves the real
zero-prefix program without assuming a caller-supplied unfolding check. This
extends the former zero-index result, while retaining arbitrary parameters and
arbitrary dependent proof-index telescopes.

The targeted build passes with 234 dependency jobs. Nine new/refactored theorem
axiom audits exclude sorryAx (only propext, Classical.choice and Quot.sound).
The executable is unchanged. General data indices and equality completeness are
still open; this is not claimed to settle the strengthening deliverable.

### Proof-index prefix replay and strengthening

`ProofIndexHeadComputation.lean` puts the new closed equations into the raw
computational model. The added declaration-level evidence is a proposition
index telescope after the parameters. Soundness follows from the checked closed
equation, and the registered iota pattern preserves constructor rigidity.
`Unfolds.of_unindexed` includes the previous unindexed class as the empty
proposition telescope.

`generated_compute` simulates the exact generated program at every supplied
arity, on arbitrary raw arguments, by a closed delta step followed by finite
beta specialization. `prefix_descend` therefore lowers the output from a lifted
source with only source typing below; `prefix_reflect_ofEnv` reflects an exact
pair of supplied endpoints with all definition assumptions discharged. The
mixed model's Pi exposure theorem also accepts the enriched definitions. No
ambient occurrence alignment certificate is strengthened in this argument.

The targeted build passes with 287 dependency jobs. Nine exported theorem axiom
audits exclude sorryAx and use only propext, Classical.choice and Quot.sound.
No executable changed. This closes proof-index prefix replay, but leaves
arbitrary data-index prefixes and general equality coverage open, so the active
strengthening goal is not marked complete.

### Repair literal family exposure through both eta forms

The previous turn was checked progress through 8bdc6592. The new full-recovery
baseline leaves an operational repair problem, not a missing declarative path.
This turn fills a gap in the existing observation model: it previously exported
Pi and sort exposure, but not projection-family exposure.

`FamilyHeadRepair.lean` uses its existing constructor tuple observations for
registered family heads. WF.projStatic proves that such a head is never any
projection constructor, so the tuple is admissible at all levels. Empty demands
on every argument record only the head, levels, and argument count. Backwards
observation through the mixed EtaCompute relation then gives PatternCompute to
the same family and levels with replacement arguments of the same count. Both
function eta and structure eta are covered; original eta annotations and family
arguments need not avoid a removed binder.

`family_exposure_below` combines this repair with syntactic lift inversion.
`major_type_below` reconstructs the lower family typing by replay from the major's
original typing. `projection_type_below` then derives field selection and the
projection's typing using the earlier totality theorem. The recovered parameters
are not required to equal the ambient path's parameters.

`FamilyTraceRecovery.lean` compiles mixed Pi/family traces into TypeRecoveryWith
for any computational base containing PatternCompute. Thus intermediate eta
annotations do not need their own recovery certificates when they can be removed
by this head-model argument. The family case uses only ambient computation
replay, source projection well-formedness, and the registered family. The model's
uncovered indexed singleton operations remain outside this theorem; no bridge
from arbitrary full paths is claimed.

The new target builds with 269 dependency jobs, and the combined full-recovery,
compared-eta and substitution build passes with 355 jobs. Eight axiom audits have
no sorryAx, only propext, Classical.choice and Quot.sound. No executable changed;
concurrent proof-index/singleton work was left untouched. The original goal stays
active, with full head repair and comparison coverage still open.

An annotation-erasure counterexample idea was also examined: loops at two
separately declared recursive fixed-point types have the same raw unannotated
shape. No non-convertibility proof was obtained. Finite beta stability alone
would not exclude full delta/eta joins, so this remains an unverified candidate,
not a rejection of annotation-erasure repair and not a strengthening counterexample.
