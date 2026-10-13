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
