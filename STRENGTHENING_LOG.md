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
