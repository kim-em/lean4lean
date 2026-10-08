# Record eta and independent family requests

The proposed rule “constructor tags require a non-eta family; record demands
require a nonempty field input” resolves the field-free case. It does not by
itself resolve source coverage for records with fields. A record value must
not force an independently chosen family-parameter observation onto its
major's existing source observer.

## The concrete mismatch

Consider a relevant structure with a parameter unused by its field:

```lean
structure Phantom (α : Type) where
  value : Nat
```

In source context `α : Type, x : Phantom α`, the structure eta equation is

```text
Phantom.mk α (Phantom.value x) = x
```

An observer of the explicit constructor application can request a nonempty
Nat observation of its field and independently observe `α` at `sort true`.
The field observer of `Phantom.value x` can use a record demand on `x` whose
family request for `α` is empty: the declared field type is Nat, so its code
does not depend on `α`.

Write `R` for the whole constructor-side record demand and `Rj` for the
projection's major demand. The field requests can agree exactly while
`R.family.arguments` and `Rj.family.arguments` differ at the parameter input.
The available source leaves are then the separate observation of `α` and an
observation of `x` at `Rj`. They do not include an observation of `x` at `R`.
Padding, pruning, and existing function adapters do not strengthen the frozen
family descriptor inside a record atom.

A generic rule rebuilding `x` at `R` from those leaves would therefore need
additional source typing evidence. Storing a certificate for `Phantom α`
alone is insufficient: the current `Obs` judgment is not indexed by its
assigned source type, and the interpreter may be invoked using a different
original typing derivation for the same expression. A raw equality between
those assigned types must not be inferred from type uniqueness.

## What has been checked

This example describes the coverage obligation of the proposed constructor
record terminal and projection grammar; it is not a checked construction of
that future grammar or a new instantiated Phantom environment.

The structural facts used in the diagnosis are present in checked code:

- `RecordData` currently freezes a complete `FamilyData`, and intrinsic
  record typing requires equality with the supporting family descriptor.
- `Obs.record_of_adapter` in `AnchoredSourceRecordExtraction.lean` proves
  exact preservation of the record descriptor through normalized adapters
  and grade changes.
- `ProjectionRows` and `ProjectionPlan` retain exact original requests but
  allow an input to exceed the domain certificate's source dependencies.
- `FamilyCaptures.registeredLiteralRecord` constructs actual literal record
  semantics from declaration rows and selected fixed field admissions; it
  does not construct an observer of an arbitrary neutral major.
- `UnitMajorDemandObstruction.lean` checks original Strong formation of
  `motive major` and a current certificate retaining an arbitrary admitted
  major query. Runtime independence therefore does not erase type demands.
- `CodeCert.familyShape` and `FamilyCodeProfile.unitLike_empty` separately
  check the arbitrary-rank field-free gate under the proposed data policy.

## Candidate separation being investigated

A record value descriptor can retain the family name and exact field
requests, while parameter observations remain in its assigned type support.
A finite `recordJoin` on the same source major can then reuse several actual
record children, even if their type supports contain different family
requests. Interpretation uses the same original typing child for every
record child; the first child supplies a natural certificate of that assigned
type, and every selected field retains its original domain alignment.

The projection producer must still recover observations of all parameters
and earlier fields needed by the selected declared field type from the
original major transfer's type certificate and its existing record children.
No caller-supplied semantic observation callback can replace that work.

The target representation must also keep any selected family support in
externally retained syntax. Hiding an unrestricted family descriptor inside
a private record witness would reintroduce the proof-context dropping bug:
its parameter supports could mention proof slots absent from the record
value descriptor.

## Dependent projection remains a separate obligation

Removing family requests from the value descriptor is not sufficient if
intrinsic record typing checks only the family name. Consider

```lean
structure Box (α : Type) where
  value : α
```

In context `α : Type, x : Box α`, suppose the available valuation contains
only a record observation of `x` whose field requests the Nat.zero demand at
fixed support Nat. At the target seed `α = Nat, x = Box.mk Nat Nat.zero`, the
concrete field admission is valid. A family support for Box whose parameter
input is empty does not provide a source observation of `α` at Nat.

A projection transfer returning the zero demand of `Box.value x` must also
return a certificate of its original source type `α`. That certificate needs
an observation of the source variable `α`; observing the separate source
variable `x` does not provide that leaf. This is a coverage counterexample to
the proposed *name-only* record typing interface, not a constructed value of
a revised production grammar.

The checked projection-row producer currently gets its exact parameter
observers from `CodeCert.familyOrigins` at the record's frozen family
requests. Removing that link requires a replacement. Joining the type
certificates of all record children helps only if each child's certificate
already covers the parameter requests of its selected field-domain template.
A possible separation retains those field dependencies in the record value
while allowing independent, stronger parameter observations in its assigned
type certificate. Proving that dependency restriction is part of producer
coverage; it cannot be replaced by an arbitrary final caller premise.

`ProjectionParameterResourceObstruction.lean` checks the structural claim:
`CodeCert.variable_absent_empty` proves that every certificate of a source
variable has empty support when that variable's valuation slot is empty,
even if other source variables have resources. The proof includes every
current certificate wrapper, including family padding and guarded views.

## Exact template footprints can still contain surplus

Requiring the parameter channels to be exactly the footprint of a selected
field-domain certificate does not establish necessity. The literal template
`(fun _ : A => Sort v) parameter` admits both a certificate with no parameter
footprint and one retaining any actually admitted parameter query. The lambda
body has an empty binder footprint; the existing lambda rule permits its
input to contain more than that footprint, and application retains the
argument observer.

`CodeCert.fieldTemplate_surplus` in
`AnchoredProjectionDependencyObstruction.lean` checks these two certificates
at the same literal template and the same output support.
`VEnv.originalIgnoredParameterType` checks the template's
original Strong formation from an actual closed parameter-domain formation.
The first theorem is conditional on the actual domain certificate, lambda
guard, and admitted query; it does not assert that an arbitrary query is
admitted. These theorems show why exact certificate provenance alone cannot
rule out independent value dependencies.

One alternative is to store finite projection typing rows in the assigned
family **type** support. Record value typing would select a covering row for
each requested field, and source extraction would use the row retained by
the major child's actual returned type certificate. Each row needs its own
parameter requests, separate from unrelated ambient family observations.
The row's natural field support can remain distinct from the field request's
fixed admission support, as in `ProjectionDomainRow` today.

This alternative still needs a source producer. The family constant's
original header precedes its constructor declaration, so the existing
earlier-header interpretation cannot interpret the constructor's field
templates inside family transfer. Delaying that work until the actual
projection consumer is now checked in `AnchoredProjectionHeaderReplay`.
Actual source projection registration supplies the constructor lookup; the
existing staged header bank supplies its strictly earlier formation theorem.
That theorem moves the certificate from frozen anchors to actual arguments
before reification. The instantiated projection-field child alone could not
perform this earlier seed-transport step. Only the covered prefix is needed.

`AnchoredProjectionUnusedPrefix` separately checks that a prefix binder whose
needs are all empty requires no semantic domain interpretation. Its actual
row consumer retains raw formation and raw domain alignment, and supplies
empty certificates to the later fitted valuation directly.

The producer still needs either typing coverage across multiple family type
atoms or an explicit row-joining operation: joining record children with
different natural type supports cannot silently choose one child's rows for
all the fields. No production grammar or relation has been changed for this
candidate.

## Dependency trees do not remove the row-matching obligation

`AnchoredFieldDependencyObstruction.lean` checks a finite counterexample to
reusing the type rows of independently observed dependency trees. The
requested tree is `2:c → [1:a]`, with selector 1 a leaf. The available major
observers instead carry `2:c` and `1:a → [0:b]`. Every selector decreases
strictly, and every requested output query occurs in the available trees.
Both available trees have exact covering rows. Even adding the requested
root row for selector 2 does not give a cover for the requested tree: the
retained selector-1 row requires selector 0, which the requested subtree
omits.

`FieldDependencyTree.rootQueries_do_not_rebuild` proves this finite row
obstruction. `CodeCert.fieldDependency_surplus` supplies the corresponding
current-syntax phenomenon at an exact singleton input: the same literal
field-domain template has both a certificate observing one earlier field
and a certificate with no such footprint. The former footprint is
unavailable after deleting that earlier-field capability.

Thus rigid dependency trees do not automatically survive constructor eta,
and covariant pruning of their nodes does not automatically preserve their
type covers. This refutes the producer that merely reuses the child rows;
it does not rule out a separate checked producer that reconstructs suitable
rows for the requested tree. No revised source grammar is assumed by these
theorems.

## An outer type index does not identify the original children

Changing `Obs expression` to `Obs expression assignedType` would make the
detached projection packet's outer field type match its interpreter. It
would not make the packet's stored major type equal the major type of the
original projection derivation. Applications have the same problem even
without inductives.

`TypedObservationChildMismatch.lean` checks an example in the empty
environment and a well-formed source context. The same application has the
same literal result type while its function and argument can use either
`Prop` or the distinct domain `(fun T : Type => T) Prop`. Both internal
choices are justified by original `IsDefEqStrong` rules. The audited roots
use only `propext` and `Quot.sound`, with no admissions.

An outer conversion can be scheduled through its original type-equality
child in both directions. Structural application/projection still needs a
coherence theorem comparing the two internal typing derivations. Indexing
queries by entire original derivations moves that obligation to the middle
of transitivity and to substitution; it does not discharge it. A candidate
comparison of original proof closures is being examined at beta, where
reinterpreting a synthesized substitution derivation would invalidate the
proposed induction. No type-indexed grammar migration has been made.

The arithmetic part of a possible replacement schedule now checks in
`AnchoredOriginalClosureMeasure`. A finite Type-valued origin tree reserves
the sum of children, and literal beta additionally reserves the product of
body and argument weights. A closure's cost multiplies its origin weight by
one plus its captured environment's maximum cost. This permits lookup into
a larger original argument proof, ordinary child comparisons, and comparison
of the original instantiated-beta child with the body closure after
substitution. A phase orders coherence-to-fundamental calls at equal cost.
It does not define a weight by eliminating a Prop-valued Strong proof, and
does not justify generic beta evaluation through a substituted function.
Actual Strong reification, typed factor/reification and the complete callback
graph remain separate acceptance gates.

The next concrete gate is typed inverse substitution in the paired
application case. Current `CodeCert.seededApplicationInput` factors a
certificate of `B[a]` and feeds every cut observer of `a` to the original
argument theorem. With typed queries, such a cut can have a different
internal typing from the original argument child. The factor operation must
retain its original typing subview and compare it with that argument child
before replay. Each cut's origin must come from the original instantiated
result child or its captured source environment, with the comparison cost
bounded by the parent application. Merely asserting a cut-origin supplier
does not establish this gate.

Source proof closures and target realizations must remain distinct. A target
Pi-row anchor is an arbitrary admitted target term and needs no original
source proof origin. Source weakening under a binder changes a closure's
display, not its original proof. Finite synthetic endpoint views of original
beta/eta also need their own structural descent; charging every view node
the unchanged parent origin would leave an equal-cost coherence call.

## Original provenance and context-tail recursion

The actual factor traversal now checks in `AnchoredOriginalFactorTraversal`.
Every cut retains a real location in the supplied typing view; no cut-origin
supplier is assumed. `AnchoredOriginalFactorContext` records the precise
binder prefix and aligns the original argument by source weakening. The cut's
assigned type may depend on those binders and is not reflected or identified
with the argument's type. Its cost includes all original domain-formation
closures added along the location path.

`AnchoredOriginalPairedApplication.pairedApplication` checks the concrete
application consumer for type-code coherence. Given the smaller comparison
of function types, it factors the incoming result certificate, replays the
actual argument cuts, selects the returned Pi row, and reifies the other
instantiated codomain. The argument replay still uses the current unindexed
syntax; typed cut reindexing is a remaining obligation.

Charging only the original term proof and incoming observer cannot justify
variable lookup: that rule retrieves a new certificate from Fits. With
unrestricted stored typing metadata, a surplus ignored-beta-argument query
can ask for the same variable again through its type certificate. A fixed
maximum of such metadata does not remove this cycle. The candidate restriction
stores each lookup certificate in the earlier context tail where its domain
was formed, and only source-shifts it into the full context. The typed grammar
must preserve that tail provenance throughout its embedded original views.

`AnchoredOriginalDerivation` supplies finite data for every original Strong
rule and an actual context-formation spine with selectable tail locations.
The lookup comparison bound now uses that selected original tail closure.
Binder traversal requires product reserves for source domain formations;
zero-cost neutral placeholders alone were insufficient. Beta captures both
its original argument and original domain formation. These are checked local
bounds, not a complete simultaneous interpretation/coherence proof. Endpoint
exposure, typed query reindexing, and record-child inversion still have to
use them in the actual recursive call graph.

Both endpoints of all 19 Strong rules now expose in
`AnchoredOriginalEndpoints`, including explicit right-application and
right-lambda conversions and finite beta/eta syntax. Their weights are
bounded by the actual original tree reserves. `EndpointRef` also records
which side supplied a context formation; synthesizing a diagonal Strong
proof here would lose the original cost provenance. `AnchoredOriginalTailFits`
constructs finite tail certificates, retains their exact original context
locations, and reconstructs full-context entries only by source shifting.
Its explicit resources lie strictly after the lookup slot. The production
query grammar must additionally enforce those tail contexts on embedded
original references; the current unindexed certificates do not express that
future invariant by themselves.

The family-row proposal also needs a target-side restriction. A row cannot
hide actual prior-field admissions in type support when the record value
request does not observe those fields: generic support retagging cannot
recover unobserved behavior from a family code. A candidate instead uses
conditional, Pi-like rows, with `HasType R Q` requiring each selected row's
nonempty earlier-field demands to occur in the flat field requests `R`.
Independent parameter requests remain in `Q`. The earlier dependency-tree
counterexample does not refute rebuilding the exact incoming `Q` through
code coherence at a restricted valuation; it refutes merely reusing richer
child rows. Constructing these typed queries, restricted fitted prefixes,
and original earlier-projection producers remains the next semantic gate.

`CodeCert.factorInstOriginal` now starts directly from an actual original
endpoint reference. The existing traversal uses computed structural head
views, retains conversion paths and whole-cut assigned types, and preserves
the source/target environment distinction. There is no supplied TypingView
or numerical origin label in this entry point. `AnchoredOriginalTypeFormation`
additionally extracts assigned-type formation from all original rules, with
soundness and cost bounds; it never reifies a derived `isType'` proof.

For canonical projection replay, original parameter views may have inferred
domains different from the declaration's literal domains. The proposed
replay state must therefore construct concrete TARGET domain alignment for
each finite incoming query, rather than assume raw source typing at those
declared domains or retain a universal retyping supplier. A domain-only Pi
query through the original function spine is the next concrete alignment
candidate. The earlier `argumentDomainSpine`'s unrestricted `earlier` premise
cannot be used as the completed producer. Projection-prefix reserves also
need the actual captured original origins; selector-first induction or a
numeric reserve without that replay state does not establish termination.


## Exact domain-query closure

The domain-only Pi alignment candidate now has checked source and target
consumers. Input adapters expand a Pi domain with mapped hereditary minimal
supports from `Basis`. The previous certificate operations could not express
those restrictions for an arbitrary source variable. `CodeCert.focusMinimal`
now records the finite `Minimal` witness and intrinsic domination proof,
without changing the source expression or footprint. Its interpretation uses
the existing `TypeRelated.focusMinimal`, not an assumed source theorem.
Source renaming, substitution, factorization, universe transport, depth bounds,
Pi-row origins, and family origins all preserve this constructor.

`AnchoredOriginalPiDomainExtraction` reconstructs each exact domain through
all wrappers. Input maps focus to each actual basis member, map it, and union
the resulting source certificates; duplicated footprints remain available in
the same valuation. The focus case uses its actual hereditary domain choice,
not arbitrary restriction of Pi origins. No codomain row or domain inhabitant
is required. `CodeCoherence.piDomainAlignment` adds the concrete target
`TypeConversion`, recovered from the literal Pi display even at empty domain
support. The semantic path and exact source extractor have clean opaque-body
audits, and the migration passes the combined 471-job checkpoint.

The remaining producer must pull these queries backward through the actual
original function prefix to the literal earlier declaration header. At a
constant, this means retaining each original conversion and the right
constant endpoint's ambient header-level equality. Applications additionally
require actual argument/cut origins and their strictly bounded callbacks.
The old universal `earlier` supplier is still not a completed producer.


The application prefix now has a finite prepare/complete consumer. Its actual
result-child path is selected internally. The strengthened factor traversal
bounds every retained cut by that selected result closure; adding the original
argument closure remains strictly below the application, independently of the
size of the collected query. This closes the previous gap where both children
were bounded only by their shared root. Completion consumes one concrete
argument answer, and function continuation also has a strict original bound.

Typed acceptance must precede source reflection at a whole cut. The fact that
its expression is `a.lift depth` does not show its assigned type can be lowered:
that type may mention removed binders. The query must first be reindexed from
the retained cut closure to the original argument closure displayed under that
prefix, then reflected to the tail. An outer type index alone cannot guarantee
that all internal typing annotations reflect. The current unindexed cut
collector remains a checked consumer; it is not this typed reindex theorem.

## Current-syntax cut transport and original contexts

`WholeCutQuery.reindexReflect` now checks the local operation for the current
grammar. It consumes the actual cut's value answer and a comparison at that
answer's exact returned support, whose destination is the original argument
type displayed under the prefix. It converts the semantic answer and reflects
the returned observation and destination certificate. No independence or
reflection premise is imposed on the original cut type. Current observations
contain no embedded source-typing trees, so this step does not require a
hereditary observer rewrite. Any future typed packet extension must establish
its own preservation invariant; this proof does not supply one automatically.

`Located.contextDerivation` reconstructs the exact source context from actual
binder-domain references and proves that its captured closures equal the
environment used by the location's cost bound. `TailFits.reorigin` preserves
current certificates and semantic fields while selecting the other original
formation spine at the same literal context. Thus comparing binder bodies
need not charge the right body against the left domain's closure.
`EndpointDisplay` retains an unweakened original closure, its actual root and
location, equality of its reconstructed original context, and an explicit
source insertion. Displaying it under binders does not fabricate a new
original derivation or enlarge its captured cost.

Simultaneous factoring now retains every capture's actual cut and unreflected
query while recovering a declaration template in one pass. For original
projection rules, queried prior projections occur in the original field-type
premise. Structure eta also retains an original typing of its constructor
applied to all projections, giving actual argument endpoints. Unused prefix
fields still need raw target typing, but not manufactured source semantic
premises. This refines the earlier blanket requirement for synthesized
projection-prefix origins.

The application comparison must peel the left conversion route inward and
restore the right route outward. Both directions now have finite checked
consumers, including distinct source realizations and valuations. The full
comparison now constructs its queries from fixed original recursive
obligations. Factorization is relative to the selected application context,
including applications under binders. The enclosing mutual theorem remains
open.

## Concrete field requests must retain their anchors

Flattening record values to selector/value-profile pairs would discard
information required by dependent rows. For a record containing a type `T`
and a value of `T`, observing `T` at `sort true` does not establish equality
with a row anchored at Nat or at Bool. The candidate flat value requests must
therefore keep explicit request anchors and supports; independent full family
queries remain separate in the assigned type support.

`RequestAdmission.retagField` changes one concrete field request using a
finite input adapter, a semantic domain chain, and the new request's actual
seed admission. The constructor's application frame supplies that seed.
Finite `FieldRequestRows` can also coalesce different old requests by their
individual output atoms. The empty-input case explicitly uses the original
raw pair equality. These are target consumers, not a proof of source record
coverage or authorization to migrate the production grammar yet.

The subsequent isolated source pilot reconstructs actual projection heads
from retained whole cuts, preserves field-type alignment through original
`projDF` with changing majors, and reindexes it through the actual
`DisplayCoherenceAnswer`. Typed `ProjectionObs` keeps that metadata through
union, views, grade changes and whole-query reflection. Its seeded frame
constructs the guard from actual fixed-child fundamental answers. This
cannot be erased into current production `Obs`, whose grammar has no
projection constructor. General constructor/eta output coverage and
hereditary traversal for the enlarged grammar remain the acceptance gate.
