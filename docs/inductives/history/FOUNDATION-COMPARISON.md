# Historical foundation investigations

This chronological research diary preserves attempted constructions and their
obstructions. Its hypotheses, status reports, and proposed next steps describe
the time of each entry; they are not current instructions or an endorsement
of the latest architecture. [HANDOFF.md](../../HANDOFF.md) is the single current
account and plan. Consult this diary only to investigate a specific argument,
and verify its claims against the source and focused counterexamples.

## Directed comparison and delayed substitutions

The constructor review found a plausible treatment of three local cases:
beta's substitution entry comes from an original argument child; transitivity
can retain the shared frontier `{H2, H1, T}`; dependent binder lifting relates
`bvar 0` to itself despite its type cast. These are argument checks, not a
completed provenance construction. Substitution entries must be tracked:
substituting into a variable dereferences the supplied entry proof, which is
not a child of that variable's derivation.

The first unclosed entry is an old proof capture versus a canonical fresh
proof variable. Its equality is a newly produced `proofIrrel` derivation.
Charging it to a proper native-observation child may work in the forward
direction, but reverse equation coverage can start from an already observed
RHS. Showing every such demand consumes an observer child requires proof
opacity. The minimal gate is `P : Sort 0, q : P, q : Sort u -> False`.
Its conversion case already needs zero-sort coherence, and application needs
shared-head codomain-shape coherence. Retained raw typings do not prove this.

Typed hole contexts provide a useful restricted substitution law. They cannot
be recovered from an arbitrary typing of the filled expression. In particular,
an outer observer expecting `B[a]` does not become an observer of arbitrary
`f x : B[x]`. The original argument equality gives endpoint conversion, not
that universal factorization.

Coinductive closure does not itself repair the remaining function cast. A
path `Pi A0 B0 -> Pi A1 B1` retags a captured function's raw trace. Applying it
to an argument at `A1` still needs the domain and codomain conversions. A
simulation clause that promises those paths would require the same proof.

## Sequential budgets and the checked transitivity obstruction

A revised candidate charges function exposure, argument demands, and
application to one sequential budget. With a source native step,
`b = B - functionCost < B` and the result uses
`j <= b - argumentCost - 1 < b`. An outer budget IH could interpret an
arbitrary capture-conversion derivation at the smaller budget. This removes
the old local promotion from `B - 1` to `B`.

Reverse closed equations can retain their original field substitution, choose
those captures on the matching side, and return the literal substituted RHS.
The original RHS typing IH supplies full-budget evidence. Partial applications
must retain their supplied prefixes; erased fields cannot be reconstructed
from the resulting observation. These local arguments remain unformalized.

[OneSidedBudgetObstruction.lean](OneSidedBudgetObstruction.lean) checks a
counterexample to the proposed raw transitivity law for **every** finite
budget `B`. Its three actual `VExpr`s are typable at the same type:

1. `Prop`;
2. `Prop` delayed by `B + 1` identity-beta steps;
3. `Prop -> Prop`.

Charging only the left trace and allowing arbitrary right cost relates the
first to the middle and the middle to the last, but not the first to the
last. The artifact uses the pure beta/head-observation fragment. It does not
claim a runtime cost for singleton proof-irrelevance conversion.

Validation: `lake env lean docs/inductives/OneSidedBudgetObstruction.lean`
passes. Printed roots use only `propext`, `Classical.choice`, and `Quot.sound`,
with no admissions. The typing witnesses use the production `Typing.Basic`
rules; no uniqueness, inversion, or environment-well-formedness theorem is
needed.

Adding an object-language equality premise changes the relation: the example
does not supply equality between the middle and the last expression. But
restricted transitivity still needs a justified new call. If the first
comparison matches source cost `l` with middle cost `m`, the second needs
budget at least `m + B - l`, possibly greater than `B`. The outer budget IH
does not justify it. Neither taking the raw transitive closure nor asserting
a limit relation supplies the missing finite-budget adequacy argument.

## Next candidate: independent finite-shape soundness

Test a preliminary interpreter of finite shapes to establish proof opacity
before the stronger relation that returns typed Pi-component paths. Its
native guards should contain only finite positive records:

```text
for each declared field C_i:
  exists c_i, Observe(capturePrefix, C_i, c_i) and HasType(x_i, c_i)
```

Data captures may be admissible subprofiles of the available index profiles;
proof captures are bottom. The interpreter is purely semantic and omits
actual target-world replay eligibility. It may overapproximate actual guarded
reduction. Reflecting actual typed observations remains a separate obligation.

The exact dependent function-field extension has a plausible noncircular
argument: soundness of the stored domain formation, applied to the already
fitting prefix, supplies `Fits.cons`'s universal refinement clause through
`InterpTyped.hsort`. It does not interpret an ambient `D -> C_i` path.
Do not insert `Fits` itself into the inductive guard: its observation
antecedents would reintroduce negative recursion.

That stored soundness must come from a justified earlier declaration stage,
with stable family-header semantics. Preservation of old *pure profile*
interpretation can be structural. The analogous claim about raw replay is
not structural: substitutions can insert later terms and enable guards.
Neither stage preservation nor formation soundness may become a caller premise.

Before porting a library, check these cases together:

- **Dependent function capture and reverse coverage.** Use a captured
  `F : Fin (f k) -> Type` that the minor actually applies. Refine its demanded
  profile using its original constructor-argument typing, factor the resulting
  type observation, and satisfy extra demands on earlier telescope fields.
  The proposed decrease is field position, not profile depth. Prove this
  finite completion for the actual generated equation.
- **Monotonicity and native compatibility.** Exact capture of the entire
  incoming profile need not stay well typed when that profile grows. Use
  admissible subprofiles, or a proved equivalent mechanism. Join positive
  witnesses under compatible prefix valuations, and align actual constructor
  indices when typing the motive result. Retain the constant rule's own type
  observation and function-profile typing: field guards alone do not type
  an arbitrary minor graph.
- **Structure eta and unit-like types.** Existing `Shape.HasType` accepts any
  constructor profile at its untagged `indTy` (ShapeLogRel:2489-2494, 2518).
  Thus a variable of Unit can receive another constructor's profile, violating
  unit-like equality; matching the name alone still permits invalid dependent
  fields. A replacement must constrain constructor choice, arity, and field
  profiles from the declaration, or prove a different sufficient observation
  design. An unchanged port of the old model fails this requirement.
- **Actual typed observations.** After global shape soundness, interpret raw
  capture-conversion proofs using that completed theorem. Establish enough
  connection to justify the fresh-proof demand in the directed comparison.
  Shape agreement alone does not provide raw Pi-component equality, arbitrary
  retyping, or confluence.

Local positive-guard arguments are evidence for this experiment, not a passed
foundation gate. The next work must close these interactions before extending
general semantic infrastructure.

## Latest conditional analyses at the planning pause

No new Lean construction was checked for the following arguments. They refine
the premises and proposed proof; they do not establish finite completion or eta.

The proposed telescope-completion theorem starts from original source-domain
formation and actual argument soundness at the declared instantiated domains.
It extends any finite demands on those arguments to simultaneously realized
profiles fitting the entire dependent telescope. The last field's soundness
refines its demand, substitution factors new demands onto earlier fields,
and the prefix induction completes them. The measure is telescope length;
finite function-profile depth is unrestricted. Join demands for both the RHS
and the dependent result type before completion. Recursor argument profiles
can retain the completed captures as subprofiles while other demands grow.

The canonical argument-typing producer is still unproved. Original application
children can type the argument at `A_i` rather than declared `D_i`. A proposed
simultaneous prefix induction uses intrinsic constructor-signature soundness
and semantic Pi reflection to align them, retaining residual signature equality
and prefix completion to form later domains. Raw product injectivity cannot
justify this step. Fixed-catalog source correspondence remains another open
prerequisite: family/constructor headers can be installed before eliminator or
projection registration, so their interpretation must remain stable across
those stages. The catalog must descend from the finite original declaration
history, not an arbitrary later replay environment.

Dependent structure profiles would retain permitted constructor names/arities
and whole admissible field tuples, with exact compatible finite joins. The
paper projection argument uses a typed major's completed tuple to supply
observations of all earlier projections, then forward substitution supplies
each declared field type. Eta reconstructs the tuple; its reverse direction
joins the finitely many demands made on the same major.

For `A : Type, x : A`, a supported tuple cannot be weakened to retain an
observation of `x` while replacing its supporting `A` profile by bottom.
This also constrains the order on type profiles: componentwise weakening of a
stored tuple would make that invalid tuple admissible again. Refine by adding
whole supported tuples and compatible joins. Arbitrary downward truncation is
not a typing law. Function fields can require deeper support than the observed
result; existing `InterpTyped` allows deeper actual completions, and upward
lifting is the relevant available law. Whether finite completion survives
these representation changes, particularly for `A, x, F : A → Type, y : F x`,
is the next substantive construction if the stronger-comparison connection
first survives scrutiny.

These arguments have not yet been checked against the experimental module;
its `SExpr.lean` currently has missing syntax cases. Repairing that import is
not itself evidence for the new construction. The risk plan explicitly checks
what the model must provide to actual typed reflection before porting it.

## Connection check after the planning turn

### Proof replacement has a coherence obligation

[ProofRetypingObligation.lean](ProofRetypingObligation.lean) proves:

1. In an inhabited extension by `z : P`, typing fresh `z` at a lifted `R`
   is equivalent to an actual `TypeConversion P R` in the original context.
2. Arbitrary replacement `q : P, z : P, q : R -> z : R`, for propositions
   `P`, is equivalent to type-conversion coherence for the two typings of `q`.
3. An ORIGINAL variable typing in the declared telescope does transport under
   a paired `Ctx.SubstEq`, including its source conversion to the use type.

The first two facts use variable inversion of `HasTypeStrong` and the existing
inhabited proof-context retraction, not type uniqueness or Pi injectivity.
All three printed roots use only `propext` and `Quot.sound`.

This is an exact obligation, not a counterexample to the intended calculus.
An observer can discard the proof computationally while requiring it at `R`,
for example application of a constant function with domain `R`. Proof opacity
does not by itself return the target typing. Retaining the original RHS
template supplies the conversion; arbitrary filled observers do not carry it.

### Dependent composition needs a complete value relation

A typed template with result `B[x]` cannot simply be put inside an outer
observer expecting `B[a]`. The endpoint equality child of `Strong.appDF`
types the two endpoints, not all intermediate substitutions. For argument
transitivity through `a_mid`, transporting `B[a]` to `B[a_mid]` generates a
new equality rather than an original equality child.

An observer-independent relation has the correct scheduling: first complete
the argument IH; then apply the original formation IH for `B` under the already
related substitution; then consume that result through conversion and outer
application. `LR.Adequate.cons` and the existing application proof display this
interface. It avoids recursively inspecting a generated intermediate typing.
It remains conditional on constructing the relation's missing native case.

### Actual versus reconstructed index prefixes

Original constructor-variable typing yields a source path from declared field
domain `C_i` to its family-index domain `D_i` at the reconstructed prefix.
After substituting captures, the available and required paths are:

```text
source:   C_i[captures] -> D_i[reconstructed prefix]
needed:   D_i[actual prefix] -> C_i[captures]
```

Original domain formation can transport the prefix equality, once that equality
is available at the correct types. It cannot supply the equality between the
actual and reconstructed prefixes. `NativeSpineMatch` currently records ambient
`IsDefEqU` entries; `NativeCaptureReplay.index` records arbitrary raw conversion
paths. Neither records a smaller original source derivation for those edges.

[TypeIndexCaptureObligation.lean](TypeIndexCaptureObligation.lean) checks:

```lean
inductive J : (A B : Type u) -> B -> Prop where
  | mk (A : Type u) (x : A) : J A A x
```

The accepted native recursor has zero parameters, three indices, two fields,
and `isK=false`. Its identity minor returns the captured field; an outer
application yields `Prop`. Both concrete witness theorems use no axioms. This
is a source/reduction check, not a formal abstract installation or LR theorem.

At an occurrence `J A B x`, capture conversion moves `x : B` to declared `A`.
For a nonbottom function demand the generic `LR.conv` approach requires
`TyRel B A` at a Pi profile, whose definition contains actual component paths.
Raw equality of these type-valued indices is not the trivial `indTy` case used
for ordinary data indices. The identity minor offers cast cancellation as an
alternative, so this example only challenges the generic per-capture producer.

Both certificates pass `lake env lean docs/inductives/<file>.lean`. No broad
build or final strict audit was rerun for these isolated foundation certificates.

### Checker-origin evidence does not remove the public obligation

`Verify/TypeChecker.lean`'s public `whnf.WF` takes arbitrary `TrExprS`.
`TrExprS.app` stores arbitrary declarative function and argument typings.
`Verify/Typing/Lemmas.lean`'s `TrExpr.beta` therefore receives a lambda already
converted to an application Pi, and currently uses `uniqU`/`forallE_inv` to
align its natural domain. Execution does not check that alignment again.
`inferOnly` similarly accepts an existing translation while skipping argument
checking. Restricting internal proofs to retained checker origins leaves this
same coherence bridge for the public inputs; requiring new origins from callers
would change the agreed contract.

**Decision:** the opacity/source-provenance connection has not passed the
foundation gate. Keep the finite-profile migration unselected and compare
replacement arguments at ambient typed index conversion. Do not treat more
profile completion lemmas as evidence that this connection is solved.

## Annotated comparison

The annotated candidate was tested at eta, beta, dependent application and
native computation. It has not passed the foundation gate. The new checked
result below concerns a local declarative equality. The bridge and global
induction analyses are not kernel-checked proofs.

### What the external annotated development supplies

The authors' [typed-confluence artifact](https://zenodo.org/records/20488664)
was inspected read-only. Its applications and lambdas retain domain, codomain
and universe annotations. `BasicMetaTheory.v:type_sort_unique` is structural
and precedes confluence. The nonlinear `J` reduction transports typed equality
guards algebraically; its computation premise concerns the literal minor.
The [paper's stated scope](https://icfp26.sigplan.org/details/icfp-2026-icfp-papers/19/Confluence-Techniques-for-Dependent-Type-Theory-with-Typed-Conversion)
omits function and dependent-pair eta. Its erasure results have normalization
restrictions; they do not directly establish our desired bridge. No artifact
code was executed or incorporated into the branch.

A separate proposed partial erasure keeps lambda domains, proofs and universe
arguments while forgetting added application and lambda-codomain annotations.
For the variable/sort/constant/Pi/lambda/application fragment, coherence of two
typed annotations of one raw term has a structural argument on that raw term.
It needs already-proved ANNOTATED Pi reflection, type/sort uniqueness,
substitution and context conversion. With that coherence established,
induction on original Strong proofs can align transitivity's middle term and
lift canonical beta, including previously chosen endpoint annotations.
No normalization or raw Pi reflection is needed in this conditional argument.

The prerequisites include reflection for the FINAL annotated equality,
including eta and singleton computation. A fixed annotated declaration and
equation catalog must also be produced from the generative specification;
typing children do not manufacture an equation rule. Current primitive
projections additionally need coherence of the hidden family/spine choices,
or their planned replacement by typed desugaring. These are substantive
conditions, not supplied results of the external development.

Annotations also remove one earlier local obstruction. For the SAME annotated
`q`, structural type uniqueness converts `q:P` and `q:R` into `P ≡ R`, so
`z:P` can be typed at `R` without Pi reflection. That observation repairs
fresh-proof retyping locally. It does not prove observational adequacy.

### Checked equality at the eta/beta/native peak

Two root eta expansions at different Pi types can be joined by nesting:
`E_A(f)` and `E_A'(f)` both expand to `E_A(E_A'(f))`. Whole-type conversion
suffices to type the nested application. This is a local argument, not a
global confluence proof.

The sharper peak starts from `(λx:A.t) a`. One branch beta-reduces to `t[a]`.
The other expands the function at a converted Pi with domain `A'`, then
computes under its fresh binder. That binder may enable singleton replay.
The resulting function `λx:A'.r` need no longer have eta syntax.

[EtaResidualObligation.lean](EtaResidualObligation.lean) checks the repair:

```text
f : Π A' B'
Γ,A' ⊢ f↑ x ≡ r : B'
Γ ⊢ Π A' B' ≡ Π A B
a : A
──────────────────────────────────
Γ ⊢ (λx:A'.r) a ≡ f a : B[a]
```

Lambda congruence and eta first relate the residual lambda to `f`. Convert
that WHOLE equality, then apply `a`. No typing `a:A'`, domain injectivity or
strengthening is used. `betaResidualEquality` composes this with the original
beta step. Both roots compile with only `propext` and `Quot.sound`, importing
only production `Typing.Basic`. The body equality can include arbitrary typed
native/proof-irrelevance computation. The whole-Pi premise must be produced;
the raw calculus's admitted uniqueness theorem is not used to obtain it here.

This corrects an overly strong negative assessment of the peak: component
alignment is not necessary for its DECLARATIVE equality. It remains necessary
for the attempted direct beta substitution at the other domain, unless a
different reduction argument is supplied.

### Retaining eta history does not establish the proposed strip induction

An experimental reduction design retains a node `N(f,r;d)`, where `d` is the
finite computation from the original eta body to `r`. An applied node may
cancel to `f a`; erasing the node gives `(λx:A'.r) a`. Cancellation versus
erasure is locally joinable: from `f a`, eta-expand, replay the stored `d`,
then erase. The argument keeps the binder witness.

Using these local joins in the proposed strip proof cycles even when `d` is
reflexive. Write:

```text
S = app_AB(lam_AB t, a)       v = t[a]
T = app_AB(N_A'(lam_AB t, etaBody; refl), a)
L = app_AB(lam_A'(etaBody), a)

original peak: S --beta--> v,    S --eta--> T --erase--> L
beta/eta join: T --cancel--> S --beta--> v
cancel/erase join: S --eta--> T --erase--> L
```

The remaining strip call is the original peak, with the same source,
conversion evidence and empty history. These particular replay diagrams
cannot be justified by source size or history length. A fixed rule-label
ordering would require both cancellation below expansion and expansion below
cancellation. This rejects that induction, not confluence of the intended
calculus or every possible history representation.

### Original proof children do not yet justify returned-guard reflection

In an original eta typing `type_conv (type_lam ...) H`, reflecting `H` is a
legitimate call on an original child. But after obtaining codomain equality
`hB` and substituting `a`, another application can require reflection of
`hB[a]`. That is a generated proof retaining the origin of WHOLE `H`, rather
than a proper child. Hereditary codomain-instance reflection is therefore an
additional obligation; ordinary original-proof height does not establish it.

The proposed pair of equality origin and original observer pointer also needs
more than labels. In `trans H1 H2`, an observer returned from `H1` can carry an
`H1`-origin guard. `H1` is not a child of the subsequent `H2` call. A completed
transfer at one observer does not answer every future demand on that guard.
Using a universal IH for `H1` could supply an internal certified handle, but
the required wrapper `PiCod(a,Q)` is a METATHEORETIC type-destructor demand,
not an ordinary term context. Its construction and target argument typing
are exactly hereditary codomain-instance adequacy. They have not been proved.

Complete typed TERM observations do supply existing beta-alignment paths,
which can be composed algebraically during ordinary lambda congruence. They
still do not close the following reverse-eta case:

```text
incoming term observation: f →* λA.t, then application at C
existing beta guard:       C ≡ A
endpoint type conversion:  L : Π A B ≡ T
eta's original typing:    K : T ≡ Π A' B'
new inner application:    app_A',B'(λA.t, y:A')
```

The new beta step needs `A' ≡ A`. The incoming observation contains no
components of `L`; it was an endpoint type conversion, not a beta guard.
Producing a type-level Pi observation of `T` requires interpreting `L`.
Requiring such a view in returned observers is a new producer obligation.
The term observation `f →* λA.t` does not by itself produce that type view.

**Decision:** no annotated-library port. The next claim must close this
term-observation/type-observation connection with a justified induction, or
replace the beta-transfer step using residual observations and prove THEIR
global decrease. The checked local cancellation is available for the latter;
the replay strip cycle above must not be reused as its proof. No production
correctness hole was closed by these experiments, and no full build or strict
audit was rerun for the isolated certificate.

## The type-view and residual connection checks

After the user's planning checkpoint, both proposed connection steps were
tested at composition. Neither establishes the foundation. The residual
composition below is now checked in production `Typing.Basic`; the analyses
of observations and capabilities are proof-design arguments, not formalized
observation relations.

### A natural type view is not a hereditary caller-type view

Structural annotated typing can expose the natural type of a literal lambda.
The conversion clause still requires:

```text
TypeView(type_conv h L, O)
  -> EqTypeView(L, TypeView(h, O)).
```

This occurs even when `O` takes no reduction steps. Given an arbitrary type
conversion `T ≡ T'`, the identity `λ(x:T).x` has natural type `Π(x:T).T` and
can be converted by Pi congruence to `Π(x:T').T'`. Hereditary comparison of
those views must compare `T` and `T'`. Choosing them to be Pi types recovers
the original component-reflection question. Term-observation depth alone
therefore does not justify the required recursion. This is not a claim that
the desired type-view theorem is false.

### Residuals preserve the wrong binder for the proposed beta call

Use a fixed caller domain `D` throughout. The original inputs are:

```text
Γ,D ⊢ t:E                 Γ ⊢ a:D
K : ΠD E ≡ ΠA B           f0 : ΠA B
G : Γ,A ⊢ f0↑ x ≡ (λD.t)↑ x : B.
```

Lambda formation and `K` type `λD.t` at `ΠA B`. Eta at `A`, followed by
whole-Pi conversion and application, then beta at `D`, give:

```text
S = (λA. (λD.t)↑ x) a  ≡  (λD.t) a = M  ≡  t[a].
```

An incoming residual observation of `S` uses `G` and an observation of `f0 a`.
After transferring the first equality, a generalized residual observation of
`M` must still retain `G` under `A`. The next beta step supplies `a:D`.
Activating `G[a]` therefore needs an additional typing `a:A`; the literal
lambda binder is now `D`. Charging the call to the original child `G` does
not supply this missing typing. Processing `G` in its original context would
instead need an observation under `Γ,A`; the supplied one observes `f0 a`
under `Γ`.

[EtaResidualObligation.lean](EtaResidualObligation.lean) now also checks:

- `extensionalResidualApplication`: compare arbitrary functions through their
  applications under `A`, then apply their whole-function equality at `D`.
- `fixedCallerResidualComposition`: the exact `S ≡ M ≡ t[a]` chain above,
  together with `S ≡ f0 a` and `M ≡ f0 a`, all at `E[a]`.

The focused Lean check passed, and both new roots use only `propext` and
`Quot.sound`. No domain component or typing `a:A` is hidden in their proofs.
This verifies equality soundness of the composition, not the observation
transfer. It rejects the simple residual-substitution bypass, not the
existence of domain conversion or every possible induction using origins.

### What eager original-child reflection would have to supply

In this particular chain, `K` really is a child of the original eta typing.
A completed reflection IH on `K` could produce `D ≡ A` before the observer
is returned, making the later substitution legal. Generalization needs a
capability that also handles every related argument pair, substituted
codomains, and future finite demands. Retaining just a raw conversion path
does not provide that capability.

Defining a certified observer and its guard capability by referring to each
other is not yet a construction. If `Obs_R` allows a guard `R(G)` and
`Cap_R(G)` means that every source `Obs_R` transfers to a target `Obs_R`,
then `R` occurs negatively through the source-observation premise. An
ordinary positive inductive/coinductive definition is unavailable in that
form. Original-proof induction can prove capabilities only after a suitable
relation has been defined independently.

There is a conditional improvement to the native producer argument. In an
original proof-irrelevance step involving a constructor, its typing at the
ACTUAL proposition is an original child. Walk that constructor's application
spine, maintaining a capability between the declared residual type and the
annotated natural type of the prefix. At each field:

1. Compose it with capabilities of the original function-typing conversions.
2. Extract the Pi domain capability and convert the original argument child's
   semantic typing.
3. Specialize the hereditary codomain capability and continue along the
   remaining constructor fields.

Composed raw paths are outputs, not new induction arguments. The remaining
field count decreases in this extraction. At the constructor result, however,
the minimal Pi-only proposal stops at `Cap(J A A F, J A B F)`. It must expose
related FAMILY indices, including type and function indices. Treating all
family-headed propositions as one opaque shape loses precisely that evidence.

The declared/source constructor correspondence also comes from
`InductiveSignature.Models.constructors` in the header environment; it is
not a child of the occurrence's typing proof. A realized semantic catalog
must supply its capability at the appropriate earlier stage. Subject to an
independently defined relation, hereditary Pi and faithful family-spine
capabilities, and this catalog, the review found no further arbitrary-new-guard
call in this specific constructor/proof-irrelevance overlap. Those conditions
remain unproved. This corrects the broader claim that the original-child route
necessarily fails merely because the resulting raw guard is newly assembled.

### A common-bottom Scott extension does not supply head adequacy

The independent-relation comparison examined the
[Coquand–Huber adequacy construction](https://link.springer.com/article/10.1007/s00224-018-9879-9).
It uses finite domain elements and type projections, validates functional eta,
and obtains syntactic reflection through an adequacy relation. Its presented
syntax covers universes, dependent functions and natural-number recursion.
The paper does not establish our proof-irrelevant singleton extension.

The following is our conditional obstruction to one proposed extension, not
a result claimed by that paper. Assume a pointed universal Scott domain,
ordinary compositional application, a single monotone interpretation of each
recursor, every proof denoting bottom, and bottom assignments allowed for open
variables. For the already accepted family `J`, choose a constant motive and
minor:

```lean
def fixed {A B : Type u} {x : B} (p : J A B x) : Type :=
  J.rec (motive := fun _ _ _ _ => Type) (fun _ _ => Prop) p

theorem fixed_constructor (A : Type u) (x : A) :
    fixed (J.mk A x) = Prop := rfl
```

Fix those closed motive/minor values and write the interpretation of the
remaining recursor arguments as `R(a,b,x,p)`. In the open constructor case,
assign `A` and `x` bottom. Iota and semantic equality soundness require:

```text
R(bottom, bottom, bottom, bottom) = interpretation(Prop).
```

Monotonicity then forces the same nonbottom sort observation at every larger
argument tuple, including the interpretation of:

```text
p : J (Nat -> Type) (Bool -> Type) (fun _ => Prop)
fixed p.
```

The actual result type is the constant `Type`, so projection at that type
cannot discard the already forced `Prop` observation. An equality check on
redundant indices cannot repair this particular monotone construction: the
positive observation is already forced at its least argument tuple.

A temporary Lean check, `/tmp/scott-singleton-obstruction.lean`, verified
source acceptance, zero parameters, three indices, two fields and `isK=false`.
`fixed_constructor` checks without axioms. At the mismatched occurrence,
`Meta.whnf` with full transparency remains headed by `J.rec`, and
`Meta.isDefEq` against `Prop` returns false. These are executable observations,
not a theorem excluding every declarative conversion. No permanent regression
suite was added for this experiment.

Thus the proposed extension does not have the direct semantic-to-head
adequacy needed by this route. Plain semantic equality soundness, or a
preliminary overapproximation for shape soundness, is not refuted. A replacement
must change an assumption, for example by retaining contextual information or
richer proof realizers, or supply a different reflection theorem with its own
guard producer. None of those replacements has been established here.

**Decision:** do not implement the residual-substitution bypass or a recursively
self-certified observer interface. The next feasibility check is the independent
relation supplying hereditary Pi AND typed family-index capabilities, tested
first on redundant type indices and fresh-binder eta. It must also explain the
mismatched open-proof case above; the common-bottom head-adequacy port is not
selected. The conditional spine
extraction is a route to its consumer, not evidence that such a relation already
exists. No production correctness hole was closed; no broad build or strict
audit was rerun for these certificates.

## The actual beta consumer and the type-free annotated comparison

The actual consumer at this checkpoint
isolates a smaller sufficient contract than the historical stratified inversion
interface. This is a checked production refactor, not a completed foundation.

### Converted beta now retains its original typing paths

`Verify/Typing/Lemmas.lean` now has two private structural views:

- `betaAppView` retains the application's original function/argument typing
  and its result-conversion path.
- `betaLamView` retains the lambda's original body typing, natural Pi type,
  and its conversion path to the supplied use type.

Both are proved from Strong's syntax-directed typing view. Their checked axiom
dependencies are only `propext` and `Quot.sound`. A `TypeConversion` retains
each edge's universe sort; combining those edges into one typed equality is
not silently assumed.

The one internal foundation boundary is now `betaLambdaAlignment`:

```text
Γ ⊢ λA.body : ΠC.D       Γ ⊢ a:C
--------------------------------------------------
∃ B, Γ,A ⊢ body:B, Γ ⊢ a:A, B[a] ↝ D[a].
```

Here `↝` is the existing finite `TypeConversion` path. This contract suffices
for the direct original-body substitution proof; it does not ask for a
stratification bound or a codomain comparison at every future argument.

`TrExpr.beta` keeps its public statement. Its beta branch instantiates the
ORIGINAL body translation under `A`, casts the canonical beta equality along
the body and application result paths, and composes at the same final type.
It no longer converts the body translation's context or uses translation
uniqueness and heterogeneous equality composition in this branch.

The alignment helper still uses the old foundation: `IsDefEqU.trans` composes
the original type path using uniqueness, then `forallE_inv` supplies the
component equalities. The checked admitted dependencies of this helper and
`TrExpr.beta` are `forallE_inv_stratified`, `fieldType_inv_stratified`, and
`sort_inv`. No new admission or final caller premise was added. The focused
`lake build Lean4Lean.Verify.Typing.Lemmas` passed (99 jobs); a separate
dependency inspection confirmed the views' admission-free bodies and these
remaining dependencies. No full build or strict acceptance audit was rerun.

Do not overstate necessity: generalized beta preservation promises the
contractum at the CALLER's result type. Applying it to an identity body gives
`a:D[a]`, not automatically `a:A`. This audit establishes a sufficient contract
for the implemented proof, not an equivalence between checker beta correctness
and full Pi inversion.

### A temporary generalized-beta rule does not settle native guard transport

A proposed bootstrap judgment would give typed equality from any source-typed
raw beta step, prove its metatheory, then prove conservativity back to Basic.
Even granting its beta preservation, the native-under-binder peak still needs:

```text
Γ,x:A' ⊢ t →native u, with replay guard G(x)
Γ ⊢ (λA'.t) a at a caller Pi with argument a:A
needed for the native residual: substitute a into G under A'.
```

Typing `t[a]` and `u[a]` by the proposed beta rule does not type that guard
substitution. Applying generalized beta to a wrapper for `G` requires typing
the wrapper application first; the existing whole-Pi conversion is for the
original term's result telescope, not this new wrapper. Closing guards under
untyped substitution would be another substantive extension, whose shape
soundness and conservativity are unproved. No bootstrap rules were added.

### Type-free annotated relations remove one guard call, but still owe Howe compatibility

These are proof-design findings, not a checked relation. Work first in fully
annotated syntax with structural type/sort uniqueness. The candidate relation
is indexed by context and relevance/sort label, rather than by the caller's
type. It retains a static typed equality at some common type, observes Pi/Sort/
family code heads, and tests function behavior with the same typed argument.

If an incoming replay types the SAME annotated `F` at both its original domain
`D` and its declared field domain `C`, structural uniqueness supplies the whole
path needed to cast its static equality with `F'`. The evidence `R(F,F')`
itself is unchanged: its index does not mention `D` or `C`. This removes the
previous demand for a semantic interpretation of that raw conversion merely
to retype an already related data capture. Identity of annotated terms matters;
identity of their erasures alone does not supply this argument.

For major-only proof irrelevance, a canonical singleton strategy can use its
fixed index-capture plan before examining the major's syntax. Both sides then
reuse the same captures and guards. Comparing a literal constructor's separate
annotated fields with occurrence indices remains a coverage obligation; the
original constructor-typing conversion is useful evidence there. These local
arguments do not construct the canonical strategy or its full coverage.

The remaining Howe application call has no established induction:

```text
H(f,g), H(a,b), source observation O of f a
  -> use the function comparison at the same a
  -> obtain a target observation O' of g a
  -> need transfer for the new compatible pair g a / g b using O'.
```

The last comparison is not an original child, and `O'` need not be shorter
than `O`. Changing the argument first allows substitution into the source
lambda body, because source beta supplies its argument typing and annotated
uniqueness retypes the static equality. But the rebuilt application observation
can grow before the subsequent function transfer. Neither proposed ordering
yet justifies all calls. Standard lambda-head simulation would supply body
evidence; restoring it must also solve the typed eta case that motivated its
removal. Direct eta contraction repairs some local cases, but observation
transfer after beta may compare differently annotated applications, for which
same-term uniqueness is unavailable.

**Next selected claim:** construct the application observation-transfer argument
for this type-free annotated relation, with explicit body evidence or a
justified context/substitution induction, and check eta against that same
construction. Do not repeat the rejected type-indexed semantic-cast objection;
the present unresolved call is the application schedule. No annotated library
port is justified until this connection and the native coverage producer are
established. The partial-erasure bridge and final-calculus coverage also remain
unproved.

## Results available at the renewed planning pause

These results refine the preceding application-transfer question. They do not
establish a replacement foundation, and no proof work was done to write the
renewed plan.

### The eta-exposed body shortcut has a recursive cycle

The proposed body comparison after exposing `f` as `λA.t` was
`t H f↑x H g↑x`. Its construction requires inverse source-computation coverage
and composition of two `H` edges; ordinary Howe right-composition with the
base relation does not supply that composition.

Adding the proposed closure rules and substituting related arguments gives
`t[a] H f a H g b`. Processing the inverse-computation edge reconstructs the
original source observation of `f a`, leaving the original application
comparison `H(f a, g b)`. Thus the alleged smaller body call restores exactly
the obligation it was supposed to reduce. Reject this construction; this is
not a counterexample to the intended calculus.

A one-step analysis offers a conditional paper argument for ordinary annotated
beta: decompose the source application and its syntactic lambda, use the beta
component guards, substitute the body relation, then append base-relation
edges. Howe substitution and independent base beta equivalence still require
proofs. The first unresolved extension is eta-beta fusion at a converted
caller type:

```text
app_C(λA.(f↑x), a) -> app_C(f, a)
body comparison: H(f↑x, u) under A
available argument: a:C
missing for the proposed substitution: a:A
```

The target body `u` may have lost its eta syntax. An extensional closure rule
must itself justify this same call; merely adding the rule does not solve it.

### Split-retraction guard transport is checked conditionally

`ProofRetypingObligation.lean` adds `guardPathAlongSplit` and
`guardPathUnderBinder`. Given a typed split embedding, an already typed open
term, an already formed desired open type, and an arbitrary typing after
retraction, they construct the open type-conversion path **assuming
`SameTermTypeCoherence`**. The argument weakens the source guard and uses the
typed round trips. It does not inverse-transform that guard's derivation or
treat it as an induction child, so the guard may have arisen after substitution.

The focused certificate previously passed with all five printed roots using
only `propext` and `Quot.sound`. The new premise remains explicit: this does
not prove coherence for production raw syntax. Its intended structural
producer belongs to a fully annotated calculus; that calculus, complete
observation lifting, native constructor/singleton coverage, and the bridge to
production typing remain unproved. No production foundation hole was closed.

## Resumed comparison: converted cuts, eta contraction, and native coverage

The planning turn did not reduce the proof risk. The following work tested
alternatives at the selected eta/singleton/application connection.

### Converted cuts close pure eta, but do not substitute into child guards

Given `f : ΠA.B`, a whole-type path `ΠA.B -> ΠC.D`, and `a:C`, the pure
eta contractum `f a` has the caller's result type directly. This part needs no
`a:A`. But commuting the cut into a body derivation under `A` encounters a
child `v:E` or native guard `G(x)`. The available path concerns `ΠA.B`;
it supplies neither `a:A` nor a path for the new wrapper type `ΠA.E`.

Retaining that wrapper application preserves typing but does not eliminate
the cut. Transitivity can compose already constructed cuts at a fixed caller,
but cannot construct this missing child substitution. Thus the proposed cut
schedule does not independently establish converted beta. This paper argument
rejects that schedule, not every possible weaker consumer proof.

### Eta contraction has a witness-dependent native fork

In the annotated ordinary beta/eta peak, the source beta already supplies
component paths between the lambda and application annotations. Static
annotation conversion joins the resulting two applications. This local paper
argument does not require new Pi reflection.

Modular commutation instead fails at a computation enabled by the removed
proof binder. Using the accepted `I` in `SingletonStrengthening.lean`, take

```text
Q := P v
p : I c v (leftMap v)
f := I.rec (constant motive Q -> Type)
       (fun _ _ => fun _ : Q => Prop) p

λq:Q. f↑ q ->eta f
λq:Q. f↑ q ->native/beta λq:Q. Prop
```

The second branch uses `q` as the singleton proof capture. Replaying that
computation outside its binder needs a witness of `Q` in the smaller context.
Forward weakening supplies no such witness. This persists with identical
caller/lambda domains. Eta-then-native postponement is a different direction
from the required fork commutation; joining modulo symmetric eta reintroduces
the binder and abandons the contraction-only proposal.

This identifies the unproved commutation call. It does not formalize full
nonjoinability, and the production `FullStep` uses eta expansion, so it is not
a counterexample to that relation. Any modular base theorem must also cover
native guards using the final equality, not only the eta-free judgment.

### Checked: canonical native coverage already contains data transfer

`TypeIndexCaptureObligation.lean` now imports production typing lemmas and
checks three roots in `VEnv.NativeCoverageObligation`. For a naturally typed
singleton family and its identity-minor selector:

```text
H : F ≡ G : A
ctor F : family F          becomes ctor F : family G
selector F (ctor F) ≡ F    implies selector G (ctor F) ≡ F
```

`retagConstructor` uses family congruence and conversion.
`selectorAtConvertedIndex` uses selector congruence, symmetry, and the literal
constructor-iota equation. Neither uses uniqueness, inversion, or strengthening.
The family/constructor/selector signatures and literal equation remain explicit
premises; this certificate does not install the complete abstract declaration.
The existing accepted `J` source supplies the concrete repeated-index pattern.

For an observation predicate, ordinary constructor-iota expansion followed by
canonical coverage choosing the occurrence index `G` gives
`Observe F -> Observe G`. `canonicalCoverage_requires_dataTransfer` checks
this consequence with both operational premises explicit. Their general
production proofs are not supplied. The result shows what uniform canonical
coverage must accomplish: arbitrary data equality transfer, beyond proof-only
substitution. It does not show that this broader theorem is false.

If a source observation provides explicit field/index equality, same-term
annotated coherence can retag the field equality and type the selected capture.
If it provides only major typing at the actual family, extracting those
indexwise equalities already needs family-spine reflection. In either case,
typing the capture does not transport an observation of the minor's result.
An original equality-derivation child can be useful; observation length and
field count alone do not justify interpreting an arbitrary generated guard.

Validation: the focused Lean command passes, including original acceptance
checks. All three new roots depend only on `propext` and `Quot.sound`. No
production correctness hole was closed; no full build or strict audit was run.

### Next comparison: proof fibers that retain index correlations

A paper-level local algebra avoids the earlier common-bottom argument.
At world/index pair `(a,b)`, keep a neutral proof `ν_ab` and, on the diagonal,
a distinct constructor proof `κ_a`. Exclude the domain bottom from valid proof
realizers. A partial equivalence relation (PER) equates the nonbottom proofs
within that fiber. The recursor maps the constructor to `Prop` and the neutral
to a residual `r_ab`; its result PER equates `r_aa` with `Prop`, leaving an
off-diagonal residual separate. It does not identify their domain values.

To support monotone non-strict proof completion, the local order must put the
neutral realizer below the admitted constructor, with raw bottom below both.
Completion sends raw bottom to the neutral and fixes realizers. Recursor
monotonicity then also requires `r_ab <= Prop` when the world contains the
diagonal correlation. Changing only the proof order would be insufficient.
The resulting completion is idempotent but not a deflationary projector.

Uniform substitutions preserve a shared diagonal index, but may identify
previously different indices. Mapping both proof and residual labels by the
same substitution preserves these PERs and commutes with the local recursor.
This is a consistent local constant-motive algebra, not a checked universe,
dependent function, eta, or full native model.

The next decisive question is whether this representation admits an independent
interpretation of arbitrary proof terms and dependent substitutions, together
with a universe PER that transports data/function indices and reflects actual
typed component paths. Excluding bottom as a proof realizer needs a producer
that does not assume normalization. Plain pointwise finite approximations can
also make unrelated indices both appear bottom: treating that approximation
as a diagonal correlation would reintroduce the old adequacy problem. The
correlation must survive the relevant information order and substitutions.
In the local name model, correlation means a shared name, not equality of
current approximants. A substitution may merge names and thus add a diagonal
equation, but cannot split one shared name. This keeps the `Prop` observation
upward closed within each world without propagating it to an unrelated pair.
Extending this to nonliteral dependent index equality is still required.

The [domain-inversion paper](https://arxiv.org/html/2607.13662v1) establishes
inversion with eta for its core model and describes further extensions, but
explicitly leaves scaling to proof irrelevance with K among the challenges.
Its finitary-projector model admits bottom at every type. The proposed proof
fibers change that property and therefore cannot be treated as a routine port
of its adequacy proof. No domain or annotated library port is selected.

The next review makes two requirements more precise. Closure of valid proof
realizers under a zero-stage projection that returns bottom would immediately
make bottom a valid proof again. Thus the realization/projection interface must
change too. A non-strict interpretation can instead retain a finite typed proof
thunk, so a neutral or divergent proof need not be evaluated before becoming a
realizer. This needs substitution-natural interpretation of original proof
derivations, with the same correlation and constructor PER membership. It is
an interface argument, not a checked interpretation.

**Next selected claim:** construct the universe/Pi PER's native compatibility
for such a proof thunk and a constructor proof, with actual dependent type
paths on reflection. The proof-thunk substitution wrapper is not the difficult
part to complete first. The construction must handle nonliteral equality of
type/function indices, not only diagonal syntactic names, and must explain why
newly produced capture evidence is available without a circular adequacy call.
Returning a setoid equality or assuming a universe-reflection callback does
not pass this connection check. The converted beta consumer remains the first
production application to audit once this claim has a viable construction.

### Planning checkpoint: semantic substitution needs its own evidence

The following review results are paper dependency analyses; no new
construction or production proof was checked during this checkpoint.

Raw equality certificates do not suffice as semantic substitution entries.
Take the original reflexive judgment `X ≡ X : Sort` in context `X : Sort`.
A pair of substitutions can send `X` to `ΠA.B` and `ΠC.D`, with an arbitrary
raw equality `K` between those types certifying the entry. Interpreting the
variable must then supply the universe/Pi capability for `K`. But `K` is not
a child of the variable derivation. Consequently, original-derivation height
does not justify this call. The semantic substitution must already carry
independently validated hereditary entry evidence.

With such evidence genuinely supplied, an induction hypothesis for the original
body, quantified over semantic substitutions, can handle beta after dependent
substitution. It need not recurse on the newly built substituted derivation.
The unresolved part is the independent producer of that evidence, particularly
for generated native replay paths. Storing raw paths in world validity or
invoking a fundamental theorem on them does not by itself provide a decreasing
construction.

Transitivity has a separate manifestation of the same need. Independently
exposing a neutral middle term as a Pi twice creates a comparison between
the two views that is not an original child. Requiring the second induction
hypothesis to accept any incoming view moves the problem into the literal-Pi
reflexive case, unless those views already carry the requisite validated
component evidence.

Even correlation of indices must handle computation after substitution.
For example, two distinct source names can be sent to `k x y` and
`(fun a => fun z => k a z) x y`. Their images remain syntactically distinct.
Beta/congruence can justify their correlation, so this example does not refute
semantic worlds; it refutes relying on literal name merging alone. Native
selector residuals extend the obligation to arbitrary data equality.

These analyses do not reject every semantic-world construction. They fix the
next feasibility test: independently define the universe/Pi relation and its
entry producer, then check native compatibility, typed component reflection,
eta/application, and composition with explicit recursive decreases.
This was the proposed feasibility test at this checkpoint; it was not a
construction of the required entry producer.

## Repair a false field-inversion bound

The foundation statement review found a concrete defect in
`fieldType_inv_stratified`. It demanded that a second field type be retyped at
the first field's literal universe expression without increasing the second
typing's stratification height. Equivalent levels need not have identical
syntax, and `HasTypeStratified.defeq` charges a step for that conversion.

`StratifiedUniverseObligation.lean` checks the exact obstruction. Given a
constant lookup with stored type `Sort 1`, the constant is typable at height
one at `Sort 1`, and at height two at `Sort (max 0 1)`. Constructor inversion
proves that the latter typing at height one is impossible. The lookup is an
explicit premise; the file does not install a complete projection environment.
The existing executable `ProjectionWithoutCasesOn` fixture supplies the
ordinary accepted source pattern: a structure with a field of type `Nat`.

The production repair leaves raw typing and stratification unchanged. The
field theorem now returns field equality at the first sort and equivalence of
the two field levels. The projection branch of `IsDefEq.uniq` uses that level
equivalence and the second field's original typing. Its induction conclusion
already allows distinct equivalent levels. No final caller responsibility or
new admission was introduced, and the named field-congruence obligation remains
open. This is a statement correction, not a proof of the corrected theorem.

The analogous Pi bound has an enclosing-constructor step available for
retyping its components; the height-one example does not refute it. The bounded
review found no further counterexample to sort/Pi inversion.

Validation: the focused certificate passes, with each of its three printed
roots depending only on `propext` and `Quot.sound`.
`lake build Lean4Lean.Verify.Typing.Lemmas` passes (99 jobs). The edited
production files pass `git diff --check`. No full build or strict completion
audit was rerun.

### Finite profiles repair bookkeeping, not native admissibility

The parallel construction review distinguishes two claims. A bare depth-indexed
relation can fail when application asks for a higher-depth induction hypothesis
under a substitution validated only at the lower depth. Requiring all-depth
substitutions then conflicts with lambda's finite-depth argument clause.
That objection does not apply unchanged to explicitly indexed finite profiles.

`Experimental/ShapeLogRel.lean:LR.DefEq.lift` pads a finite profile to a larger
ambient level without adding observations.
`Experimental/ShapeLogRelAdequacy.lean:LR.Adequate.cons` combines that padding
with restriction, compatible type-profile joins, and the original domain IH
to extend a substitution from one finite argument profile. It does not require
completion of that argument pair to an all-depth related pair. These existing
core proofs identify the legitimate bookkeeping pattern; they do not establish
those closure laws for the proposed native/correlation model.

In particular, a larger profile is not by itself a common typed view of a
neutral middle term. Existing `LRS.join_ty` uses head-reduction determinism
before joining the two domain/codomain profiles. Independently returned Pi
views may have domains `D₁` and `D₂`. Probing both codomains with a variable of
type `D₁` requires that variable at `D₂`, hence the domain path being sought.
Do not import this join proof into a different observation relation with that
step left as an assumed callback.

An alternative generic completion proposal also has a paper obstruction.
Arbitrary monotone, continuous, nondeflationary idempotents need not have
images approximable by finite deflationary retractions. For example, retract
sets of rational observations onto open rational cuts, always adding a neutral
token. On the resulting interval of cuts, every continuous finite-image
deflationary idempotent fixes only the least cut: fixing a positive cut would,
by continuity and finite image, send a strictly smaller cut to it, violating
deflation. Thus composing arbitrary typed retractions with truncations does
not supply the missing finite construction. This argument was not formalized,
and does not refute the particular finite proof-fiber completion or a universe
of more constrained retractions. Generic pair completion is no longer selected.

**Next selected construction:** independent admissibility of finite family/Pi
profiles, with restriction, join, and dependent application strong enough for
the native singleton call. Test it on the original typing
`mk A F : J A B G` and a demanded selector result profile `m`. The profile must
support actual `A ↝ B` and cast `F ≡ G` paths and hereditary data behavior at
`m` (at an argument-to-result profile if the minor applies `F`). An original
conversion child can legitimately supply its IH at a padded profile; the
missing premise is admissibility of that demanded profile in the first place.
General proof-irrelevance cases must obtain it from the observed constructor's
original typing spine, not assume arbitrary result capabilities in proof
membership. Finite token storage is insufficient: its unions must be realizable
and its paths compatible with dependent application. Do not implement another
conditional constructor-spine wrapper before constructing this relation and
its essential closure. The actual converted-beta consumer remains the first
production connection to establish. No native/Pi foundation proof was completed
by this comparison.

## Fixed proof tokens and a common symbolic readback

The next comparison tested a deterministic native observation strategy:
singleton recursors use the occurrence-index captures, and an unavailable
guard leaves the observation stuck. Proof captures are canonical named tokens,
with fixed declaration domains and domain dependencies. Their names exclude
the major proof and the witness chosen to realize a token.

At the reduction layer, adding guards preserves completed traces when rewrite
results are fixed. To compare two observations of a middle term, keep both
inside their symbolic proof frames, amalgamate those frames, and align the
middle there. Retracting the two views independently too early would produce
`D[q]` and `D[q']` and lose literal head agreement.

There is a paper construction of the common frame. Union the finite canonical
keys and order them by their domain dependencies. For each new key, choose an
originating frame and construct a typed substitution from its original prefix
into the current union: present keys map to union variables; absent keys map
to their original witnesses under the already constructed substitution. This
fallback decreases the original prefix length. Once all domain dependencies
are present, the domain image is the canonical domain and the substituted
original witness inhabits it. `SplitProofFrame.cons` can then add the binder.
Witness-only dependencies do not require additional ordering constraints.
Identified keys can make the maps noninjective, so a complete observation
development must support typed substitutions, not only renamings. The named
syntax, complete key-union construction, and trace stability are not yet
formalized.

Eta retains its ordinary binder in the base context. Only the added proof
tokens are retracted; a native replay enabled by the ordinary binder therefore
does not demand a witness outside that binder. Converted application still
needs the original conversion child's Pi-domain capability before substituting
the argument. Once that capability exists, ordinary typed substitution can
transport the frame and its witnesses.

### Checked: component equalities from a common symbolic Pi

`SplitTypedEmbedding.compareRetractions` now proves an actual cross-realization
equality from a common symbolic typing. The two embeddings may have different
base contexts and retraction witnesses, but must embed the same variable
positions. Apply one embedding's reverse round trip, substitute using the
other retraction, and use its literal left inverse. The proof uses no type
uniqueness, Pi injectivity, normalization, or semantic guard interpreter.

`SplitProofFrame.piReadbacks` applies this result both to a commonly typed
symbolic domain and under its retained dependent binder. For two realizations
`r` and `s`, it returns:

```text
Γ ⊢ A[r] ≡ A[s] : Sort u
Γ, A[r] ⊢ B[r↑] ≡ B[s↑] : Sort v
```

The common symbolic typings are essential premises; two unrelated typings of
the readbacks do not imply this result. This verifies the proposed readback
step, not the existence of a common symbolic native observation.

Validation: `lake build Lean4Lean.Theory.Typing.SplitTypedEmbedding` passes
(40 jobs). Both new roots print only `propext` and `Quot.sound`; whitespace
checks pass. No new test file, admission, or final caller hypothesis was added.
No production foundation admission was closed, and no full build or strict
completion audit was run.

**Next selected claim:** construct independent family/Pi profile admissibility
and its native capture producer. For an original typing
`mk A F : J A B G`, the demanded field/function profile must be admissible
before calling an original conversion child's IH at that profile. Its result
must supply actual `A ↝ B` and cast `F ≡ G` evidence and the demanded data
behavior. Only then can the original proof fields be transported to realize
the canonical proof-token domains. Adding `z : Q(G)` as an opaque token does
not show that `Q(G)` is inhabited in the original context. Neither the checked
readback operation nor deterministic trace alignment supplies this missing
data-index capability. Do not implement the surrounding named-token library
before this producer has an independent admissibility argument.

## Planning checkpoint: a constructor exposed through proof substitution

The latest two independent reviews distinguish a conditional literal case
from a harder substitution case. These are paper dependency arguments. No
relation, adequacy theorem, or new Lean certificate was implemented for them.

For a constructor visible in the original derivation, an observation of the
original minor result can demand a field profile `m` (a finite function demand
when the minor applies the field). A strengthened typed-interpolation induction
hypothesis on the original child `F : A` could supply a typed refinement
`f : a`. A structural family-observation clause could then build the natural
profile `J-profile a a f` for `J A A F`, before invoking the original conversion
child to `J A B G`. A suitable family relation would return actual `A ↝ B`,
cast `F ≡ G`, and the demanded data capability. Proof opacity alone does not
invalidate this scheduling. The strengthened induction hypothesis and full
family relation are still unproved, so this is not a completed literal-case
foundation theorem.

Now start with source proof variables `p, q : J A B G`. A target substitution
can send `p` to `mk A* F*`, typed at `J A* B* G*` through a target-only conversion
`K*`. Native evaluation after substitution can demand an observation of `F*`.
The source variable/proof-irrelevance derivation contains neither `F*` nor its
field-typing child. The literal argument cannot invoke that child as an
original induction hypothesis here.

This is a separate issue from using raw equalities as semantic substitution
entries. Even ordinary hereditary validity for every already admissible
family profile does not itself produce the new profile demanded by the exposed
constructor. The missing operation is demand discovery and admissibility from
the substituted proof realizer. A stronger entry interpretation might supply
it, but must have an independent construction and a producer from actual
typing derivations. Recording an exposure certificate as an unexplained
premise would only restate the obligation.

This review identifies an unfilled call in the candidate; it is not a proved
counterexample to all possible interpretations or to the intended calculus.
The checked common-Pi readback result remains valid with its stated premises.

The proposed feasibility test at this checkpoint was the substitution
producer and its continuation through conversion, composition, and dependent
application. This identified a missing connection; it did not establish that
the equality foundation could be completed.

## Direction audit and realization-indexed finite observations

Inspection of the actual code corrected the preceding proposed first
obligation: reverse coverage of every constructor exposed in a target
substitution is unnecessary for the source-directed adequacy route.

The relevant source locations are in `Experimental/ShapeLogRelAdequacy.lean`:

- `LR.adequacy` at line 106 takes a SOURCE `LE_Interp` observation.
- Transitivity at line 122 moves that source observation through the original
  equality child before invoking the next child.
- Beta at line 390 uses the original application/body children and target
  beta closure. Proof irrelevance at line 417 makes the source profile bottom
  without inspecting the substituted target proof.
- `forallE_whRed_l` at line 434 starts with a literal source Pi profile and
  uses identity substitution. It does not request all target observations.

These are inspected dependency facts in the experimental implementation, not
a claim that its native extension is proved. In particular, its current
constant and native support is insufficient for the final calculus.

The native replacement for the direct `extra` contraction at line 424 can use
a chosen canonical target reduction: expose the fixed canonical captures,
compare them with the original equation's captures using original children,
and expand along that chosen reduction. The relation needs two-way closure
under its chosen reduction, not under every ordinary native contraction.
This is a conditional native proof schedule; canonical guards and the
underlying interpretation still need production.

### Define the target relation first

The existing `LRS.PiDefEq`, `ValTyPi2`, `LamDefEq`, `TyDefEq`, and `DefEq`
definitions use raw target head reduction, typed paths, finite profile typing,
and lower relations. They do not mention `LE_Interp`. Accordingly a candidate
target relation `R` may be defined first by profile recursion, provided its
canonical target reduction uses only raw typed guards. Source observations
can then mention this already defined predicate without an Obs/R definition
cycle. This does not establish the required new profile grammar or relation.

Use source observations indexed by a target realization `sigma` as well as
the finite source valuation `rho`. The proposed fundamental statement returns
both the corresponding observation under `sigma'` and target relatedness,
given related substitutions. It need not preserve the old realization-free
adequacy signature. Making guards uniform over all realizers instead would
introduce an unnecessary inverse source-weakening problem when extension
restricts that set of realizers.

Simply stratifying Obs itself by the rank of guard capabilities is not yet a
replacement: padding would then change which observations are admissible.
The existing `LR.DefEq.lift` at line 6046 keeps raw target observations fixed,
and proves no such change-of-observation theorem. Deep field demands alone
are not a counterexample to finite profiles; their full finite support can
have a greater rank than the final result.

### Raw self-validity is insufficient; retain an argument anchor

For opaque target types `B,C : Type` and `g : B`, use the singleton selector
`t(X,p : J X B g) : Type` with constant motive and minor returning `Prop`.
The proposed canonical guard is available at `X=B` by reflexivity; at `X=C`
it needs an additional type path. Both opaque types have the bottom profile
in the old head-profile grammar. An observation at argument `B` therefore
cannot establish a lambda clause ranging over EVERY raw argument self-valid
at that profile. The original body IH needs paired argument evidence, which
self-validity of `B` and `C` separately does not provide. This is a paper
failed-call analysis for that clause, not a new kernel-checked nonconversion
theorem or a counterexample to the calculus.

A candidate finite function row retains an actual argument anchor `a`, an
input profile `p`, and an output profile `m`. It admits `x` only with actual
typing, `a ≡ x`, and lower-profile `R(a,x,p)`. The original body IH can then
transport the observation at `a` to the admitted `x`. The following local
arguments have independent paper reviews:

- Application composes the row's argument relation with the original argument
  child's relation. Eta uses the same reanchoring operation. At a converted
  function type, the original conversion child's Pi-domain capability casts
  the anchor; its Pi-edge capability transports dependent result types.
- Rows and their compatibility must quantify over FUTURE target context
  extensions. Current-context-only coverage does not handle new arguments
  enabled by a fresh binder. Forward weakening composes the extensions.
- Join by finite UNION of rows. At an actual overlap, both lambda clauses
  give body observations in the same target context under the same realized
  argument. Their compatibility can be proved there. An overlap may first
  become inhabited in a future context; do not preselect one current-context
  anchor for every possible intersection.
- Source weakening keeps the target context and anchors fixed and changes
  the source substitution/valuation. It does not require inverse weakening of
  the raw target anchors.

### Every native guard must retain its finite source support

A guard `R_q(L[sigma],R[sigma])` must retain source observations of its endpoint
and type expressions at the demanded profiles. Otherwise it could inspect a
substituted argument at `q` while the binder's recorded profile is bottom; the
body IH would then have no paired `q` evidence with which to transport it.
The observation grammar, not an external callback, must expose this support.

For `J`, let `T_AB` be the source guard aligning the realized type indices.
The explicitly supported index observations let original children produce
cross-realization capabilities `T_A`, `T_B`, and the field capability. The
target internal alignment is `T_A.symm.trans T_AB |>.trans T_B`; actual
`TypeConversion` paths compose identically. Field relations convert along
those paths to the declared capture domain. This uses supplied capabilities
algebraically, without induction on a newly generated guard derivation.

**Next selected construction:** define the anchored finite family/Pi profiles,
their admissibility, and typed interpolation with these explicit supports.
Restriction, padding, and finite union must preserve enough evidence for the
dependent constructor telescope and native minor application. Test those laws
at the actual indexed-singleton call before implementing a general table or
token library. Neither the relation nor these laws have been implemented.

This turn removes an unnecessary proof demand, rejects an unanchored raw
realizer clause, and gives a more specific candidate with locally checked
dependency arguments. All new construction arguments above are on paper.
No production foundation admission was closed, no Lean code or test was
changed, and no build or strict audit was rerun.

### Next exact call: finite domain refinement with fixed argument profiles

The final bounded review checks uniformity of the dependent function type
profile. For each finite row, the SOURCE lambda observation must retain:

```text
Obs_sigma,rho(A,d_j),  p_j : d_j,
Gamma0 |- a_j : A[sigma],  R_(p_j,d_j)(a_j,a_j).
```

The source observation premise belongs to the Obs constructor, not to the
intrinsic profile definition used to define R first. Putting Obs back into
that intrinsic definition would invalidate the proposed construction order.
Target typing and target R alone cannot recover this source premise.

The needed finite domain law is:

```text
For finitely many supported d_j of the SAME source domain A, construct d with
  Obs_sigma,rho(A,d),  d_j <= d,  p_j : d
while retaining every p_j and every raw anchor a_j unchanged.
```

With that law and the relation's type-refinement laws, the original domain
IH alone can establish the substitution extension at each anchor. Only then
invoke the original body IH, obtaining fixed refined output/type profiles for
that row under the unchanged `rho.push p_j`. For every future admitted `x`,
construct the paired extension at `(a_j,x)` by the same domain argument;
the original codomain-formation and body IHs transport those fixed profiles.
There is no need to choose a different type profile for each future realizer
and then take an infinite join.

The required domain and codomain formation children really are present in
production `IsDefEqStrong`: `lamDF` at `Theory/Typing/Strong.lean:93`, `appDF`
at line 68, and `beta` at line 109. Thus the argument does not charge a newly
constructed formation proof to the current body's induction hypothesis.
For the dependent telescope `A,x,F : A -> Type,y : F x`, the final extension
must use the original formation IH for `F x` with previously established
F/x support; a new unsupported demand there would fail this construction.

The finite-domain law, the underlying family/Pi profile definitions, and their
restriction/compatibility laws are still unproved. This is the next exact
construction to test, before any general observation/table library. The review
establishes a conditional recursion schedule, not the lemma itself.


## Planning checkpoint: dependent restriction and the original Pi producer

The following preserves bounded paper arguments from two reviewers. None
was a newly checked Lean construction or a closed production admission. At
this checkpoint the complete profile grammar and native adequacy remained
unconstructed.

### Frozen supports and dependent restriction

A proposed row freezes its raw anchor/domain, input profile, type support, and
output. Eligibility uses those stored supports, not the ambient domain profile.
At an actual future world and actual admitted raw argument, choose finitely many
support rows covering the active outputs. Join their input profiles to obtain
an input below the original input, retaining coverage. With lower-rank typed
join and admission laws, restriction preserves the function output; lower-rank
type transport moves that output to the refined dependent codomain.

A proposed concrete grammar uses finite conjunctions of type/value demands,
with union for joins and existential coverage of each value atom by a type
atom. Same-source domain observations would supply support for the union while
retaining each row's input and anchor. A nonempty value relation must retain all
its type-profile capabilities, allowing a later restriction to replace a
covering type atom. This proposal still needs the complete intrinsic grammar
and its proofs; a coverage predicate alone is not that construction.

The candidate keeps an explicit proof/data relevance distinction. Empty value
profiles remain trivially related, and function rows have nonempty outputs.
Otherwise a strengthened type requirement at bottom would reintroduce a type
adequacy obligation into the identity substitution before its producer exists.
This is a constraint on the proposed construction, not a proved full model.

### Frame scope and fixed raw Pi prototypes

An outer existential split proof extension can collect finitely many type
capabilities in a common context. The core function clauses must additionally
quantify over future injective typed context extensions and their raw arguments,
including new data binders. A separate lower-rank frame may be chosen for each
argument result. Restricting the future quantifier to proof additions silently
weakens the required function clause.

Existential-frame absorption works only when the endpoints, type, and profile
are lifts from the requested base. It does not turn raw readback equality
between D[r] lifted back and D into a semantic relation. Keeping all data local
to the larger context merely moves this scope problem to exporting profiles or
substitution entries.

The proposed repair fixes a base-context raw Pi prototype Pi B.C in a type atom.
A symbolic display Pi D.E carries full raw domain/codomain paths to that
prototype, lower-rank domain capabilities, and lower-rank capabilities for each
fixed codomain test. Comparing two such displays can compose through their
common symbolic display to endpoints that really are lifted prototypes. The
lower existential frames can then be absorbed without semantic retraction.
Full raw codomain paths are necessary even for an empty table: pointwise tests
alone cannot return full Pi reflection. Pi validity also needs lower-rank
functoriality for related arguments, not just a reflexive pointwise comparison.

The producer review proposes using original domain and codomain formation
children in `IsDefEqStrong`. Source Pi observations retain domain observations,
raw prototype alignment, and supported observations of the original codomain.
The domain IH creates the paired substitution extension; only then does the
original codomain IH transport the row test. Related-argument functoriality uses
that original child under two related arguments. Raw full-codomain paths use
typed substitution under the prototype binder. This is a proposed decreasing
schedule, conditional on the unconstructed grammar and lower laws.

The proof-frame union argument concerns forward injective embeddings. It does
not establish arbitrary data-substitution stability: such substitutions can
merge previously distinct anchors and introduce incompatible rows. Any later
use requiring that stronger property must identify and prove it explicitly.

### Decision and next evidence

The local paper arguments refine a candidate; they do not establish foundation
feasibility. The next attempt must make the coupled dependent restriction and
original-Pi producer explicit, check its decisive construction, and connect it
to the hard native/eta/dependent-application call at the real checker boundary.
Do not treat a conditional frame library or a new producer callback as success.
Rerank the risks after decisive evidence; compare different constructions at the
same failed call if this one cycles. No Lean code, tests, full build, or strict
audit changed during this planning checkpoint.

## Earlier planning checkpoint: constant adequacy and source staging

This checkpoint revised the candidate clauses in the preceding entry. It
records completed paper reviews and source inspection, not a new Lean
construction. No production foundation admission was closed by these arguments.

### Corrections to the dependent-profile candidate

- A function-row key freezes the raw domain, anchor, input profile, and input
  type support. It cannot require a full fixed Pi codomain: a source lambda
  observation does not determine the codomain of every typing of that lambda.
  Covering Pi type atoms may carry different codomain prototypes. Function
  outputs are related at the actual displayed caller codomain. Different covers
  must therefore transport the unchanged output using lower capabilities at
  that same actual type.
- Remove the fixed proof/data relevance header. An empty Pi table does not
  determine the original codomain sort. Code-profile sort typing must constrain
  every supported output, while function coverage stays existential. Otherwise
  joining a strong cover with an empty cover would destroy supported output.
  The corresponding proof-opacity argument remains a paper argument.
- Retain component `TypeConversion` chains with individually typed edges.
  Original codomain formation and a prototype path can use different sorts.
  `DependentTypeConversion.changeDomain` and `composePi` support the raw path
  operations already; closing a chain through uniqueness would be circular.
- Proof-frame absorption only applies to endpoints and profiles actually lifted
  from the requested base. Function clauses must still cover future typed
  embeddings with new data binders. Raw readback equality alone supplies no
  semantic transport.

The full grammar, rank, closure laws, original Pi/lambda producers, and chosen
canonical native reduction remain unconstructed. These corrections repair
particular proposed calls, not the complete foundation.

### The next missing producer

Observation induction alone does not produce a lambda's behavior at every
future admitted argument; the original body theorem supplies that parametricity.
Typing induction alone cannot interpret a constant by invoking the theorem on
its independently supplied RHS typing. Transitivity also transports observations
before applying its next typing child. Neither simple lexicographic ordering of
typing height and observation size resolves both calls.

Source rules provide a possible different decrease:

- `VDecl.WF.mutualDef` in `Theory/Typing/Env.lean` checks declared types in the
  base environment, then bodies in the environment with opaque headers, then
  adds equations.
- `VInductBlock.WF` in `Theory/Inductive/Formation.lean` retains typing of all
  rules before adding the block's equations.

The proposal is to prove the earlier-source-stage fundamental theorem uniformly
into the final target relation, relative to a supplied polymorphic opaque
signature. For a current-head observation, cut its finite source-observation
tree at current-block heads, retaining ORIGINAL proper descendants and all
type/native-guard support. Apply the observation hypotheses to those descendants
individually; only then join their resulting semantic capabilities. Interpret
the original body typing using the earlier-stage theorem, restore its opaque
observation leaves, and prepend the chosen typed native reduction.

The construction must prove the following, rather than package them as premises:

- Finite factoring preserves the actual source operand/template provenance.
  Equal raw realizations of different source operands do not give source support
  for the operand actually used by substitution or weakening.
- The induction uses original descendant occurrences, never their newly joined
  or refined observation. Collect demanded type profiles too. Universal future
  argument clauses belong to the semantic relation; source support is finite.
- Opaque entries are polymorphic. Equivalent universe lists may denote different
  raw terms; identifying them as one source variable loses literal realization.
  A descendant hypothesis must provide observation transfer and semantic
  coherence to equivalent instances at fixed finite profiles. Raw level equality
  alone is insufficient. Unobserved entries use bottom support.
- The source-stage relation is justified for the entire final calculus,
  including abstract eliminator registration and specialized rules. Concrete
  `VInductBlock.WF` is evidence for concrete rule staging, not automatically a
  producer of every abstract rule typing. Mutual bodies can mention opaque
  current heads in binder domains; a recursor-only syntax argument is too weak.
- Any native observation syntax that bypasses a compositional head observation
  needs an explicit strict extraction argument. It cannot silently treat a
  newly constructed head observation as an original child.

Independent paper reviews found no further cycle in this strengthened schedule.
That is limited evidence: the complete definitions, relative fundamental
theorem, finite factoring, and current-block producer are all unproved. The
next attempt must construct them at the difficult call and connect the result
to dependent alignment in the actual checker. Reassess the largest remaining
risk at each decisive result. No additional tests are a separate workstream.


## Coupled dependent application and case interpretation

The following evidence changed the candidate construction at this checkpoint;
it did not establish a complete model.

The uniform unconditional capability for abstract heads had a missing induction
hypothesis: recursively encountered heads did not inherit the original generic-
type formation child's semantic result. The candidate replacement separates
head kinds. Current recursive constants use earlier-stage body interpretation
with opaque capabilities for current constants. Each abstract eliminator uses
a direct operator on the generated case template, conditional on that particular
original generic-type child's joint result. Keep the conditional interface in
later stages as well. Finite factoring, the relative theorem, and polymorphic
coherence remain unproved.

A second issue survives that split. A whole-Pi target capability does not
transport observations of its actual SOURCE codomain from a frozen anchor to
a new argument. Retain the domain/body results of original literal-Pi children
in the simultaneous fundamental induction, for both equality endpoints:

```text
Joint(H) and SourcePiFormation(SelfJoint, left)
         and SourcePiFormation(SelfJoint, right)
```

The checked raw `IsDefEqStrong.sourcePiFormation` theorem verifies structural
routing through the original rules. Its returned endpoint typing proofs are
not new original children on which to invoke the semantic theorem. The proposed
semantic payload must instead be populated by original child IHs. The telescope
accessor retains the tail's own capability as well as recursive Pi information;
the minor remains at its actual source prefix. Moving under later binders needs
semantic substitution projection or a proved source-weakening operation.

This is a requirement for the actual source body, not the previously retracted
demand for evidence about arbitrary frozen raw Pi prototypes.

The fixed-valuation application argument now has a conditional paper schedule:
choose existing function support; restrict argument support to the join of
supporting row inputs; use retained source-body IHs to transport codomain
observations to the same actual argument; join those observations and refine
their TYPE profile; retain result values from existing function rows. It must
also work for function-valued results and later dependent binders in the case
template. Neither source inputs nor result rows can be enlarged beyond the
fixed valuation to repair the argument.

The immediate unconstructed law is anchored `HasDom`/coverage, together with
its producer. Supporting rows must preserve admission at the SAME actual raw
argument: frozen-anchor equality and the lower-rank relation, in addition to
profile inequalities and retained outputs. A stronger coverage definition is
not sufficient without producing it for the source observations needed by the
joint theorem. This coupled call, including source-body transport and generated
case interpretation, is the first feasibility gate. The full grammar, relation,
joint induction, and head producers remain unconstructed.

The raw `CaseStep.of_type` integration was repaired and passed a focused audit
before the latest source-prefix refactor: no sorry sources, standard logical
axioms only. `SourcePiFormation` passed a focused build. The latest layout/prefix
refactor still needed its final integration result confirmed at this checkpoint.
None of these facts closed a production foundation admission.


## Checked intrinsic profiles, unresolved common-display producer

This checkpoint identified a precise unavailable comparison call. No production
foundation admission had been closed.

The repaired source-prefix integration passed. Its saved focused audit reports
no sorry sources for `sourcePiFormation`, `telescope`, `rhs_layout`,
`source_prefix`, and `CaseStep.of_type`; the last visits 3,420 declarations,
with only `propext` and `Quot.sound`. Raw endpoint formation is still not an
original semantic induction hypothesis on a synthesized typing derivation.

`Typing/AnchoredProfiles.lean` now constructs the finite grammar and intrinsic
typing/order by rank recursion. Function keys freeze raw domain, anchor, input,
and domain support. Coverage preserves exact keys while allowing larger output
and ambient domain support. Checked laws include finite joins, type enlargement,
value restriction, function-cover inversion, and `proof_empty`: a value typed by
a profile itself typed at the irrelevant sort has no atoms. These are intrinsic
facts; no raw-term logical relation or semantic fundamental theorem is defined.

Paper review proposes producing lambda covers from original domain/body children,
then interpreting application by retaining existing function outputs. Original
source-codomain results transport observations from the frozen anchor to the
actual argument; only type support is joined/refined. The substitution extension
must handle every needed domain observation, not only frozen support. Join that
new source-domain observation with the frozen one, use the original domain child,
and transport through the resulting enlarged type support. Each finite demand
may have its own proof extension. These semantic operations remain unproved.

The next unavailable operation is reconciling two independently produced Pi
displays for the same raw type. Choosing a common display within one witness does
not prove compatibility across witnesses used in type enlargement or composition.
The candidate needs forward amalgamation of their proof extensions and compatible
typed head displays, sufficient for the lower component paths actually consumed.
Whole-Pi equality followed by Pi inversion is circular here. Pure syntax
uniqueness of a head program does not supply typed-trace stability or guards.

The proposed simplification contracts native heads only at the first prefix
containing the major argument. Partial applications are interpreted pointwise
by the function relation; trailing arguments remain outside contraction. The
paper reviews found no required partial head-exposure consumer in this interface,
but adequacy for all actual primitive equations and converted caller types must
still be constructed. No closure theorem for every nondeterministic `FullWHRed`
step is required merely because the old architecture used it.

`Inductive/SaturatedNativeProgram.lean` implements pure metadata-selected syntax:
copy fields determined by actual indices; otherwise propose a fresh proof binder
at the equation domain instantiated by earlier captures. It records the saturated
prefix, trailing arguments, field instructions, captures, and resulting term.
The author reported a focused build; no final audit result was received before
the pause. Neither a fresh slot nor a proof major establishes that its domain is an
inhabited proposition. Generic proof selectors can fail typing at constrained
dependent indices, as in the two-family strengthening example. Typed replay must
produce the actual witnesses and index alignment from original premises.

Appending trailing arguments must retain the caller's type-conversion evidence.
Existing closed-telescope beta helpers can invoke admitted lambda/Pi inversion;
if replay needs such a helper, use original open-body typing instead. Do not
expand that helper library until its use in the central producer is concrete.

The first gate remains a checked coupled construction with its semantic evidence
produced, followed by removal of the selected admitted dependency from the actual
beta consumer. The intrinsic algebra, pure program, and paper schedules do not
pass it. A precise obstruction changing the construction is useful risk evidence;
more conditional infrastructure alone is not.

## 2026-09-28: checked trace comparison; eta changes the next construction

The preceding paper-only guard review did not close a foundation admission.
The following implementation closes the common-display subproblem for an
explicitly limited head fragment.

### Checked common-display producer

`CanonicalHeadTrace.lean` implements syntax-selected head beta, ordinary
registered definitions, and saturated native singleton programs. The output
contains the actual added telescope and result. Guards never choose a different
syntax step. The total `step_rename` theorem includes unsuccessful executions;
`Trace.rename` retains all fresh slots, and `Trace.terminal_unique` proves
literal agreement of terminating traces. Partial native heads stay stuck.
Ordinary constructor iota, quotient computation, abstract eliminators, and
projections are explicitly outside this file's dispatcher.

`CanonicalTraceAmalgamation.lean` distinguishes unrelated initial private
variables from corresponding slots created by the same trace. Its
`synchronizeTelescope` identifies each corresponding slot once in a common
context and produces actual split typed embeddings with the required `consN`
map equations. Merely disjointly merging the final contexts would leave two
copies of each proof slot and would not yield literal Pi agreement. The
construction allows dependent domains and data binders; it does not request
an unlifted domain typing in the original base.

`canonicalPiDisplay_common` in `CanonicalHeadComparison.lean` starts with two
actual initial interleaving histories, two traces from the respective lifts of
one source expression, and typing of their final telescopes. It constructs the
common context and literal equality of the lifted Pi domains and codomains.
The same construction separates Pi and sort exposures. It does not assume
whole-Pi equality or invoke inversion/uniqueness. Lower semantic capabilities
must subsequently move forward into this common context. It is still invalid
to semantically retract a private display component to a base prototype merely
because raw readbacks agree.

`CanonicalHeadRegistry.lean` supplies the machine's scope facts from an actual
`VEnv.WF'` declaration history and the native table's concrete registration
invariant. It adds no semantic producer callback or body-closure caller premise.
Typed guard availability and soundness of selected traces remain separate.

Combined focused build: **117 jobs, passed**. Focused transitive audit:

| Root | Dependencies visited | Sorry sources | Axioms |
| --- | ---: | ---: | --- |
| `CommonTarget.synchronizeBinder` | 2883 | 0 | `propext`, `Quot.sound` |
| `CommonTarget.synchronizeTelescope` | 2888 | 0 | `propext`, `Quot.sound` |
| `canonicalPiDisplay_common` | 3282 | 0 | `propext`, `Quot.sound` |
| `canonicalPiDisplay_ne_sort` | 3279 | 0 | `propext`, `Quot.sound` |
| `Trace.pi_unique_renamed` | 2296 | 0 | `propext`, `Quot.sound` |

The registry producer's roots also passed their focused audit with those same
two axioms. Reproduction files are `/tmp/canonical-head-comparison-audit.lean`
and `.out`; the audit traverses opaque theorem bodies. No new tests or final
full-branch audit/replay were run. No final foundation admission was removed.

### Precise native-guard provenance

The constructor-variable case can retain an observation/type-capability
isomorphism between the variable's assigned type and its unique lookup type in
the simultaneous Strong motive. The bvar case uses its original formation
child; conversion composes the original conversion child's result; endpoint
routing follows the original children in symm/trans/beta/eta/native/proofIrrel.
A generated `.hasType` proof must not become a new semantic induction argument.
For literal Pi formation, an arbitrary core payload must also provide endpoint
self-evidence; equality-child evidence alone does not imply self-evidence.

This remains a paper producer schedule. The crucial raw/semantic distinction
survives: arbitrary proof witnesses can be reused by raw typed substitution at
empty demand, but data fields need supported semantic domain alignment.

### Eta refutes the minimal literal-key grammar

If `rho(f)` contains `(a,p0,d) -> m` and `p0 <= p1`, unrestricted lambda
observation gives `lambda x. f x` a row `(a,p1,d) -> m` that literal-key variable
support cannot give to `f`. Same-support rekey repairs only this first issue.

Combining output observations creates a second issue. Two outer rows with
incomparable domain supports can output `fn j o0` and `fn j o1`. A fusion rule
makes their application observable at the SINGLE atom `fn j (o0 union o1)`.
Even lambda generation restricted to one output atom then combines the outer
supports. Same-support rekey and same-key fusion cannot recover that new outer
row from `f`. Arbitrary changed-support rekey is not justified either: target
capabilities do not manufacture a new observation of the actual source domain.

Two different constructions were considered. One uses finite semantic covers
by existing source type rows, rather than requiring a new value key in the
source Pi table. Its cover producer remains unproved. The narrower current
candidate DISTRIBUTES function output conjunction into separate atomic rows at
every rank, with no observation rule that merges several outputs into a single
function or Pi atom. This removes the particular fusion counterexample; the
existing `AnchoredProfiles` grammar has not yet been migrated to enforce it.

Exact source-support factoring must stop at a WHOLE variable observation,
including its rekeying, and replace it by reflexive lookup at its final demand.
Collecting only primitive lookup leaves fails for function-valued inputs: the
leaf demand may have a different key and may not be typed at the old frozen
support. Eta's compositional application then uses one old function row, that
whole argument observation, and target admission evidence, without an arbitrary
source result-type observation.

Native annotation provenance must be structural. The natural type of an index
is the fixed registered recursor telescope's domain instantiated with the actual
source prefix operands. The reconstructed field domain comes from the fixed
equation telescope and prior captures. Choosing an arbitrary assigned type from
a derivation in the enlarged source context is insufficient for erasure. With
the fixed templates, observations of `f.lift` inherit source weakening while
raw target anchors and guards remain unchanged. The semantic producer must
retain the ORIGINAL generic-type child at constDF/elimDF and its domain/body
payload through the application spine; newly synthesized prefix typing cannot
replace those IHs.

**Next gate:** construct observation-substitution factoring and the coupled
converted eta/beta/native producer with distributed atomic outputs and this
provenance. It must preserve the fixed valuation, handle function-valued inputs
and results, and justify every decrease. The source grammar and target relation
remain unconstructed. This is the current leading uncertainty, not permission
to fill surrounding profile libraries or unrelated proof holes.

## 2026-10-02: concrete support change; source rank gate

`AnchoredSemantics` now defines the target predicates by rank, before source
observations. Keys retain raw domain, anchor, and input demand; domain support
is existential typing evidence. Function outputs are single atoms. The relation
quantifies future typed insertions explicitly. Its term interpretation gives
each atom its own inhabited proof extension, so finite union does not assume
that independent unsaturated displays have a common semantic witness.

`AnchoredSupport.Related.retag` proves that a fixed value demand can change its
type support when the new support is intrinsically valid and has an actual
type capability. Its function case constructs new covering rows, compares
actual canonical exposures using `Exposure.samePi`, and uses generated
proof/future pushouts. All three output comparisons recurse on the smaller
output rank. Only operands genuinely lifted from the smaller context are
absorbed back into the proof-saturated relation; private displayed components
are never retracted semantically. The lower-rank premise of the internal
function lemma is discharged by the public rank induction.

The combined comparison/registry/support build passed (126 jobs). The support
root's audit visited 2,747 declarations with zero sorry sources and only
`propext`/`Quot.sound`. A later per-atom saturation adjustment also passed its
focused build (57 jobs). These are local results: no final foundation admission
has been removed, and the final full build/audit/replay has not been run.

Source-eta review found a dead-key defect in the first concrete relation.
For example, an anchor `Sort 0` with domain `Sort 1` and input demand
`sort true` can never be admitted. Universal function behavior was therefore
vacuous, while a source lambda could not observe its body at that anchor.
Function behavior now requires anchor self-admission in its base core context;
the support-change proof preserves that evidence unchanged and still audits.
The outer inhabited proof extension permits frame-dependent anchor evidence.

The next construction must distinguish available valuation from local binder
footprint. Factoring cuts at a WHOLE bound-variable observation, including any
rekey, and records its FINAL demand. Cutting at primitive lookup leaves repeats
the already rejected higher-order eta counterexample. External variable views
may still be supported by the original fixed valuation. Changing a raw domain
needs an actual binary type capability; changing an anchor additionally needs
the original codomain child's observation transfer. Raw conversion alone is not
the semantic producer.

There is also a concrete rank mismatch in `lambda x. x a`: uniform application
raises the rank of the function demand above the rank permitted for the lambda
input. Raising every rank together does not fix it. The current implementation
attempt adds explicit atomic padding, with bounded lower interpretation and
type-support decoding. Both introduction and elimination are required for beta.
Eta also needs the checked single-row commuting step between
`pad(fn key output)` and `fn(padKey key, pad output)`, together with the
corresponding Pi-cover change. Merely adding a padding constructor does not
establish that gate. Source observation factoring and the coupled original-child
producer remain unimplemented; native templates and missing head forms remain
separate obligations after feasibility is established.

### Checked padding and the next domain bridge

The explicit-padding implementation now passes. `Related.unpad` handles any
high-rank type support by decoding it, rather than requiring that support to be
syntactically padded. `Admitted.pad/unpad` therefore preserve the accepted
arguments. `PiWitness.rankShift` reuses the actual display and pads its lower
capabilities. The full `Related.rankShift_fn` maps the ENTIRE fixed type cover
before future worlds are quantified; different worlds may select different
covering Pi atoms. `Related.commute_pad_fn` combines unpadding and row shift.
No source observation or conversion producer is assumed in these theorems.

Combined focused build: 129 jobs passed. Updated transitive audits:

| Root | Visited | Sorry sources | Axioms |
| --- | ---: | ---: | --- |
| `Related.retag` | 2804 | 0 | `propext`, `Quot.sound` |
| `Related.rankShift_fn` | 2771 | 0 | `propext`, `Quot.sound` |
| `Related.commute_pad_fn` | 2772 | 0 | `propext`, `Quot.sound` |

Reproduction: `/tmp/anchored-padding-shift-audit.lean`. This closes the target
rank-adjustment calls, not source beta/eta observation factoring.

The next exact raw-domain rekey obligation is to combine binary code bridges
with different type supports, while typing the SAME fixed input demand. A new
Pi witness needs its local key-to-domain bridge and both self-body capabilities
at the selected output support; merely producing an endpoint bridge is too
weak. Local row-domain supports can vary across future worlds, so the result
must arise from a finite syntax-based support construction chosen beforehand.
Arbitrary code restriction along intrinsic domination is NOT available: a
smaller Pi domain may discard the original row's existential support.

Current feasibility work tests hereditary minimal typing supports and a
simultaneous focus/composition/transport induction. The difficult repairs must
recurse on actual lower-rank input/output demands. No such semantic producer is
checked yet, and it must not become a caller callback in the source grammar.

### Closed support, conversion, and transitivity (2026-10-02)

That support producer is now checked. `AnchoredSupportBasis` computes a finite
list of hereditary minimal supports, proves it inhabited from intrinsic typing,
and retains the constructor certificates and literal subprofile membership.
`AnchoredMinimalSupport` closes the full rank induction for focusing, symmetry,
minimal-first composition, and transport. The Pi constructors rebuild local
row-domain links at selected minimal supports; dependent composition retains
the actual displays and both self-body clauses. `TypeRelated.rekey_domain`
selects its support before any later caller domain or future context.

`AnchoredConversion` closes term conversion across binary raw-type capabilities,
including function-valued outputs, and proves `Admitted.rekey`. It uses actual
binary codomain evidence, not a raw conversion path as a semantic substitute.

Term transitivity exposed a further context issue: independently transporting
two chosen Pi exposures does not identify their old private variables. The
definition now requires full future code capability for non-function term
atoms. Function atoms transport a SINGLE self-display and its actual future
leg. `CoreRelated.future` then moves both saturated cores into the common
generated proof context; `Related.trans` closes by rank. This theorem requires
the concrete registry's scope facts, supplied by the existing history-derived
registry theorem. No arbitrary private-variable retraction is asserted.

Fresh focused build: 78 jobs. Audits after the definition change:

| Root | Visited | Sorry sources | Axioms |
| --- | ---: | ---: | --- |
| `Related.trans` | 3508 | 0 | `propext`, `Quot.sound` |
| `Related.convert` | 3536 | 0 | standard three logical axioms |
| `Admitted.rekey` | 3537 | 0 | standard three logical axioms |
| `TypeRelated.rekey_domain` | 3481 | 0 | standard three logical axioms |

`Classical.choice` enters finite intrinsic guard decisions in `Basis`, not a
semantic producer oracle. Source observation renaming still has to be proved
from its concrete grammar; target core transport does not supply that lemma.

### Next source eta gate: hereditary output changes

Whole-variable factoring resolves the direct eta row, but not a transformed
function-valued result. If the available demand of `f` is `fn k (fn j o)`,
observing `f x` and reanchoring its inner result to `fn j' o` produces the lambda
demand `fn k (fn j' o)`. Changing only the outer key cannot recover that demand
from `f`. This example already works with an empty inner input and beta-equal
anchors, so domain composition alone does not resolve it.

The current concrete construction is `AtomView`, whose constructors store
actual guards and whose `mapType` is computed before future arguments. A
`fn key view` copies each matching Pi row with its lower view's mapped output
support, retaining the old rows. Its paired code/term interpretation must close
by rank, with no interpretation callback stored in the view. Source `Obs.view`
can then preserve the old external footprint. This producer is in progress.

The eventual binder normalization must retain the rank even of an empty whole
variable demand. Erasing that grade would silently demand an unproved reverse
function-row rank shift. The original source observation grammar, normalization,
factoring, and coupled fundamental theorem remain unimplemented. No final
foundation admission has been removed by these target results.

### Closed views and the source certificate call (2026-10-02)

The full `AtomView` interpreter now closes by rank and proper subview size,
including domain rekeying and padding/function commutation. Its public code and
term roots each audit at 3,968 dependencies with no sorry sources and only the
standard three logical axioms. The focused build passes 88 jobs.
`AnchoredSourceObservation` adds the guarded finite core, the whole-local-demand
invariant (including empty grades), target transport, and the external-variable
nested-output eta example. That focused build passes 89 jobs. These do not yet
establish substitution factoring or the fundamental theorem.

The next source support call rules out a naive literal type-observation result.
If a term's source type is protected local `i`, a view may change its supporting
profile from `d` to `view.mapType d`; `Obs.local_whole` requires different
footprints for those two literal observations. A separate finite code
certificate can instead retain its computational observation leaves and apply
the checked code transformations above them. Lambda/Pi consumers must interpret
those leaves using the ORIGINAL formation child, without flattening the result
back to a protected-local observation. The source valuation must itself retain
available type-support certificates for its entries; semantic substitution
evidence alone cannot manufacture them.

`Related.codeInFrame` now extracts code evidence from any intrinsically sortable
term demand in an actual inhabited proof extension. It combines the finitely
many atom frames and descends through padding. Its 2,712-declaration audit has
no sorry sources and only `propext`/`Quot.sound`; the focused build passes 55
jobs. This exact leaf operation does not yet satisfy `PiWitness.rowBodies`,
which needs base-world code evidence after each arbitrary future argument.
The selected attempt reflects the deterministic trace through its initial
renaming, reconstructs the generated telescope using the actual proof
retraction, and commutes that initial insertion into the exposure's post-frame.
All private domains/bodies remain in the same final display context. This is a
specific absorption proof under construction, not an assumed general inverse
weakening law or permission to weaken the final foundation contracts.

### Original-child lambda integration and the beta resource obstruction (2026-10-02)

The absorption proof mentioned above is complete: it reflects the deterministic
trace and moves the initial inhabited insertion into the final display frame.
`TypeRelated.absorb` and `Related.code_of_sortable` provide code evidence in the
caller's world without retracting private domains or bodies. Reversible finite
profile views now support contravariant function-input adaptation. Variable
and application factoring normalize at a common grade, transform the whole
function, and lower it back; this also handles arbitrary output-view closures.
`Obs.eta_contract` transfers an eta expansion to its function at the same demand
and available valuation, using the ORIGINAL function-child Joint hypothesis.

The first lambda assembly exposed a false candidate induction invariant.
Availability of returned local leaves does not imply equality of the binder's
packed input. Requiring reversible equality of raw local footprints is also
false: `(lambda x:T. x) y` can observe `T` through the domain certificate while
its reduct observes only `y`. This persists when the domain support is minimal.
With empty input, `(lambda x:T. Sort0) y` can erase a wholly gratuitous domain
certificate. An unrestricted unused-resource constructor would break source
binder reflection and eta; it is not the adopted repair.

Checked repair components are now available. Atomic provenance follows each
surviving code demand to actual observation leaves and eliminates branches that
project to empty. Literal `CodeCert.select` compiles atomic/pruned certificates
back to the ordinary certificate grammar without reintroducing erased leaves.
The original argument and formation children produce argument evidence at a
chosen actual-domain support. Input enlargement is sound at a known literal
Pi type using actual domain code (`Related.literalInput`), while the earlier
arbitrary-type reversible view remains unchanged. These are components of the
source repair; a complete resource-correct source motive is still required.

The original-child lambda schedule is now implemented through its anchor and
argument probes. `Fits.push` obtains every local leaf from the fixed packed
input and lowers the actual A certificate to its grade. `Obs.lambda_type`
queries ORIGINAL Hbody at the anchor and constructs an actual source Pi
certificate containing the returned B certificate. `LambdaTypeResult.atArgument`
uses ORIGINAL HB to transfer that fixed B certificate and ORIGINAL Hbody to
relate both body endpoints to the same anchor. The package and its finite
valuation transport to future contexts without changing the support choice.
Original HAB also transfers actual source type certificates for conversion.

The required target beta expansion now closes by rank as `Related.headBeta`.
A single-universe `Exposure.sound` field would have required the very type
uniqueness theorem being constructed. Exposure instead retains an explicit
chain of typed conversion edges and formation of its final head. Each function
step casts along its chosen actual Pi display, aligns the dependent result with
original raw codomain formation, and calls the lower rank. The root audits at
3,256 dependencies, with no sorry and only `propext`/`Quot.sound`.

The remaining immediate work is the complete lambda semantic constructor and
source beta substitution/resource integration. The original-child hypotheses
in these helper theorems are not a proved global fundamental theorem. No final
foundation admission has been removed, and native head coverage and final
inductive integration still remain.
