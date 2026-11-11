# Strengthening under canonical `Eq`: a first-principles assessment (2026-11-10)

Outcome (updated 2026-11-11): **not settled; probably false.** There is a candidate
counterexample (§7): in a well-formed environment with canonical `Eq` and two looping
`mutualDef`s, `C E ≡ E` is derivable under a hypothesis `z : P` (machine-checked), and
`weakN_iff` fails there if it is not derivable without the hypothesis (machine-checked
implication). Non-derivability has a paper argument (§20 to §23) reached after five refuted
models; the last three independent reviews did not break it, one construction in it is
unwritten, and none of it is machine-checked. Sections 1 to 6 record the earlier analysis.
The reduction of §1 is checked and stands.

## 1. A normal form of the problem (needs canonical `Eq`)

Strengthening for every binder follows from strengthening for one closed proof binder.

* Any binder to a proof binder. Given `Γ, x : A, Δ↑ ⊢ s↑ ≡ t↑` with `A : Sort u`, put
  `P := @Eq (Sort u) (A → A) A`. In `Γ, x' : P` the term
  `@Eq.rec (Sort u) (A → A) (fun X _ => X) (fun a : A => a) A x'` has type `A`, so substituting
  it for `x` gives `Γ, x' : P, Δ↑ ⊢ s↑ ≡ t↑`. `A → A` is inhabited whatever `A` is, which is the
  point. Several binders are removed last first.
* Any proof binder to `x₀ : ∀ p : Prop, p`, by `x' := x₀ P`.

So the statement is equivalent to: **assuming `∀ p : Prop, p` creates no definitional equality
between terms that do not mention the assumption.** In that form every occurrence of the new
variable sits inside a proof subterm, the new context has a proof of every proposition, and the
only thing the variable can contribute to a derivation is intermediate terms containing proofs
that do not exist below. The ledger has a related "fresh equality-proof binder" step; I did not
find this exact reduction stated.

This reduction is in Lean: `Lean4Lean/Theory/Typing/Strengthening/ProofBinderReduction.lean`
defines `UniversalBinderStrengthening` (the one-binder statement for a binder of type
`∀ p : Prop, p`) and proves `strengthening_of_universalBinder`: it implies the one-binder
statement for every binder. One binder is the only case `IsDefEqU.weak'_iff` uses. The new
obligation is a special case of the old one, so it is strictly narrower; my judgment is that it
is true and open.

## 2. Why descending a confluence join cannot work as a method

Write `Ψ(R)` for: "the two terms reduce to normally equal terms, where every side condition
(guard of a singleton unfolding, common type of two compared proofs, equality of two lambda
domains, the typing used by an eta step) is taken from `R`". Church-Rosser plus soundness says
definitional equality in any context is a fixed point of `Ψ`. For terms not mentioning the new
variable, reducts do not mention it either (choosing eta-expansion domains from the term's own
type), and each side condition is again a pair of such terms. So equality above, restricted to
lifted terms, and equality below are two fixed points of the same operator.

`Ψ` has more than one fixed point in this calculus, because `mutualDef` admits loops:

    H : ∀ n : Nat, n = 0 := fun n => H n
    a : Nat := @Eq.rec Nat a (fun _ _ => Nat) 0 0 (H a)

`a` unfolds to a cast whose singleton step fires exactly when `a ≡ 0`. The equation supports
itself: adding it is consistent with every closure property that Church-Rosser, uniqueness of
types and injectivity express, yet no rule ever introduces it (I believe; not proved). The same
happens through lambda domains with `W : Nat → Type := fun n => W n → Nat` and
`Om : Nat := (fun w : W Om => w w) (fun w : W Om => w w)`, which is the shape behind the
branch's `RecursiveLoopSeparation`.

Consequence: an argument that takes the join of a lifted equation and recurses on its side
conditions is an argument about an arbitrary fixed point of `Ψ`, and for those the conclusion
is false. Routes A and B, `PropFront`/`LamDomainFront`/`KeyFaithful`, and any rank on joins are
all of this kind. The residue "matched beta-redex pair whose arguments are lambdas" is where
the recursion visibly has no measure, but the cause is general. What distinguishes the larger
context from a self-supporting extension is only that its equations have finite derivations,
so a proof has to consume the derivation, not the join.

The same remark says where a counterexample would have to come from: a rule instance, not a
cycle. I went through the rules in the normal form of §1 (proof irrelevance, eta, structure
eta, unit-like, iota, singleton unfolding with extraction, projection) looking for one whose
use with a non-existent proof cannot be simulated below, and found none once `Eq` supplies
extraction. I think the statement is true.

## 3. What would prove it

A system of **hereditarily certified joins**: an inductive judgment in which every side
condition of a reduction step or of a normal comparison is a sub-derivation of the same
judgment, with types inferred from the subject terms (so typing side conditions are joins
between an inferred type and the required shape). For it:

1. Descent is a plain structural induction. A certificate for two lifted terms mentions only
   lifted terms, and each sub-certificate is smaller.
2. Completeness for the declarative judgment, in one fixed context, is the real theorem. It is
   a statement about a single context and does not mention strengthening. It requires
   confluence, subject reduction, Π-injectivity and uniqueness of types to be proved as
   operations on certificates, so that every fact the confluence proof takes from typing
   (the domain equality in the eta/beta overlap is the main one) arrives with a certificate.

This is the architecture of Adams (2006) and Siles and Herbelin (2012, "Pure Type System
conversion is always typable"): typed parallel reduction whose premises are again typed
reductions, with confluence by induction on derivations, valid for non-normalising systems.
They treat beta only. Eta, proof irrelevance and guarded singleton steps are not covered by
that work, and Church-Rosser for beta-eta on well-typed terms of non-normalising pure type
systems was, as far as I recall, left open by Geuvers, so step 2 is research, not
transcription. Neither paper is cited in the ledger. The branch's `domain_join_complete`
certifies lambda domains but leaves typing and guard side conditions declarative, which is
why its joins do not descend.

I did not find a way to obtain step 2 from the existing theorems used as black boxes; §2 is
the reason to expect there is none.

Which conditions need a certificate. `DomainNormal.descend` (already on the branch) lowers a
final comparison using only typings below, so proof types and lambda domains in positions with
a known common type need nothing. Going through the step kinds of `FullStep` the same way, the
typing premises of function eta and structure eta are recoverable below wherever they are
needed (common-type positions, projection majors, partial applications of a recursor, whose
type is syntactically a Π). What is left is exactly:

1. the index guard of a singleton unfolding (`UnfoldingCheck.major_prop`/`recursor_lhs`): an
   equation between an index argument and the constructor's index pattern, both lifted;
2. the domains of two lambdas at the heads of matched beta redexes, when contracting the
   redexes does not terminate. For `(fun w : A₁ => w w) (fun w : A₁ => w w)` against the same
   term with `A₂`, the two are convertible below exactly when `A₁ ≡ A₂` is, so no rearrangement
   of the join avoids the domain equation.

`domain_join_complete` does not give (2): its domain certificates are `refl` after a typed
reannotation step, which moves the same equation into the typing premise of that step.

Two other proof shapes, and where each stops:

* Induction on the size of the derivation above. Composing the conversions inside the premises
  of one rule gives a smaller derivation, which handles proof irrelevance against the new
  variable. It stops at application: the premises type the function at a Π type that may
  mention the variable, and recovering a Π type below needs Π-injectivity with a bound on the
  size of the component derivations, which the confluence-based proof of injectivity does not
  give.
* Induction on the derivation above, relating each term to terms typed below with the same
  proof erasure (erasure is injective up to conversion on non-proof terms typed below). It
  stops at intermediate terms with no such counterpart, for example a beta expansion whose
  argument is a proof of a proposition unprovable below. Reducing above first restores
  existence, but then an iota step above at a constructor built from the new proof must be
  mirrored below by a singleton unfolding, and its guard (1) has no sub-derivation, because the
  typing of a reduct is not part of the derivation being inducted on.

Both stop at the same place the join route does: a condition on a reduct whose justification
is not a sub-object of anything the induction controls. That is the content of step 2.

## 4. Things that do not help

* Erasing lambda annotations: false (two loops with the same erasure and type), as the ledger
  already records.
* Erasing proofs: sound and injective on non-proof terms of the smaller context, and it removes
  the variable of §1 entirely, but conservativity of the erased theory is the same statement.
* Adding an inhabitant of every type (a looping `bot : ∀ A, A`) makes strengthening trivial by
  substitution; removing it again is the same statement. Building it into the abstract
  environment would make the checker theorem `sorry`-free and empty.
* An algorithmic invariant for the caches: individual runs never consult an unused binder, but
  the equivalence manager closes facts transitively through terms that mention it, which is
  the declarative statement again.

## 5. A cheaper theorem that may be worth having

Loops in `mutualDef` are the only source of the cycles in §2 that I could construct. The
executable only installs such blocks for unsafe declarations. If the checker verification can
be stated for environments whose safe part has no such block, the obstruction of §2 would need
a different witness, and the "holds in every normalising fragment" result may apply to more
than it currently does. I have not checked what the safe fragment needs (proof-level
non-normalisation remains), so this is a question, not a claim.

## 6. Second pass (2026-11-11): what the branch already has, and the exact missing theorem

Reading `GuardedSingletonPrefixDescent.lean` and `Confluence/JoinableTyping.lean` changes the
picture of §3 in two ways.

**The descent half exists.** `prefix_descend` lowers a singleton prefix step whose single
family guard is certified by any comparison `Cmp` with `EndpointDescent Cmp`;
`DomainNormal.descend` lowers the final comparison. What is open on the branch is
`FamilyCertificateCoverage Cmp` for a `Cmp` that descends, that is, a finite certificate for
every guard that holds. This is the hereditary-join completeness of §3, restricted to the one
condition that matters most.

**Why no black-box use of confluence can give coverage.** A term can contain a singleton
redex whose guard happens to hold for reasons unrelated to how the term arose (the guard is not
required by typing). `FullReduction.church_rosser` is free to contract such a redex while
closing a peak, and then nothing certifies its guard. Coverage therefore needs a confluence
proof in which the steps that close a peak are known to descend from the steps of the peak.
I tried five ways of avoiding this (a semantic permission predicate closed under all
transports; forward-only certificates; erasure realizers; derivation size; minimal failing
pair by term size or join length). Each fails at the same point: the certificate of a
mirrored or residual step is produced by an opaque lemma and is not a sub-object of the
certificate being inducted on.

**A design that does give provenance, using what is there.** The existing confluence proof is
already an induction on strong derivations (`IsDefEqStrong.church_rosserJ_of`) whose
transitivity case goes through the abstract criterion of `LevelledConfluence.lean`. That
criterion's `claim` counts steps: when one branch of a peak has no step of the top level, the
other branch closes using lower steps only. This is the provenance statement, for whatever is
placed at the top level. So:

1. Add a permission predicate on prefix-unfold instances to `DeltaPar.delta` and
   `FullStep.delta` (a `Params` field with the closure properties the peak lemmas use: argument
   development at each level, mirror through `NormalEq₀`, weakening, instantiation, context
   conversion). `PrefixUnfolding/` is untouched: its transport lemmas are used as they are.
2. Take the permission to be the closure under exactly those transports of *seeds*, a seed
   being an instance whose family guard has a join by reductions permitted at a lower stage.
   Closure holds by construction. Stage `s` permissions are cumulative.
3. Prove the two-predicate form of the three delta peak lemmas (`DeltaPar.peak`,
   `DeltaPar.parRed_peak`, `EtaPar.deltaPar_peak`): against a step permitted at a lower stage,
   the higher side closes by lower-stage steps. The proofs are the existing ones with the
   predicate threaded through.
4. Coverage (`Confluence/SingletonPatCoverage` and the quotient analogue) produces seeds: it
   already builds the unfolding check from joins of `HasTypeJ`, which are the induction
   hypothesis.
5. Descent, by induction on the stage: an instance permitted at stage `s`, any substitution
   instance of it, any reduct, any term of the smaller context normally equal to that reduct,
   is valid below. The seed case closes the peak between the seed's join (stage below `s`) and
   the given reduction; by 3 the steps on the given side are of lower stage, so their mirrors
   below are valid by the induction hypothesis.

Open points in this design, which I have not resolved: eta steps sit above delta in the
existing level order while a seed's join may use eta, so the counting in 3 has to be stated for
delta stages in the presence of eta steps on both branches; the typing premises of eta and
structure-eta steps and of reannotation need either the same treatment or the recovery
argument of §3; and step 5 needs the mirror lemmas to relate a term of the smaller context to
a reduct that may contain proofs with no counterpart below.

Size: `LevelledReduction.lean` (4241 lines), the delta parts of `FullReduction.lean` and
`ChurchRosser.lean`, the coverage files, and a new descent file. This is a multi-week
formalisation at the rate this branch has moved, with the open points above as real risk. It
was not started.

## 7. A counterexample (2026-11-11): Klop's example lives in this calculus

Thinking about the gap of §6 shows it cannot be closed, because the thing it asks for is false.
Hereditary certificates do not exist in general, and strengthening itself fails, for
well-formed environments with canonical `Eq` that contain a looping `mutualDef`.

**The mechanism.** Klop (1980) showed that the λ-calculus with a non-left-linear rule
`D x x → E` is not confluent: with `C x → D x (C x)` and a fixed point `A → C A`, one gets
`A →* E` and `A →* C E`, and `C E` reaches `E` only if `C E` and `E` are already convertible.
In this calculus `Eq.rec` at a constant motive is such a rule,
`@Eq.rec T a (fun _ _ => T) E b h ≡ E` exactly when `a ≡ b` (proof irrelevance turns `h` into
`Eq.refl a`, then ι), and `mutualDef` supplies `C`. Declarative equality is transitive by fiat,
so `C E ≡ E` is derivable whenever a fixed point of `C` is available as a middle term, and is
self-supporting otherwise. A fixed point that needs a hypothesis is available above a binder
and not below it.

**The environment.** Canonical `Eq`, four axioms and two looping definitions:

```text
T   : Type
E   : T
P   : Prop
H   : ∀ x y : T, x = y
C   : T → T := fun x => @Eq.rec T x (fun _ _ => T) E (C x) (H x (C x))
Fix : P → T := fun p => C (Fix p)
```

**Above** (`z : P`): `Fix z ≡ C (Fix z)` by unfolding, so the `Eq.rec` in `C (Fix z)` has
definitionally equal endpoints and computes to `E`; hence `Fix z ≡ E`, and
`C E ≡ C (Fix z) ≡ Fix z ≡ E`. The terms `C E` and `E` are closed.

**Below** (empty context): `C E` unfolds to an `Eq.rec` with endpoints `E` and `C E`. It
computes only if `C E ≡ E` already holds, and `Fix` cannot be applied without a proof of `P`.

**What is checked in Lean** (`Strengthening/KlopCounterexample.lean`, no `sorry`, axioms
`propext`, `Classical.choice`, `Quot.sound`):

* `exists_klopEnv`: every well-formed environment with canonical `Eq` in which the six names
  are fresh extends to a well-formed environment with canonical `Eq` containing these
  declarations (`KlopEnv`).
* `KlopEnv.above`: in such an environment, `[P] ⊢ C E ≡ E`.
* `KlopEnv.not_strengthening`: if `C E ≡ E` is not derivable in the empty context
  (`KlopEnv.Separated`), then the statement of `IsDefEqU.weakN_iff` is false for it.

**What is not checked: the separation below.** Argument, on paper. Take the base environment
to consist of `Eq` alone and interpret the calculus in sets equipped with a partial
equivalence relation, definitional equality being identity of elements and `Eq a b` being
"`a` and `b` are related":

* universes and `Prop` carry the discrete relation, Π-types the pointwise one, and the elements
  of a Π-type are the relation-respecting functions. Consequently every family of types over a
  type with the total relation is constant;
* `T` is `ℤ/3` with the total relation, `E` is `0`, `P` is empty, `H` is the trivial proof;
* `Eq.rec α a M m b h` is `m` when `a = b`; otherwise it is `a + 1` when `α` and the fibre
  are both `T`, and `m` in every other case. The fibres at `a` and `b` are the same set, the
  result is related to `m`, and the ι rule and its proof-irrelevant instances hold because
  definitionally equal endpoints are identical;
* `C` is `x ↦ x + 1`. It satisfies its defining equation: `x ≠ x + 1`, so the right-hand side is
  the junk value `x + 1`;
* `Fix` is the unique function on the empty set, and its defining equation holds between
  functions on the empty set.

Every rule of `IsDefEq` is sound for this interpretation (β, η, proof irrelevance, the two
`extra` equations, the ι rule of `Eq.rec`; the environment has no structures or quotients),
and `C E` is `1` while `E` is `0`. The context `[P]` has no valuation, which is why the
equation above is not contradicted. This is a setoid-style model in which `T` is propositionally
a subsingleton and definitionally has three elements. It is not formalised; a formal proof
needs either this model in Lean or a syntactic argument (collapse of binders of type `P`, then
stratification of the unfoldings of `C`).

**Consequences.**

* `IsDefEqU.weakN_iff` is false for well-formed environments with canonical `Eq`, as the
  theory stands, subject to the separation above. Adding `HasCanonicalEq` to the hypotheses
  does not rescue it; canonical `Eq` is what makes the example work.
* Hereditary certificates (§3, §6) do not exist even in one context: in an environment with a
  closed fixed point `A := C A`, the equation `C E ≡ E` is derivable through `A` and has no
  well-founded join. This is why `FamilyCertificateCoverage` resisted proof.
* The fixed-point test of §2 was the right diagnosis and the wrong conclusion. I argued there
  that a self-supporting cycle cannot be grounded above only. It can: transitivity through a
  term that exists only above grounds it.
* Every ingredient is needed: a non-left-linear computation rule (`Eq.rec`, or any singleton
  with a repeated index), proof irrelevance, and a definitional fixed point guarded by an
  uninhabited type. In an environment whose definitions terminate there is no `C` and no
  `Fix`. The executable sends looping blocks to the kernel only for unsafe declarations, so a
  statement restricted to environments without `mutualDef` is not refuted by this example;
  whether it is true is open, and the earlier "holds in every normalising fragment" result
  points that way.
* The real kernel does not find the derivation above (it overflows on `Fix z ≡ E`), so this is
  a statement about the declarative theory, not a demonstrated unsoundness of the caches.

## 8. The separation below, in detail (paper proof)

Claim. Let `env` be the environment of §7 built over a base containing only the inductive
declaration of `Eq` (constants `Eq`, `Eq.refl`, `Eq.rec`, the ι rule of `Eq.rec`, no
projections, no other definitional equation). Then `[] ⊢ C E ≡ E` is not derivable.

No argument that uses only the existing confluence, uniqueness and rigidity theorems can prove
this: those hold in every context, and the equation is derivable in the context `[P]`. The
proof has to use that `P` has no closed proof, which is a semantic fact. So it is a model.

### 8.1 The model

A first version of this section interpreted every inhabited proposition by the same one-point
set. That is not enough: the ι rule of `Eq.rec` fires on a redex whose major premise is
syntactically `Eq.refl`, and with one-point propositions the model cannot tell that the two
endpoints of such a redex are identical, only that they are related. The model below records
this in the proof itself.

Work in ZFC with countably many inaccessible cardinals `κ₀ < κ₁ < …`, as in Carneiro's model.

*Values.* Data values are ordinary sets. *Proof values* are tokens `refl c` (one for each
data value `c`), `junk`, `⋆`, and functions all of whose values are proof values. Proof
values are disjoint from data values (by tagging).

*Semantic types.* A *proposition* is a set with at most one element, which is a proof value.
A *data type* is a pair `(X, ≈)` of a set of data values and a partial equivalence relation;
its elements are the `x` with `x ≈ x`. Two propositions are related when both or neither is
inhabited; a data type is related only to itself.

* `⟦Prop⟧` is the set of propositions; `⟦Sort (n+1)⟧` is the set of data types in `V_κₙ`,
  together with the one-point set `{⋆}`.
* `⟦∀ x : A, B⟧ρ`, by cases on `𝔸 = ⟦A⟧ρ`:
  * `𝔸` an empty proposition: `{⋆}`;
  * `𝔸` an inhabited proposition with element `t`: `⟦B⟧ρ[x ↦ t]`. A function out of a
    proposition is identified with its value;
  * `𝔸` a data type and all `⟦B⟧ρ[a]` propositions: the set containing the function
    `a ↦` (the element of `⟦B⟧ρ[a]`) if every `⟦B⟧ρ[a]` is inhabited, and `∅` otherwise;
  * `𝔸` a data type and the `⟦B⟧ρ[a]` data types: the functions `f` on the elements of `𝔸`
    with `f a` an element of `⟦B⟧ρ[a]` and `a ≈ a' ⟹ f a ≈ f a'`, related pointwise.
* `⟦fun x : A => b⟧ρ` is `⋆`, `⟦b⟧ρ[x ↦ t]`, or the function `a ↦ ⟦b⟧ρ[a]`, by the same cases.
  `⟦f a⟧ρ` is `⟦f⟧ρ` when `⟦a⟧ρ` is a proof value and `⟦f⟧ρ (⟦a⟧ρ)` otherwise.
* `⟦@Eq α a b⟧` is `{refl a}` if `a = b`, `{junk}` if `a ≈_α b` and `a ≠ b`, and `∅`
  otherwise. `⟦@Eq.refl α a⟧ = refl a`.
* `⟦@Eq.rec α a M m b h⟧`: if the result type is a proposition, its element. Otherwise, `m`
  if `h` is a `refl` token; if `h = junk`, it is `a + 1` when `α = ⟦T⟧` and the fibre is
  `⟦T⟧`, and `m` in every other case.
* `⟦T⟧ = (ℤ/3, total relation)`, `⟦E⟧ = 0`, `⟦P⟧ = ∅`, `⟦H⟧ x y =` the element of
  `⟦@Eq T x y⟧`, `⟦C⟧ = x ↦ x + 1`, `⟦Fix⟧ = ⋆`.

A valuation assigns to each variable an element of the denotation of its type. Two valuations
are related when their data components are related; proof components are unconstrained.

### 8.2 Soundness

Statement, by induction on derivations: if `Γ ⊢ a ≡ b : A` then for all related valuations
`ρ`, `ρ'` of `Γ`:

1. `⟦A⟧ρ` is a semantic type and `⟦A⟧ρ`, `⟦A⟧ρ'` are related (equal, for data types);
2. `⟦a⟧ρ` and `⟦b⟧ρ` are elements of `⟦A⟧ρ` and `⟦a⟧ρ = ⟦b⟧ρ`;
3. if `⟦A⟧ρ` is a data type, `⟦a⟧ρ ≈ ⟦a⟧ρ'`.

Clause 1 makes data-type families over `T` constant, and makes a data type independent of
which proof inhabits a proposition it mentions.

Rule by rule.

* `bvar`, `sortDF`, `constDF`, `symm`, `trans`: immediate. `defeqDF`: the hypothesis gives
  `⟦A⟧ρ = ⟦B⟧ρ`.
* `lamDF`, `forallEDF`, `appDF`: by the cases of the definition, using clause 3 for the body
  to see that the function respects the relation and clause 1 to see that the codomain does
  not depend on the choice of proof or of related argument.
* `beta`, `eta`: by the substitution lemma. For a proposition domain, the argument denotes the
  element of the proposition, which is what the abstraction was evaluated at.
* `proofIrrel`: a proposition has at most one element.
* `extra` for `C`: the right-hand side denotes `x ↦ ⟦Eq.rec T x M E (C x) (H x (C x))⟧`. The
  endpoints `x` and `x + 1` differ, so `H x (C x)` denotes `junk`, `α = ⟦T⟧` and the fibre is
  `⟦T⟧`: the value is `x + 1 = ⟦C⟧ x`.
* `extra` for `Fix`: both sides denote `⋆`, because `⟦P⟧` is empty.
* `pat` (the ι rule of `Eq.rec`): the major premise denotes a `refl` token, so the redex
  denotes `m`. No inversion of the typing is needed.
* The derived K instances are sound because they are derived: if `a ≡ b` then `⟦a⟧ = ⟦b⟧`,
  so `⟦@Eq α a b⟧ = {refl a}` and every proof of it denotes `refl a`.
* `Eq.rec` is type correct and respects relations. Let `h` be an element of `⟦@Eq α a b⟧`, so
  `a ≈ b`. For a data motive, `M a` and `M b` are related data types, hence equal, and `m` is
  an element. The value is `m` or `a + 1`, the latter only in the fibre `⟦T⟧`, whose relation
  is total; so it is an element related to `m`, and related inputs give related outputs.
* `projDF`, `projIota`, `structEta`, `unitLike`: no instance, the environment has no
  projection entry.
* Constants are elements of their types: `C` respects the total relation on `ℤ/3`; `H` is the
  unique element of a proposition; `Fix` is `⋆`, the element of `⟦P → T⟧ = {⋆}`.

### 8.3 Conclusion

At the empty valuation `⟦C E⟧ = 1` and `⟦E⟧ = 0`, so `[] ⊢ C E ≡ E` is not derivable. The
context `[P]` has no valuation, so the derivation of §7 is vacuously sound, as it must be.

Points a formalisation would have to make precise: the universe hierarchy (inaccessibles are
used only for closure of universes under Π), the substitution and weakening lemmas, and the
bookkeeping of the two kinds of value. None is specific to the example. This model has not
been machine-checked, and its first version had a gap (above); treat the separation as
argued, not proved.

## 9. Plan for a machine-checked separation: a term model

The set model of §8 needs universes closed like inaccessibles, which Lean supplies only for an
externally fixed number of levels. The model below has the same content with closed terms in
place of sets, so every semantic type is countable and no size question arises. Nothing in this
section is implemented.

**Why no cheaper route exists.** Any proof of the separation must use that `P` has no closed
proof, so it proves a consistency statement for the environment and cannot come from the
confluence, rigidity or injectivity theorems, which hold in every context (`IDEAS.md`,
2026-11-11, lists the five shortcuts tried). Proof irrelevance cannot be modelled without
types, which rules out untyped domain models; the uniformity of a recursor in its motive rules
out a translation into an environment where `T` has constructors.

**Ingredients.**

1. *Inventory.* A predicate on environments saying that the constants are exactly `Eq`,
   `Eq.refl`, `Eq.rec`, `T`, `E`, `P`, `H`, `C`, `Fix` with the stated types, the definitional
   equations are exactly those of `C` and `Fix`, the only registered pattern is the ι rule of
   `Eq.rec`, and there is no projection entry. The separation is proved for every environment
   with this inventory; that a well-formed one exists is a separate obligation (the repository
   obtains canonical `Eq` only through the checker verification, so it needs a direct
   construction of the `Eq` declaration).
2. *Weak head reduction* on closed terms: β, unfolding of `Fix`, and ι for `Eq.rec` at a
   syntactic `Eq.refl`. `C` is not unfolded. This relation is defined before everything else,
   so later definitions may use its negation.
3. *Values.* `Val t i` for a closed term `t` and `i : ℤ/3`, inductively: `E ↦ 0`;
   `C t ↦ i + 1` if `t ↦ i`; closure under weak head expansion; and for
   `Eq.rec α a M m b h` with `α` reducing to `T`, `a ↦ i`, `b ↦ j`: the value of `m` if
   `i = j`, and `i + 1` if `i ≠ j` and `h` does not reduce to an `Eq.refl`. A redex with
   distinct endpoints whose proof reduces to `Eq.refl` has no value; this is what makes the ι
   rule sound without inverting a typing.
4. *Semantic types.* One inductive predicate over all universe levels relating a closed type
   term to a pair of partial equivalence relations on closed terms, a fine one (definitional
   equality) inside a coarse one (propositional equality):
   * `T`: fine is equality of values, coarse relates all terms with a value;
   * `Eq α a b`: inhabited when `a`, `b` are coarsely related; its members are the closed terms
     `h` such that, if `h` reduces to an `Eq.refl`, then `a`, `b` are finely related; all members
     are related;
   * `P`: empty. Other propositions: empty or full, by the usual clauses;
   * `∀ x : A, B`: functions taking finely related arguments to finely related results and
     coarsely related arguments to coarsely related results, where the fibres over finely
     (coarsely) related arguments are finely (coarsely) equal types;
   * `Sort n`: type terms with an interpretation at level `n`, fine and coarse type equality;
   * a stuck `Eq.rec` in a data type other than `T` behaves as its minor premise.
5. *Soundness*, by induction on `IsDefEq`: under finely related closing substitutions the two
   sides are finely related members of the interpretation of the type, and under coarsely
   related ones coarsely related.

**Obligations, in order.** Each is a statement about the definitions above and does not
depend on the open `sorry`.

* `KlopModel.red_deterministic`, `KlopModel.val_functional`.
* `KlopModel.interp_functional`: a type term has at most one interpretation; symmetry and
  transitivity of both relations; closure under weak head expansion.
* `KlopModel.sound`: the statement of item 5, one case per rule of `IsDefEq`. The cases for
  projections, structure eta and unit-like types are vacuous by the inventory.
* `KlopModel.separated`: `Val (C E) 1`, `Val E 0`, hence `KlopEnv.Separated`.
* `exists_eqEnv`: a well-formed environment with canonical `Eq` and the base inventory.

Risks I can see: the interaction of the two relations at Π-types and universes (every lemma is
proved twice), impredicative quantification over a larger universe inside the single inductive
predicate (positivity holds, functionality has to be proved for all levels at once), and
proofs whose weak head reduction does not terminate (item 3 treats them as not reducing to
`Eq.refl`, which is sound as far as I can see). The size is that of the existing observation
model, several thousand lines.

## 10. The term-model plan of §9 is unsound as written (2026-11-11)

§9 item 3 reads the major premise of an `Eq.rec` off the raw term (does it reduce to
`Eq.refl`?). That is incompatible with proof irrelevance. Witness, all typed in the
environment of §7:

```text
m  := fun h' : C E = E => @Eq.rec T (C E) (fun _ _ => T) E E h'     : C E = E → T
M  := fun (y : T) (_ : C E = y) => y = E → T
t  := @Eq.rec T (C E) M m E (H (C E) E)                              : E = E → T
```

`t (Eq.refl E)` and `t (H E E)` are definitionally equal by proof irrelevance and congruence.
`t` is a transport of `m` along a proof of a false-in-the-model equation, so in any semantics
where it behaves as `m`, the first becomes an ι redex with value `⟦E⟧ = 0` and the second a
stuck `Eq.rec` with distinct endpoints, value `⟦C E⟧ + 1 = 2`. `KlopModel/Val.lean` has
exactly this defect and is marked accordingly; `Red.lean` and `Val.lean` are not on the path
to the separation.

The set model of §8 is not affected: there a function out of a proposition is identified with
its value at the unique proof, so `⟦t⟧ = ⟦m⟧ = 2` and applying it to any proof returns `2`.
What this shows about a formalisation:

* the interpretation has to be type-directed at binders and applications over propositions
  (whether a domain is a proposition is a semantic fact; it is not computable from the raw
  term, because a type can be a transport of `Prop`);
* proofs of an equation over `T` must denote a token determined by the proposition, and
  everything else about proofs must be invisible to data.

An operational semantics on raw terms provides neither. A relational, type-directed
semantics over closure values might, with the interpretation of terms and of types defined
together; I have not found a formulation I trust, having now made three design errors on this
model (one-point propositions in §8's first version, the raw-term major here, and the
untyped classification of proofs considered and rejected while writing this).

Status of the separation: paper proof by the set model of §8, checked only by me, with the
history above as a reason for caution. A machine-checked version is a research-scale
formalisation and I do not have a validated design for it.

## 11. Review of §8 and a repaired model (2026-11-11)

An independent adversarial review of §8 found it **not well defined**. Confirmed flaw: with
proof values `refl c` for every data value `c`, and function-valued proofs, `⟦Prop⟧` is not a
set. `∀ p : Prop, p → p` denotes `{f}` with `dom f = ⟦Prop⟧ ∋ {f}`, contradicting foundation,
and `@Eq (Type 1) Type Type` denotes a singleton of rank above the first universe. So §8.2's
"`sortDF`: immediate" is wrong. The review also found the Π clause undefined for families
with mixed proposition and data fibres (`∀ p : Prop, p → T`), ambiguity in what counts as a
member of a universe, and a disagreement between §7 (discrete `Prop`) and §8. It found no
equation with two different denotations, and confirmed the derivation in the larger context.
**The separation is therefore unproved by §8.** What follows is a repair; it has not been
reviewed.

### 11.1 What the tokens were for, and how to do without them

The tokens existed to make the ι rule sound without inverting the typing of the redex, and
they are the source of every problem above. The repair removes them. All proofs denote one
value `⋆`, `Eq.rec` decides by its endpoints, and the fact that a redex with major `Eq.refl`
has identical endpoints is obtained from a semantic typing predicate that is hereditary in the
term, so that it is available from the typing premise of the `pat` rule.

### 11.2 Codes

Semantic types are *codes*, compared by identity, each with a set of elements `El` and a
partial equivalence relation on it.

* Proposition codes: `⊥` with `El = ∅`; `⊤`, `R`, `J` with `El = {⋆}`. The set of these four
  is `El(prop)`. `R` and `J` are the codes of true and of false-but-inhabited equations over
  `T`; they differ only as codes.
* `T`: `El = ℤ/3`, total relation.
* `pi(𝔻, 𝔹)` for a code `𝔻` and a function `𝔹` from `El 𝔻` to codes: if every `𝔹 d` is a
  proposition code, the code is `⊤` when all are inhabited and `⊥` otherwise (so the result
  is one of the four proposition codes and proofs stay small). Otherwise it is the formal
  pair, with `El` the functions `f` on `El 𝔻` with `f d ∈ El(𝔹 d)` that respect the
  relations, related pointwise.
* `univ n` for `n ≥ 1`: `El` is the set of codes in `V_κ(n-1)`; `univ 0 = prop`.
* A relation `~` on codes: the least congruence with `⊤ ~ R ~ J`; `pi(𝔻, 𝔹) ~ pi(𝔻', 𝔹')` when
  `𝔻 ~ 𝔻'` and `𝔹 d ~ 𝔹' d'` for related `d`, `d'`. Related codes have the same `El` and the
  same relation. `~` is the relation of `univ n` and of `prop`.

### 11.3 Interpretation of terms

Compositional on raw terms, at a valuation:

* `⟦Sort ℓ⟧ = univ ℓ`; `⟦∀ x : A, B⟧ = pi(⟦A⟧, d ↦ ⟦B⟧[d])`; `⟦fun x : A => b⟧` is the
  function `d ↦ ⟦b⟧[d]` on `El ⟦A⟧`, or `⋆` if all its values are `⋆`; application is
  function application, and `⋆` applied to anything is `⋆`.
* `⟦@Eq α a b⟧`: if `⟦α⟧ = T`, then `R` when `⟦a⟧ = ⟦b⟧` and `J` otherwise; for any other
  `⟦α⟧`, `⊤` when `⟦a⟧`, `⟦b⟧` are related and `⊥` otherwise. `⟦Eq.refl α a⟧ = ⋆`.
* `⟦@Eq.rec α a M m b h⟧`: `⋆` if the fibre `⟦M b h⟧` is a proposition code; otherwise `⟦m⟧`
  if `⟦a⟧ = ⟦b⟧`; otherwise `⟦a⟧ + 1` if `⟦α⟧ = T` and the fibre is the code `T`; otherwise
  `⟦m⟧`. The proof `h` is not consulted.
* `⟦T⟧ = T`, `⟦E⟧ = 0`, `⟦P⟧ = ⊥`, `⟦H⟧ = ⋆`, `⟦C⟧ = x ↦ x + 1`, `⟦Fix⟧ =` the empty function.

### 11.4 Hereditary semantic typing

`Sem(e, 𝔸)`, by recursion on the raw term `e`, at a valuation whose variables carry codes:

* a variable: `𝔸` is its code; a constant: `𝔸` is the denotation of its type;
* `f a`: there are `𝔻`, `𝔹` with `Sem(f, pi(𝔻, 𝔹))`, the pair not collapsed to a
  proposition code or else recorded alongside it, `Sem(a, 𝔻)` and `𝔸 = 𝔹 ⟦a⟧`;
* `fun x : A => b`: `Sem(A, univ n)` for some `n`, and `𝔸 = pi(⟦A⟧, 𝔹)` with
  `Sem(b, 𝔹 d)` at every `d ∈ El ⟦A⟧`; similarly for `∀` and sorts.

`Sem` determines `𝔸`. The one delicate point is the first bullet of `f a` for functions
whose Π-type is a proposition: the collapse of `pi` to `⊤` forgets `𝔻`. `Sem` must therefore
carry the uncollapsed domain and fibre for every application, which means defining it over
uncollapsed formal types `Π(𝔻, 𝔹)` with a map to codes. I have not written this out.

### 11.5 Soundness

If `Γ ⊢ a ≡ b : A`, then at related valuations `ρ`, `ρ'` of `Γ`: `Sem(a, ⟦A⟧ρ)`,
`Sem(b, ⟦A⟧ρ)`, `⟦a⟧ρ = ⟦b⟧ρ ∈ El ⟦A⟧ρ`, `⟦A⟧ρ ~ ⟦A⟧ρ'`, and `⟦a⟧ρ`, `⟦a⟧ρ'` are related.

* `pat`: the premise gives `Sem` of the redex `Eq.rec α a M m b (Eq.refl α' a')`. Unfolding
  it through the six applications, the domain at the last one is `⟦@Eq α a b⟧`, and `Sem` of
  the major gives that this code is `⟦@Eq α' a' a'⟧`. If `⟦α⟧ = T` the latter is `R`, so
  `⟦a⟧ = ⟦b⟧` and the redex denotes `⟦m⟧`. If `⟦α⟧ ≠ T` the redex denotes `⟦m⟧` or `⋆`
  regardless.
* `extra` for `C`: endpoints `x`, `x + 1` differ, `⟦α⟧ = T`, fibre `T`: value `x + 1`.
  `extra` for `Fix`: both sides are the empty function. `Sem` of the four sides is checked
  directly.
* `proofIrrel`: both sides are `⋆`. `beta`, `eta`, congruences: compositionality and the
  substitution lemma for `⟦·⟧` and `Sem`.
* `Eq.rec` is type-correct: for related endpoints the fibres are `~`-related, hence have the
  same elements; `⟦a⟧ + 1` is used only in the fibre `T`, whose relation is total.
* The transport witness of §10: both `t (Eq.refl E)` and `t (H E E)` apply `⟦t⟧` to `⋆`.

`⟦C E⟧ = 1` and `⟦E⟧ = 0` as before.

### 11.6 Status

This model answers the reviewer's confirmed flaw (no large proof values; `El(prop)` has four
elements) and the gaps on mixed fibres and universe membership (codes; `pi` is uniform). It
has two points I have not worked through: the uncollapsed types in `Sem` (11.4), and whether
`⋆` as the value of every proof-valued function is compatible with data functions whose
fibres are propositions at some arguments and data at others. It needs its own review before
it is relied on. Until then the counterexample is: larger-context half machine-checked,
smaller-context half supported by a model that has been repaired twice and is not yet
independently checked.

## 12. Second review: the repaired model does not prove the separation (2026-11-11)

A second independent review of §11 found the denotations consistent (no derivable equation
with two values; `⟦C E⟧ = 1`, `⟦E⟧ = 0`) but the proof of soundness broken at the `pat` case,
with no local repair.

* **`Sem` is not functional over collapsed codes.** The type of `Eq.refl` and
  `∀ a : T, a = a` both collapse to `⊤`, so `Sem(Eq.refl T (C E), R)` and
  `Sem(Eq.refl T (C E), J)` both hold, and the code equality used in the `pat` case does not
  follow.
* **No completion over a small `Prop` can work.** Add to the environment the definitional
  equation `(∀ a : T, a = a) ≡ (∀ x : T, x = E)`. Both sides denote `⊤`, and every clause of
  the soundness proof other than `pat` still passes. But then `Eq.refl T (C E) : C E = E`, and
  `pat` gives `@Eq.rec T (C E) (fun _ _ => T) E E (Eq.refl T (C E)) ≡ E`, where the model says
  `2`. A correct soundness proof must fail on that extension, so the model has to separate two
  propositions that are the same element of its `Prop`.
* **Uncollapsed formal types are not invariant under conversion**: a proposition passed
  through a variable of type `Prop` loses its formal type, e.g. in
  `(fun (F : Prop → Prop) (k : F (∀ a : T, a = a)) => k) (fun X => X) (Eq.refl T) (C E)`.
* Π-proposition codes that remember their fibres are well-founded over domains built from `T`
  and propositions, but not for `∀ α : Sort u, …` or `∀ X : Prop, …`: the foundation problem of
  §8 again.

So the obstruction is structural. To validate ι at a syntactic `Eq.refl` the model must know
that a proof of `a = b` built from `Eq.refl` has identical endpoints; proof irrelevance and
impredicativity force propositions to be small, and small propositions cannot carry that
information. A set model with small propositions cannot prove the separation; what remains is
a realizability or syntactic argument that also handles the transport witness of §10, and I
have no such argument.

**Status of the counterexample.** `[P] ⊢ C E ≡ E` is machine-checked. `[] ⊬ C E ≡ E` is a
conjecture. The evidence for it: no derivation is visible (the only rule that makes the
`Eq.rec` in `C E` compute needs `E ≡ C E` or a fixed point of `C`, and the only fixed points
are `Fix p` for a proof `p` of the axiom `P`); two reviews found no equation refuting the
intended denotations. That is not a proof. `weakN_iff` is therefore neither proved nor
refuted.

## 13. Third attempt at the separation: a proof-insensitive term model (2026-11-11)

Not reviewed. It is built to avoid each defect found so far:

* §8, §11 (sets): propositions that carry endpoint information are too large, small ones
  cannot make ι sound. Here types are closed *terms*, so a proposition `∀ a : T, a = a` is
  compared structurally with `∀ x : T, x = E` and they differ, with no size cost.
* §10 (raw-term values): data must not depend on which proof is supplied. Here no data
  computation ever inspects a proof.

**Values.** `Val t i` for closed terms: `E ↦ 0`; `C t ↦ i + 1` if `t ↦ i`; closed under weak
head β-expansion; `Eq.rec α a M m b h` with `α` head-reducing to `T`, `a ↦ i`, `b ↦ j`: the
value of `m` if `i = j` and `i + 1` if `i ≠ j`. For any other `α`, and for an `Eq.rec` applied
to further arguments, the term behaves as its minor premise (applied to those arguments).
There is no ι rule on proofs and `h` is never examined. `Fix` is not unfolded.

**Types.** One inductive definition over all levels assigns to a closed type term a set of
closed terms with a fine and a coarse partial equivalence relation, together with a fine and
a coarse equality of type terms:

* `T`: members are the terms with a value; fine is equality of values, coarse is total.
* `@Eq α a b`: all closed terms if `a`, `b` are coarsely related in `α`, empty otherwise.
  Two such types are finely equal when their components are finely equal, coarsely equal when
  coarsely equal. `P` is empty. A Π-proposition has all closed terms or none.
* `∀ x : A, B`: terms `f` sending fine (coarse) related arguments to fine (coarse) related
  results; type equality componentwise.
* `Sort n`: type terms interpreted at level `n`, with fine and coarse type equality.
* an `Eq.rec` used as a type is its minor premise.

Coarsely equal types have the same members and relations up to the coarse/fine distinction
needed to place a transported term: `Eq.rec α a M m b h` lies in the fibre over `b` because
that fibre is coarsely equal to the one over `a`.

**Hereditary typing.** `Sem(e, A)` for closed `e` and closed type term `A`, by recursion on
`e`: for `f x` there are `D`, `B` with `Sem(f, ∀ D, B)`, `Sem(x, D)` and `A` finely equal to
`B[x]`; constants at the instance of their declared type; abstractions and Π-types
structurally. `Sem(e, A)` and `Sem(e, A')` give `A`, `A'` finely equal.

**Soundness.** If `Γ ⊢ a ≡ b : A` and `σ`, `σ'` are closing substitutions, finely related
pointwise and satisfying `Sem` at the context types, then `Aσ`, `Aσ'` are finely equal types,
`aσ`, `bσ'` are finely related members, and `Sem(aσ, Aσ)`, `Sem(bσ, Aσ)`; with coarsely
related substitutions, the coarse versions.

* `pat`: from `Sem` of the redex `Eq.rec α a M m b (Eq.refl α' a')`, the type of the major is
  finely equal both to `@Eq α a b` and to `@Eq α' a' a'`. If `α` is `T`, fine equality of
  these types gives equal values of `a` and `b`, so the redex has the value of `m`.
* The extension `(∀ a : T, a = a) ≡ (∀ x : T, x = E)` of §12 is not validated: the fibres
  `a = a` and `x = E` are not finely equal types.
* `proofIrrel`: all terms of a proposition are related. The witness of §10: no computation
  looks at the proofs.
* `extra` for `C`: values `v + 1` on both sides, since `v ≠ v + 1`. For `Fix`: the type
  `P → T` has every term as a member, vacuously.
* Under finely related substitutions the endpoints of an `Eq.rec` over `T` have equal values
  on both sides, so the same branch is taken.

`Val (C E) 1` and `Val E 0`, and values are unique, so `[] ⊢ C E ≡ E` would give `1 = 0`.

**Unchecked points.** Functionality of the type interpretation with impredicative Π;
whether fine type equality is preserved by every conversion rule under substitution (β at
type level, η); whether "behaves as its minor premise" for `α ≠ T` is compatible with fine
relatedness when the endpoints are coarsely but not finely related; the treatment of
partially applied `Eq`, `Eq.refl`, `Eq.rec` and of η; whether `Sem` is stable under the
substitution used in the `beta` case.

## 14. Third review: where the proof of the separation is missing (2026-11-11)

The review of §13 found no derivable equation contradicting `Val (C E) = 1`, `Val E = 0`, and
no extension equation of the §12 kind that the non-`pat` clauses accept. Probes on `Eq.rec`
away from `T`, on non-`T` fibres, the §10 witness, η, `extra`, `proofIrrel` and partial
applications pass. Three defects:

* **F1, repairable.** `Val` tests "`α` head-reduces to `T`" by β only, while the types
  identify an `Eq.rec` used as a type with its minor premise. With
  `α₁ := @Eq.rec T (C E) (fun _ _ => Type) T E (H (C E) E)` the generic
  `fun X a b h m => @Eq.rec X a (fun _ _ => T) m b h` is not finely self-related. Repair: the
  head reduction of types used by `Val` includes `Eq.rec … m … args ⇝ m args`.
* **F3, repairable.** `Sem` is not a recursion on closed terms (the abstraction clause is
  not structurally smaller and is negative in `Sem`). Repair: define it on open terms with a
  valuation assigning each variable a closed term and a closed type, binders quantifying over
  members; it must also record membership of each argument.
* **F2, open.** The type interpretation is not an inductive definition. Fine type equality
  cannot be structural (`(∀ z : P, C E = E) ≡ (∀ z : P, C E = C E)` is derivable, so fibres
  are compared only over members), and with that clause the equality of `∀ X : Prop, B` and
  `∀ X : Prop, B'` quantifies negatively over the relation being defined. Levels do not
  stratify it: `∀ X : Type, (X → T) → E = E` is at level 0 and quantifies over level 1, which
  contains `(∀ X : Prop, X) → T`.

So the missing piece of the separation is one definition: **a fine equality of propositions,
strong enough that `@Eq T a b` and `@Eq T a' b'` are equal only when the values agree and that
Π-propositions determine their fibres, sound for conversion, and definable in the presence of
impredicative quantification.** Truth of propositions is not the problem (it can be taken
from the standard proof-irrelevant set model in which `T` is a point and `P` is empty).

A candidate, not validated: take membership and the coarse data from a first model in which
propositions are compared by truth only, and define the fine equality afterwards by a
positive recursion whose Π clause compares fibres at the same closed, declaratively
well-typed argument on both sides. The proof that conversion respects it then needs every
valuation to consist of declaratively well-typed closed terms and to be related to itself,
and I have not checked that this closes without assuming the theorem being proved.

Status: `[] ⊬ C E ≡ E` remains a conjecture; three reviews found nothing against it and
located the gap in its proof at F2.

## 15. Working out the two-layer candidate of §14 (2026-11-11)

Paper analysis, not reviewed. The two-layer candidate does not close; the reason identifies
what the definition has to be.

Write FT for the fundamental theorem: if `Γ ⊢ a ≡ b : A` then related closing substitutions
give finely related instances (at `T`: equal values; at `Prop` and `Sort n`: the fine type
equality `R`).

1. *Layer one is fine.* A unary predicate (every declaratively well-typed closed term is a
   member of its type; closed terms of type `T` have a value), with propositions interpreted
   only by their truth in the standard model where `T` is a point and `P` is empty, is
   definable by recursion on levels, because propositions contribute nothing structural. It
   needs no equation between values, so the ι rule is not an issue there.
2. *`R` as a greatest fixed point with the Π clause at one argument on both sides* is a
   positive definition. But to prove a `forallEDF` conclusion one needs the body at the
   substitution extended by the same argument `d` on both sides, hence `d` related to itself,
   which is FT for the typing derivation of `d`. That is not an induction hypothesis.
3. *Quantifying over declaratively equal arguments instead* removes the need for
   reflexivity, but then a constant such as `C` or `Eq.rec` is self-related only if
   declaratively equal closed terms of type `T` have equal values, which is FT at `T` for an
   arbitrary derivation.
4. *Mixing* (related pairs at data domains, declaratively equal pairs at sort domains) fails
   at the variable rule: a type variable instantiated by two declaratively equal types must
   give `R`-related types, which is FT for types, and proving that by coinduction from the
   injectivity theorems of the calculus lands on equal values for declaratively equal
   endpoints of an equation over `T`, again FT at `T`.

Every variant needs FT for a derivation that is not a sub-derivation, and always at the same
place: the instance of a variable of type `Prop` or `Sort n` (or a higher kind over them).
This is the impredicativity circle, and its known resolution is Girard's: let such variables
range over arbitrary *candidates*, independent of any actual type, and prove a substitution
lemma identifying the interpretation at an actual type with the interpretation at that
type's own candidate.

What a candidate has to be here: for `X : Prop`, a truth value together with an abstract
colour, two occurrences being `R`-related when their colours agree; for `X : Sort (n+1)`, a
set of closed terms with a fine and a coarse relation, and a colour; for higher kinds,
functions on candidates. The term model is countable, so countably many colours suffice to
name every `R`-class, which is why the size obstruction of §8 and §11 does not return.
`@Eq T a b` gets the colour determined by the two values, a Π-proposition the colour of its
family of fibre colours over candidates of the domain.

Not done: the definition written out, the substitution lemma, and the check that Π over a
sort domain is sound when the candidate is not the candidate of any type. This is the
reducibility-candidates method for a calculus with impredicative `Prop`, predicative
universes and dependent types, extended by the colour component; it is a substantial proof
even on paper.

Status unchanged: `[] ⊬ C E ≡ E` is a conjecture.

## 16. Candidates with colours, written out (2026-11-11)

Not reviewed when written. It refines §13 (with the repairs F1, F3 of §14) at the one place
§14 and §15 left open. Size check first: a colour for a Π-proposition that determined its
fibre colours at all candidates would have to be a function on candidates, and colours would
contain their own function space. So Π-types get **no colour**. Colours are abstract tokens
attached only to *variables*.

**Layer one** (as §15 item 1): for each declaratively typed closed type term, its members,
with propositions interpreted by truth only; every declaratively typed closed term is a
member of its type, and those of type `T` have a value. Call such terms *valid*.

**Configurations.** A configuration is an open type or term together with a valuation `ρ`
assigning to each variable a valid closed term of the instantiated type and, if the variable's
type is a sort or a function type ending in a sort, a *colour* from a fixed infinite set
(for function kinds, a function from valid arguments to colours). Write `A[ρ]` for the closed
instance.

**Fine type equality `R`** between configurations of types, as a greatest fixed point; both
sides are first brought to weak head normal form by β, and by `Eq.rec … m … ⇝ m` at type
level:

* a coloured variable applied to arguments, on both sides: related when the colours at those
  arguments agree;
* `T`, `T`; `P`, `P`; `Sort ℓ`, `Sort ℓ'` with `ℓ ≈ ℓ'`;
* `@Eq α a b`, `@Eq α' a' b'`: `α R α'`, and if `α` is `T` then equal values of the instances
  of `a`, `a'` and of `b`, `b'`;
* `∀ x : A, B`, `∀ x : A', B'`: `A R A'`, and the bodies are related at every extension of the
  two valuations by a pair related at `A`: for a sort or sort-ended kind, any two valid terms
  with the same fresh colour; for `T`, valid terms of equal value; for a proposition, any two
  valid terms; for a data Π-type, valid terms related pointwise in the same sense;
* a type that is one side's variable and the other side's proper type is never related.

Every occurrence of `R` in these clauses is positive: relatedness of sort-typed instances is
equality of colours, not `R`.

**Abstraction lemma (the substitution lemma).** If two configurations are related at every
common colour of a variable `X`, and `Q R Q'` are valid closed types with the layer-one data
of the candidates, then the configurations with `Q`, `Q'` substituted for `X` are related.
Intended proof: coinduction, using that `R` is an equivalence and that a coloured variable
is compared only with a variable of the same colour.

**Fundamental theorem.** If `Γ ⊢ a ≡ b : A` and `ρ`, `ρ'` are valuations related pointwise
(same colours; equal values at `T`; pointwise at data Π-types), then the type configurations
are `R`-related and the term instances are related at the type, with hereditary typing as in
§13/§14-F3 using `R`.

* `bvar` at a sort-typed variable: same colour.
* `forallEDF`, `lamDF`: the bound variable ranges over related pairs, including all coloured
  pairs at sort domains, so no instance needs to be related to itself.
* `appDF` at a sort domain, argument types `Q`, `Q'`: the induction hypothesis gives `Q R Q'`;
  the function's hypothesis gives relatedness at every colour; the abstraction lemma gives
  relatedness of the instances.
* `pat` over `T`: hereditary typing gives `@Eq α a b R @Eq α' a' a'` at the valuation, hence
  equal values of `a` and `b`.
* constants: `C`, `Eq`, `Eq.refl`, `Eq.rec`, `H`, `E`, `T`, `P`, `Fix` are related to
  themselves at related arguments by their value clauses.

At the empty valuation: `Val (C E) = 1`, `Val E = 0`.

**Points I know are unverified:** the abstraction lemma (in particular for variables of
function kind, and when the substituted type is itself a Π over a sort); that `R` is
transitive; whether a coloured variable used as the *domain* of a Π or as the `α` of an `Eq`
needs more than layer-one data; and whether hereditary typing interacts correctly with
colours when a proposition is passed through a variable (the term of §12-F3).

## 17. Fourth review: §16 does not close the gap (2026-11-11)

Verdict of the review: not a complete definition, the abstraction lemma false as stated, `R`
not transitive. Local repairs exist for each defect but the repaired system was not shown to
close. Confirmed:

* **A. Function-kind colours.** "A function from valid arguments to colours" is either
  unsound (arbitrary function: `F ((fun Y => Y) X) ≡ F X` fails), circular (respecting `R`),
  or refutes the abstraction lemma (constant). Repair: an atomic colour for `F`, neutral
  applications compared argumentwise.
* **B. `Eq` at a variable type.** `@Eq X x y` ignores endpoints when `X` is not literally `T`,
  so substituting `X := T` breaks the abstraction lemma, and `fun X a b => @Eq X a b` is
  related to `fun X a b => @Eq X a a`. Repair: compare endpoints in the element relation at
  `α` for every `α`.
* **C. Elements of a type variable.** With only layer-one data, no choice of element
  relation at `X` works: total fails on
  `fun X x y h => @Eq.rec X x (fun _ _ => T) E y h`; an arbitrary candidate relation must be
  contained in `R`, which is the negative occurrence again. The surviving option is the
  structural relation of the actual closed instances, defined by recursion on levels, which
  is no longer abstraction in Girard's sense. Not verified.
* **D. Transitivity.** Colours not tied to truth make `R` non-transitive. Repair: a colour
  carries its layer-one class.

Also unproved: that `R`-related types have the same element relation (needed for `defeqDF`),
the abstraction lemma after the repairs (it needs coinduction up to substitution), and
existence of weak head normal forms of types under `Eq.rec … m … ⇝ m`.

Assessment after four reviews. The intended values have survived every probe, and the gap
has narrowed from "a model" to four named lemmas about one relation. But each written
definition has failed review, the last on four counts, and the remaining case (variables of
data-type kind) is exactly where the predicative and impredicative parts of the calculus
meet. I do not have a definition that I expect to survive a fifth review, and continuing to
iterate sketches at this rate is not converging fast enough to call the separation
established.

**Result of this effort.** `IsDefEqU.weakN_iff` under canonical `Eq`: open. Reduced, with a
machine-checked implication, to the non-derivability of the single closed equation
`[] ⊢ C E ≡ E` in one explicit environment (`KlopEnv.not_strengthening`); if that equation is
derivable the example proves nothing, and if it is not, the theorem is false as stated. The
equation is conjectured underivable.

## 18. A fifth model: small `Prop`, proof values outside it (2026-11-11)

Not reviewed when written. Diagnosis of the four failures: the ι rule needs a proof of
`a = b` over `T` to *know* whether its endpoints are identical (§8's tokens), but making that
knowledge part of the proposition makes `Prop` large (§8) or forces a fine equality of
propositions (§11 to §16). The way out is the standard one for impredicative `Prop`: keep the
denotation of a proposition a bare truth value, and give proofs values through a separate
realizability interpretation with Girard candidates. The tokens then live in proof values,
which are not elements of any universe, so no size constraint applies to them.

**Denotations `⟦·⟧`** (sets, with inaccessibles for the data universes):

* `⟦Prop⟧ = {0, 1}`. A data type is a set with a partial equivalence relation; `⟦T⟧` is `ℤ/3`
  with the total relation, every other base relation is equality, Π-types are pointwise.
  `⟦Sort (n+1)⟧` is the set of data types in `V_κₙ` with the discrete relation; on `{0,1}` the
  relation is equality.
* `⟦∀ x : A, B⟧`: if `B` is proposition-valued, the truth value of "for all elements"; if `A`
  is a proposition, `⟦B⟧` at any realizer when `⟦A⟧ = 1` and the one-point type when
  `⟦A⟧ = 0`; otherwise the dependent functions respecting the relations.
* Functions out of a proposition are identified with their value; data never receives a
  proof as an argument.
* `⟦@Eq α a b⟧ = 1` iff `⟦a⟧`, `⟦b⟧` are related in `⟦α⟧`.
* `⟦@Eq.rec α a M m b h⟧` for a data fibre: `⟦m⟧` if the proof value of `h` is the token
  `r`, or if `⟦α⟧ ≠ ⟦T⟧`, or if the fibre is not `⟦T⟧`; otherwise `⟦a⟧ + 1`.
* `⟦T⟧`, `⟦E⟧ = 0`, `⟦C⟧ = (+1)`, `⟦P⟧ = 0`, `⟦Fix⟧` the point of `⟦P → T⟧`.

**Proof values and realizers `⟪·⟫`.** A valuation gives each proof variable an arbitrary set
as value, and each variable `X : Prop` (or of a `Prop`-ended kind) a *candidate*: a set of
values, non-empty exactly when `⟦X⟧ = 1` (for kinds, a function to candidates). For a
proposition term `Q`, `⟪Q⟫` is a set of values:

* `⟪X⟫` is the candidate; `⟪F a⟫` applies the candidate function;
* `⟪@Eq α a b⟫`: if `⟦α⟧ = ⟦T⟧`, `{r}` when `⟦a⟧ = ⟦b⟧` and `{j}` otherwise; for other `α`,
  `{⋆}` when related, `∅` otherwise;
* `⟪∀ x : A, B⟫`: the functions `f` on the denotations of the arguments with
  `f(d) ∈ ⟪B⟫[x ↦ d]`; when `A` is `Prop` or a `Prop`-ended kind, for every element `d` and
  *every* candidate over it, with the same `f(d)`; when `A` is a proposition, functions from
  `⟪A⟫` to `⟪B⟫`;
* `⟪P⟫ = ∅`.

Proof terms get values compositionally: `λ` is a function, application is application,
`Eq.refl α a` is `r` if `⟦α⟧ = ⟦T⟧` and `⋆` otherwise, `H x y` is `r` if `x = y` and `j`
otherwise, and an `Eq.rec` with proposition fibre is `⟦m⟧`'s value when the major is `r` or
the endpoints are identical, and otherwise a chosen element of the realizer set of the fibre.

**Soundness**, by induction on `IsDefEq`, at valuations related pointwise (identical data
except coarsely related at... no: *identical* data and candidates; a second clause for
coarsely related valuations as in §8):

1. data: `⟦a⟧ = ⟦b⟧ ∈ ⟦A⟧`, and under coarsely related valuations the values are related;
2. types: `⟦A⟧ = ⟦B⟧`, and for propositions also `⟪A⟫ = ⟪B⟫`;
3. proofs: the values of `a` and `b` are in `⟪A⟫`. No equation between proof values is
   claimed; data does not depend on which element of `⟪A⟫` is supplied, because the only
   observation of a proof is the token test in `Eq.rec` over `T`, and `⟪@Eq T a b⟫` is a
   singleton.

Cases: `pat` holds by the definition of `Eq.rec` at the token `r`, since `Eq.refl T a'` has
value `r`. `proofIrrel` needs nothing for proofs; where a proof feeds an `Eq.rec` over `T`,
clause 3 for the two premises puts both values in the same singleton. `extra` for `C`: the
major `H x (C x)` has value `j`, so the right-hand side is `x + 1`. The extension equation of
§12 is rejected by clause 2: `⟪∀ a, a = a⟫` contains only the constant function `r`,
`⟪∀ x, x = E⟫` only the function that is `j` off `0`. The witness of §10: `⟦t⟧ = ⟦m⟧` is the
value of the body at the realizer `j`, namely `2`, and applying to a proof does nothing.
Impredicative instantiation uses the usual substitution lemma: `⟪B[Q]⟫ = ⟪B⟫[X ↦ ⟪Q⟫]`.

`⟦C E⟧ = 1`, `⟦E⟧ = 0`.

**Unverified:** that data really is independent of the chosen realizer under binders over
propositions (it should follow from clause 3 and singletons, but functions returning
elements of `T` whose bodies test a proof of a *non*-`T` equation or of a Π-proposition
applied to arguments need checking); the `Eq.rec` clause with proposition fibre and its
"chosen element"; the substitution lemma at `Prop`-ended kinds; `⟪·⟫` under type-level
`Eq.rec`; and whether clause 2 for propositions (`⟪A⟫ = ⟪B⟫` as sets) survives η and proof
irrelevance *inside* propositions, e.g. `Q h` versus `Q h'` for `Q : (E = E) → Prop`.

## 19. Fifth review, and a sixth model (2026-11-11)

**Review of §18: refuted as written.** A closed derivable equation gets two values. With

```text
e0   := @Eq.rec T E (fun y _ => @Eq Prop (E = E) (E = y)) (Eq.refl Prop (E = E)) (C E) (H E (C E))
cast := @Eq.rec Prop (E = E) (fun Y _ => Y) (Eq.refl T E) (E = C E) e0     : E = C E
D    := @Eq.rec T E (fun _ _ => T) E (C E) cast
```

`D ≡ C E` is derivable (proof irrelevance, then the equation of `C`), but the model gives
`cast` the value `r` (a cast between propositions of equal truth value is "identical
endpoints"), hence `⟦D⟧ = 0`. Further: no uniform realizer exists for transport along `j`
(`fun M k => Eq.rec k (H E (C E)) : ∀ M : T → Prop, M E → M (C E)`); set-theoretic functions
cannot realize `fun X x => x`; the soundness clauses omit function kinds, and the extension
`(fun x : T => E = x) ≡ (fun x : T => E = E)` is accepted and breaks `pat`; "is a
proposition" has to be semantic. The reviewer judged the diagnosis right and one idea
missing, and proposed it: a default realizer.

**Sixth model (incorporating that proposal; not reviewed).**

* *Realizers.* An applicative structure of untyped values (λ-terms over tokens `r`, `⊥` and
  data constants, modulo β), with `⊥` absorbing application. `r` is a certificate that the
  two endpoints of an equation over `T` are identical, and nothing else.
* *Types as realizability structures.* Every semantic type is a set with its relations as in
  §18 and, in addition, a realizability relation between values and elements; a proposition
  is a subset of a point, so its realizability relation is a set of values, which always
  contains `⊥` when the proposition is true. Kinds are interpreted by functions between such
  structures, so a type family carries its realizer sets, and equality of families includes
  them. Type variables range over all such structures (candidates).
* *Equality.* `@Eq T a b` is realized by `{r, ⊥}` if `⟦a⟧ = ⟦b⟧` and by `{⊥}` if merely
  related. At any other `α`, by `{⊥}` when related. `Eq.refl T a` has value `r`; `H x y` has
  value `⊥`; every `Eq.rec` with proposition fibre has the value of its minor premise only
  when `⟦α⟧ = ⟦T⟧` and the major is `r`, and `⊥` otherwise.
* *Data.* `Eq.rec` over `T` with fibre `⟦T⟧`: the minor premise if the major is `r` **or**
  the endpoints are identical, and `⟦a⟧ + 1` otherwise. Data therefore depends on a proof
  only through "is it `r`", and `r` can occur only where the endpoints are identical, so the
  result is a function of the endpoints wherever the proof is a realizer of its type.
* *Checks against the known failures.* `cast` above: `α = Prop`, so its value is `⊥`, and
  `⟦D⟧ = ⟦E⟧ + 1 = 1 = ⟦C E⟧`. Transport along `j` is uniformly `⊥`, a realizer of every
  true proposition. The ι rule holds by the first disjunct, with no inversion. The equation
  of `C`: major `⊥`, endpoints distinct, value `x + 1`. `(∀ a : T, a = a)` is realized by
  `λ_. r`, `(∀ x : T, x = E)` is not, and `fun x => E = x`, `fun x => E = E` differ as
  families, so both extension tests are rejected. `⟦C E⟧ = 1`, `⟦E⟧ = 0`.

What is not done is the bulk: the definition of realizability structures for universes
(coded, as in Λ-set or ω-set models), the interpretation of kinds, and the fundamental
theorem. After five failed reviews I state this model as a proposal, not as a proof.

## 20. The sixth model written out (2026-11-11)

Not reviewed when written. Three interpretations of raw terms at a valuation, and one theorem.

### 20.1 Semantic objects

* **Data.** As in §18: `⟦Prop⟧ = {0, 1}` (tagged, so it is recognisable); data types are sets
  with a partial equivalence relation, `⟦T⟧ = ℤ/3` total, universes of data types discrete,
  Π pointwise; a Π over a proposition domain is its codomain when the domain is `1` and a
  point when `0`; a Π whose fibres are all truth values is the truth value of the
  conjunction.
* **Values.** An applicative structure `𝕍`: untyped λ-terms over the tokens `r`, `⊥`, with
  abstraction over data arguments represented by set-indexed families, modulo β;
  `⊥` applied to anything is `⊥`. Proofs denote values. Values are not elements of any
  semantic type.
* **Candidates.** `Cand(0) = {∅}`; `Cand(1)` is the collection of β-closed sets of values
  containing `⊥`. The *shape* of a semantic type: `Sh(Prop)(t) = Cand(t)`;
  `Sh(Π(𝔻, 𝔹))(f)` is the dependent functions sending `(d, c)` with `c ∈ Sh(𝔻)(d)` to
  `Sh(𝔹 d)(f d)`, with proposition domains skipped; every other shape is a point.

### 20.2 Valuations and interpretations

A valuation gives each variable `x : A` an element `d ∈ ⟦A⟧`, a shape component
`c ∈ Sh(⟦A⟧)(d)`, and, if `⟦A⟧` is a truth value, a value `w ∈ ⟪A⟫`.

* `⟦e⟧` (data): as §18, with these clauses for `Eq`: `⟦@Eq α a b⟧ = 1` iff `⟦a⟧`, `⟦b⟧` are
  related; `⟦@Eq.rec α a M m b h⟧` with data fibre is `⟦a⟧ + 1` if `⟦α⟧ = ⟦T⟧`, the fibre is
  `⟦T⟧`, `⟦a⟧ ≠ ⟦b⟧` and the value of `h` is not `r`; and `⟦m⟧` in every other case.
  `⟦fun h : Q => b⟧` over a true proposition is `⟦b⟧` at any `w ∈ ⟪Q⟫`.
* `⟪e⟫` (shape component), compositional: the component for a variable; functions and
  application for `λ` and application, skipping proof arguments; `⟪@Eq α a b⟫` is `{r, ⊥}`
  if `(⟦a⟧, ⟪a⟫) = (⟦b⟧, ⟪b⟫)`, `{⊥}` if merely related, `∅` if unrelated;
  `⟪∀ x : A, B⟫` for a proposition is the set of values `v` such that for every `(d, c)`
  (and every `w ∈ ⟪A⟫` when `A` is a proposition) `v` applied to the argument is in
  `⟪B⟫`; `⟪P⟫ = ∅`; a type-level `Eq.rec` has the shape component of its minor premise.
* Values of proofs, compositional and untyped: variables, `λ`, application;
  `Eq.refl α a ↦ r`; `H x y ↦ ⊥`; an `Eq.rec` with proposition fibre has the value of its
  minor premise if its major has value `r`, and `⊥` otherwise.

### 20.3 Theorem

If `Γ ⊢ a ≡ b : A`, then at every valuation `ρ` of `Γ`:

1. `⟦A⟧ρ` is a semantic type, `⟦a⟧ρ = ⟦b⟧ρ ∈ ⟦A⟧ρ` and `⟪a⟫ρ = ⟪b⟫ρ ∈ Sh(⟦A⟧ρ)(⟦a⟧ρ)`;
2. if `⟦A⟧ρ = 1`, the values of `a` and of `b` are in `⟪A⟫ρ`;
3. `⟦a⟧`, `⟪a⟫` do not change when the values `w` of proof variables are changed within
   their candidates, and are related (coarsely) at coarsely related valuations.

Key cases.

* **`pat`.** The major is a literal `Eq.refl`, value `r`, so both the data clause and the
  proposition-fibre clause return the minor premise. Nothing about the endpoints is needed.
* **Certificate.** By 2, a proof of `@Eq α a b` has value in `{r, ⊥}` only if the endpoints
  are identical in denotation and shape component, and in `{⊥}` otherwise. So in the data
  clause "value of `h` is `r`" implies identical endpoints, and the data of an `Eq.rec`
  over `T` is a function of its endpoints whenever `h` is typed: clause 3.
* **`Eq.rec` with proposition fibre.** Major `r`: endpoints identical in both components, so
  the fibres over `(a, refl)` and `(b, h)` have the same `⟪·⟫`, and the minor's value is in
  it. Otherwise `⊥`, which is in `⟪·⟫` of every true proposition; the fibre is true because
  families respect the coarse relation.
* **`proofIrrel`.** No equation between values of proofs is claimed; data and shape
  components do not see proof arguments (clause 3, proposition domains skipped).
* **`extra` for `C`.** Major `H x (C x)` has value `⊥`, endpoints `x`, `x + 1` differ:
  `x + 1`. For `Fix`: both sides are the point of `⟦P → T⟧`.
* **`forallEDF` for a Π-proposition over `Prop` or a kind:** candidates are arbitrary, and the
  substitution lemma `⟪B[Q]⟫ρ = ⟪B⟫ρ[X ↦ (⟦Q⟧, ⟪Q⟫)]` is the usual one, valid because
  `⟪Q⟫ρ` is a candidate (β-closed, contains `⊥` when `Q` is true: every clause of `⟪·⟫`
  produces such a set).
* Checks: the term `D` of §19 has `cast ↦ ⊥` (its major `e0` is `⊥`), so `⟦D⟧ = 1 = ⟦C E⟧`.
  `(fun x => E = x)` and `(fun x => E = E)` have different `⟪·⟫`, as do `∀ a, a = a` and
  `∀ x, x = E`; both extension tests are rejected by clause 1.

At the empty valuation `⟦C E⟧ = 1` and `⟦E⟧ = 0`.

### 20.4 Known soft spots

Whether "the fibre is a truth value / the domain is a proposition" is always decidable from
the semantic objects (tagging of `{0,1}` and of points); the precise definition of `𝕍` and
of application of a value to a data argument; `⊥ ∈ ⟪Q⟫` for every true `Q` including `Eq`
at types whose elements have non-trivial shape components; clause 3 through `λ` over a
proposition whose realizers reach a data `Eq.rec` by proof-level computation; the coarse
relation on shape components; universe sizes for shapes (shapes are not elements of
universes, but `⟦·⟧` must not depend on them: it does not, except through the test
`⟪a⟫ = ⟪b⟫`, which occurs only inside `⟪·⟫`).

## 21. Sixth review, and the repair of its main gap (2026-11-11)

**Review of §20: no flaw found, incomplete in named places.** The reviewer could not produce
a derivable equation with two values or a typed proof whose value falls outside its realizer
set, and every earlier killer term passes (§19's `D`, the transport `Sub`, the §10 witness,
both extension equations, `Eq.rec` at a type variable, `Q h` versus `Q h'`). `C³ E = E` is
validated, harmlessly. Defects of the write-up:

1. **Certificate step (structural).** The `appDF` case for `Eq.rec T a M m b h` must show
   that the value of `h` lies in `⟪@Eq T a b⟫`, but its premises type `h` at some `A'` and
   the function at `∀ _ : A', B`, and nothing in §20 links `⟪A'⟫` to `⟪@Eq T a b⟫`: the shape
   of a data type was a point, so the candidate of `A'` was discarded.
2. The coarse clause for `⟪·⟫` in §20.3(3) is false and unused: delete it.
3. Whether an argument is a proof cannot be read from a raw term, and identifying
   `⟦Q → B⟧` with `⟦B⟧` makes `⟦E = E → T⟧` literally `⟦T⟧`.

**Repairs.**

* (3) Proofs denote a tagged point `•` in `⟦·⟧`; a Π over a proposition is the functions on
  `{•}` or on `∅`. Then `⟦f a⟧` is plain application, and `(E = E) → T` is not `⟦T⟧`.
* (2) Deleted.
* (1) *Types get codes.* The shape component of a data type is no longer a point but a code:
  `⟪T⟫` a tag; `⟪Sort ℓ⟫` a tag; `⟪∀ x : A, B⟫` for a data Π the pair of `⟪A⟫` and the
  function `(d, c) ↦ ⟪B⟫`; for a proposition, its candidate as before. A variable
  `X : Sort (n+1)` carries an arbitrary code over its denotation. Codes are not elements of
  universes, so there is no size constraint, and they are compared by set equality, so there
  is no fixed point to define. In `⟪@Eq α a b⟫`, "identical" compares `⟪a⟫`, `⟪b⟫`, which now
  includes codes when `α` is a universe. Clause 1 of the theorem already states
  `⟪A⟫ = ⟪B⟫` for convertible types.

  *Spine lemma*, proved in the same induction: if either side of `Γ ⊢ e ≡ e' : A` is a
  constant applied to `k` arguments, then `(⟦A⟧, ⟪A⟫)` equals that of the constant's declared
  type instantiated at those arguments. Cases: `constDF` at `k = 0`; `appDF` from the lemma
  for the function, since equal codes of Π-types have equal domain codes and equal fibre
  functions, together with the substitution lemma; `defeqDF` by clause 1; `beta` because an
  instance is a constant spine only if the body or the argument was; `pat`, `eta`,
  `proofIrrel` from their typing premises; `extra` by inspection of the four sides.

  *Certificate*: at `appDF` for `Eq.rec α a M m b h`, the spine lemma at `k = 5` gives
  `⟪A'⟫ = ⟪@Eq α a b⟫`, and clause 2 for the premise `h : A'` puts the value of `h` there.
  So a value `r` implies identical endpoints, which is what the data clause, clause 3 and
  the well-definedness of `⟦fun h : Q => b⟧` need.

  A redex `Eq.rec α a M m b (Eq.refl α' a')` needs nothing: its major has value `r`.

With these repairs I know of no gap that is more than the routine part of a soundness proof
(the definition of the applicative structure with a case construct on `r`/`⊥`, the
substitution lemmas for the three interpretations, universe levels). That is my assessment
and not a reviewer's; the repaired certificate step has not been reviewed.

## 22. Seventh review and the consolidated model (2026-11-11)

**Review of §21: no refutation; the certificate step not closed as written.** Confirmed:
the spine lemma's `beta` case fails when the body is a variable applied to arguments and the
argument a partial spine (`(fun R => R b h) (@Eq.rec T a M m)`); the lemma is unproved at
Π-propositions, whose shape component is a candidate and not injective; the `∀` clauses are
ill defined at empty domains (`P → T` versus `P → P`); and the data clause read an untyped
proof value while proofs denote a point. The reviewer gave local repairs A to F and checked
the cases named below. The earlier killers all still pass.

**Consolidated model (§20 with the repairs of §21 and A to F).**

1. *Data `⟦·⟧`.* `⟦Prop⟧ = {0, 1}`; `⟦T⟧ = ℤ/3` with the total relation; other relations as
   before and reflexive. Collapse convention (F): a Π all of whose fibres are truth values is
   the truth value of their conjunction, a proof `λ` denotes `•`, and hereditarily
   one-point Πs are identified with `1`. `⟦Eq.rec⟧` is a curried function of the **endpoints
   only** (A): at `⟦α⟧ = ⟦T⟧`, fibre `⟦T⟧` and `⟦a⟧ ≠ ⟦b⟧` it is `⟦a⟧ + 1`, otherwise the
   minor premise. No data clause reads a proof value. `⟦C⟧ = (+1)`, `⟦E⟧ = 0`, `⟦P⟧ = 0`.
2. *Values.* An applicative structure with tokens `r`, `⊥` (absorbing) and a case construct.
   Constants have compositional values (B): `Eq.refl ↦ λλ. r`,
   `Eq.rec ↦ λ…m b h. case h of r ↦ m | _ ↦ ⊥` at proposition fibres, `H ↦ ⊥`.
3. *Shape components `⟪·⟫`.* Propositions: candidates (β-closed sets of values, containing
   `⊥` exactly when true). Data types: codes, a Π-code being the domain code with the function
   sending an argument to the pair (denotation, code) of the fibre (D). The shape of an element
   depends on the denotation of its type only (E). `⟪@Eq α a b⟫` is `{r, ⊥}` if the pairs
   (denotation, shape) of `a` and `b` are identical, `{⊥}` if merely related, `∅` otherwise.
4. *Theorem*, by induction on `IsDefEq`, at every valuation:
   (1) `⟦a⟧ = ⟦b⟧ ∈ ⟦A⟧` and `⟪a⟫ = ⟪b⟫` of the shape of `⟦A⟧`, with coarse relatedness of
   data at coarsely related valuations;
   (2) if `A` is a proposition then `⟦A⟧ = 1` and the values of `a`, `b` are in `⟪A⟫`;
   (3) *head invariant* (C), for each side whose head is a constant or a variable applied to
   arguments: as long as the code of the head's type, instantiated at the arguments so far,
   is a Π-code, the next argument's (denotation, shape, value) lies in its domain and the
   remaining type is the fibre.
5. *Where the certificate is used.* Only at `pat` with `⟦α⟧ = ⟦T⟧` and fibre `⟦T⟧`: the
   redex's typing premise gives the head invariant for `Eq.rec α a M m b (Eq.refl α' a')`; all
   Πs in that prefix of the declared type are data Πs with non-empty domains, so the major's
   value `r` lies in `⟪@Eq α a b⟫`, the endpoints are identical, and the redex denotes its
   minor premise. At proposition fibres `pat` holds because the value of the redex is the
   case construct at `r`. Congruence in `h` and the K-instance are immediate because data
   ignores `h`.

`⟦C E⟧ = 1 ≠ 0 = ⟦E⟧`.

**Status of this argument.** Seven reviews. The last two found no derivable equation with
two values and no typed proof outside its realizer set, and each named gaps with repairs;
the consolidation above has not itself been reviewed, and the reviewer of §21 declined to
call the sketch acceptable until A, B, C and F are written out and checked. It is a paper
argument whose earlier versions were wrong five times.

## 23. Eighth review of the consolidated model (2026-11-11)

The reviewer worked repairs A, B, C and F through independently. Verdict: no refutation;
each holds with a stated amendment; one construction is still unwritten.

* **A (`Eq.rec` by endpoints): holds.** Membership in the declared type, coarse relation in
  every argument, the equation of `C`, congruence and the K-instance, and `pat` in its three
  situations. Amendments: the shape component is that of the minor for every data fibre; in
  the non-`T` cases the reduct denotes the minor through its typing premise.
* **B (values of constants): holds with a repair of a real failure.** Under the collapse
  convention a truth value can be an element of `Sort (n+1)` (`⟦P → T⟧ = 1`), and a type
  variable valued there with candidate `{⊥}` breaks clause 2 for
  `f : ∀ X : Type, X → X ⊢ f X x : X`. Repair: a truth value inside `Sort (n+1)` is always
  `1` and carries only the full candidate. `Eq.rec` is the case construct at all levels.
* **C (head invariant): holds once restated** with the closing clause "if the chain of
  Π-codes never breaks, the last one is the pair of the stated type". Walked through every
  rule, including the `beta` case that broke §21 (the two chains concatenate) and `defeqDF`.
  For the redex over `T` with fibre `T` all six prefixes of the declared type of `Eq.rec` are
  Π-codes, so `r ∈ ⟪@Eq α a b⟫` at the actual arguments.
* **F (collapse): holds as one rule**: a Π is a truth value exactly when all its fibres are
  (vacuously over an empty domain); a function constantly `•` is `•`. Checked on `P → T`,
  `P → P`, `∀ x : T, P → T`, `∀ p : Prop, p → T`, `fun X : Prop => X → T`,
  `(∀ α : Type, α) → T`, `∀ X : Type, X → X`, `T → Prop`, with η.
* All earlier killer terms pass; five new attacks by the reviewer failed.

**Still open.**

* *Structural:* the definition of shapes and of "a code over a denotation" (a recursion on
  codes or an inductively generated universe with unique decomposition of non-collapsed
  Π-sets, the codes over a set forming a set). The reviewer sketched but did not verify one.
* *Routine:* the applicative structure, substitution and weakening lemmas, level valuations.
* *Environment:* the argument is for the environment with exactly `Eq`, the four axioms and
  the two definitions. `KlopEnv` in the Lean file is a hypothesis on any extension, so a
  formal statement also needs that minimal environment constructed, with its inventory.

**Where the question stands.** The non-derivability of `[] ⊢ C E ≡ E` has a paper argument
that three successive independent reviews failed to break, with every amendment they asked
for either checked by a reviewer or listed above as open. Its earlier versions were wrong
five times, one construction is unwritten, and nothing of it is machine-checked. I regard
the statement as very likely true and `IsDefEqU.weakN_iff` as very likely false for
well-formed environments with canonical `Eq` and looping definitions, and I do not regard
either as established.

## 24. The construction of denotations, codes and shapes (2026-11-11)

Not reviewed when written. This is the piece §23 lists as structural.

**Denotations are tagged.** A semantic type is a tagged object, so that its outermost
constructor and components can be read off it:

* `tT` (with underlying set `ℤ/3`, total relation); `tProp` (underlying set `{0, 1}`);
  `tOne` (the collapsed one-point type, underlying set `{•}`); `tU n` (underlying set: the
  semantic types of level `n`, defined below);
* `tPi(𝔻, 𝔹)` with `𝔻` a semantic type and `𝔹` a function from the underlying set of `𝔻`
  to semantic types respecting the relation of `𝔻` (related arguments give equal types),
  not all of whose values are `tOne` or truth values; underlying set: the dependent functions
  respecting the relations; `tPiP(𝔹)` for a Π over a true proposition with data fibre `𝔹`
  (underlying set: functions on `{•}`).

Collapse rule (§23 F): the formation of a Π returns `tOne` when every fibre is `tOne`, the
conjunction truth value when every fibre is a truth value, `tOne` over a false proposition
or an empty domain with data fibres, and otherwise one of the two tagged forms. The semantic
types of level `n` are those hereditarily built with `tU m`, `m < n`, inside `V_κₙ`;
closure of each level under Π uses inaccessibility of `κₙ`. Because of the tags, a
non-collapsed Π determines its domain and fibre function.

**Shapes**, by recursion on the tagged denotation, for an element `d`:
`Sh(tT)(d) = Sh(tOne)(d) = {•}`; `Sh(tProp)(t) = Cand(t)`;
`Sh(tU n)(𝔻) = Code(𝔻)`, the codes over `𝔻` defined next;
`Sh(tPi(𝔻, 𝔹))(f)` = the dependent functions sending `(d, c)`, `c ∈ Sh(𝔻)(d)`, to
`Sh(𝔹 d)(f d)`; `Sh(tPiP(𝔹))(f) = Sh(𝔹)(f •)`.

**Codes**, by recursion on the tagged denotation `𝔻`:
`Code(tT)`, `Code(tProp)`, `Code(tU n)` are one-point sets (the tag);
`Code(tOne)` is the one-point set containing the full candidate;
`Code(tPi(𝔻, 𝔹))` = pairs of a code `κ ∈ Code(𝔻)` and a function sending `(d, c)` to a
code in `Code(𝔹 d)`;
`Code(tPiP(𝔹))` = pairs of a candidate (the realizers of the proposition domain) and a code
in `Code(𝔹)`.
A truth value has, as its shape component, a candidate. So the pair (denotation, shape
component) of a type is: for a proposition, (truth value, candidate); for a data type,
(tagged denotation, code).

Both recursions are well founded (on the rank of the tagged object), `Sh` is a function of
the denotation alone (repair E), and `Code(𝔻)` is a set: it is built from subsets of the
value structure `𝕍` and functions on sets. `Code` and `Sh` are mutually recursive only
through `Sh(tU n) = Code`, and `Code(𝔻)` for `𝔻` of level `n` refers to `Sh` at components
of `𝔻`, which have smaller rank.

**What the theorem needs from this.** (i) The interpretation `⟪A⟫` of a type term lands in
`Code(⟦A⟧)` or `Cand(⟦A⟧)`: by the clauses of §22 item 3, compositionally. (ii) A variable
`X : Sort (n+1)` ranges over all pairs `(𝔻, κ)` with `𝔻` of level `n` and `κ ∈ Code(𝔻)`, or
`(1, full candidate)`: the substitution lemma holds because every `⟪A⟫` is such a pair.
(iii) Equal Π-codes have equal components: pairing. (iv) The head invariant reads the domain
of a Π-code and its fibre at an argument: defined.

**Value structure.** `𝕍` is the set of closed terms of the untyped λ-calculus with constants
`r`, `⊥` and a binary `case`, modulo β and the rules `⊥ v = ⊥`, `case r u v = u`,
`case ⊥ u v = v`; data and type arguments are erased (a proof applied to a data argument is
applied to `⊥`... no: applied to nothing, the abstraction over a data variable is erased).
This calculus is confluent (orthogonal rules plus β), so `r ≠ ⊥`. A candidate is a set of
values containing `⊥`. With data arguments erased, `H ↦ ⊥`, `Eq.refl ↦ r`, and a proof of
`∀ x : T, x = E` such as `fun x => H x E` has value `⊥`, a realizer; `∀ a : T, a = a` is
realized by `r`, and `∀ x : T, x = E` is not, because `r ∉ ⟪1 = 0⟫ = {⊥}`.

One consequence to check: with data arguments erased, a proof cannot return `r` at some
arguments and `⊥` at others. A term needing that would be a proof of `∀ x y : T, x = y`
built by cases on `x`, `y`; `T` is an axiom with no eliminator, so no such term exists, but
an environment with an inductive `T` would need unerased data arguments (set-indexed
abstraction), as §20 had.

## 25. Ninth review, and the model as it now stands (2026-11-11)

**Review of §24: no refutation; one structural defect with a repair the reviewer worked
through in part, two routine ones.**

* *Structural.* "Proof or data" was not determined by the construction. With `tOne` distinct
  from the truth value `1`, the collapse rule is not a function of semantic input (`P → T`
  against `P → P`). With them identified, erasing data arguments breaks `lamDF`: in
  `fun (q : Prop) (g : q → T) => Eq.refl T E` the variable `g` is data at `q = 1` and a proof
  at `q = 0`, so the erased `λ q` has no single value.
  **Repair:** identify `tOne` with `1` and do not erase. The value of a term is a purely
  syntactic translation (variables, `λ`, application; sorts and Π to `⊥`;
  `Eq.refl ↦ λ α a. r`; `Eq.rec ↦ λ α a M m b h. case h m ⊥`; `H ↦ ⊥`), data variables take
  arbitrary values, and a Π-proposition over a data domain is realized by the `v` with
  `v u ∈ ⟪B⟫` for every `(d, c)` and every value `u`, the same formula as for a proposition
  domain at the full candidate.
* *Routine.* The shape of a proof is `{•}` (needed so that `@Eq Q h h'` is realized by `r`);
  `Cand(0) = {∅}` is the exception to "contains `⊥`".

Checked by the reviewer under the repair: closure of levels, relations, well-foundedness of
`Sh` and `Code`, compositionality of codes and the substitution lemma for types, the
constant `Eq.rec` in the candidate of its declared type, impredicative Π, β, η, confluence of
the value calculus, both extension equations, the certificate in the `T`/`T` case, and a
further round of attacks (Leibniz-style hypotheses, `congrArg`, equations under
`fun p : P`, type-level `Eq.rec` under `p`, partial spines through β), all failing.
Not re-checked by this reviewer: the head invariant beyond `appDF`, `defeqDF`, `trans` and
`beta`.

**The model as it now stands** is §22 with the amendments of §23, the construction of §24,
and the repair above. In one paragraph: a set model in which `Prop` is `{0, 1}`, `T` is
`ℤ/3` with all elements related, `C` is the successor and `Eq.rec` is a function of its
endpoints that returns `endpoint + 1` exactly at `T` with fibre `T` and distinct endpoints;
every term also has an untyped value in a λ-calculus with tokens `r`, `⊥`; every proposition
has a set of realizing values, containing `⊥` when true and containing `r` for an equation
exactly when its endpoints are identical; every data type has a code recording those sets;
and the soundness theorem carries a head invariant from which a redex
`Eq.rec T a M m b (Eq.refl …)` with fibre `T` has identical endpoints. Then
`⟦C E⟧ = 1 ≠ 0 = ⟦E⟧`.

**Review history.** Nine independent reviews. Models 1 to 5 were each refuted. Reviews 6 to 9
of the sixth model found no derivable equation with two values and no typed proof outside
its realizer set, across some dozens of attack terms; each found definitional gaps, each with
a repair, the last one "structural" in the sense that a construction had to be changed, not
that an idea was missing. Unwritten: the full induction for the head invariant, level
valuations, and the minimal environment. Nothing is machine-checked.

## 26. The head-invariant induction, written out (2026-11-11)

This is the item §25 lists as unwritten. It follows the walk of the eighth reviewer (§23 C)
and adds the cases they did not need. Notation: for a term `s = h e₁ … e_k` with `h` a
constant or a variable, and a valuation `ρ`, let `R₀` be the pair (denotation, shape
component) of the type of `h` (the declared type of a constant at its levels; the pair
carried by `ρ` for a variable).

**Inv(s, A, ρ).** There are pairs `R₀, …, R_j`, `j ≤ k`, such that for `i < j` the pair
`R_i` is a non-collapsed Π (a `tPi` or `tPiP` with its code), the triple (denotation, shape,
value) of `e_{i+1}` at `ρ` lies in its domain (for `tPiP`: the value lies in the domain's
candidate), and `R_{i+1}` is its fibre there; and either `j = k` and `R_k` is the pair of
`A` at `ρ`, or `j < k` and `R_j` is a truth value with a candidate (the chain has entered a
proposition, where nothing more is claimed).

**Claim.** If `Γ ⊢ a ≡ b : A`, then for every valuation `ρ` of `Γ`, `Inv(a, A, ρ)` when `a`
has a constant or variable head, and likewise for `b`; together with clauses (1), (2) of
§22.

Rules of `IsDefEq` (`Basic.lean`):

* `bvar`. `k = 0`, `R₀` is the pair of the variable's type, which is the pair of `A` by the
  definition of a valuation of `Γ` and the weakening lemma.
* `symm`, `trans`. Each side of the conclusion is a side of a premise at the same `A`.
* `sortDF`, `lamDF`, `forallEDF`. Neither side has a constant or variable head.
* `constDF`. `k = 0`; `R₀` is the pair of the declared type at `ls`, and at `ls'` for the
  other side; these agree because the levels are equivalent and the interpretation depends
  on levels through their values. `A` is the declared type at `ls`.
* `appDF`, conclusion `f a ≡ f' a' : B[a]` from `f ≡ f' : ∀ x : A, B` and `a ≡ a' : A`.
  Suppose `f = h e₁ … e_{k-1}`. By induction `Inv(f, ∀ x : A, B, ρ)`. If its chain ends at
  `j < k - 1` in a truth value, the same chain serves for `f a`. Otherwise
  `R_{k-1}` is the pair of `∀ x : A, B`. If that pair is a truth value (the Π collapsed),
  the chain for `f a` stops there. If not, it is a non-collapsed Π whose domain is the pair
  of `A` and whose fibre function is `d, c ↦` the pair of `B` (definition of the
  interpretation of `∀`); clauses (1), (2) for the premise `a ≡ a' : A` put the triple of
  `a` in the domain; the fibre there is the pair of `B` at `ρ[x ↦ a]`, which is the pair of
  `B[a]` by the substitution lemma. Same for `f' a'`, using `⟦a⟧ = ⟦a'⟧`, `⟪a⟫ = ⟪a'⟫` to
  identify the stated type's pair; the value of `a'` lies in the domain by clause (2) for
  the right-hand side.
* `defeqDF`. Clause (1) for `A ≡ B` gives equal pairs for the two stated types; the chain
  is unchanged.
* `beta`, conclusion `(fun x : A => e) e' ≡ e[e'] : B[e']` from `A :: Γ ⊢ e : B` and
  `Γ ⊢ e' : A`. The left side is λ-headed. For the right side, at `ρ`, use the induction
  hypothesis for `e` at `ρ' = ρ[x ↦ triple of e']`, a valuation of `A :: Γ` by clauses (1),
  (2) for `e'`.
  - If `e = h e₁ … e_k` with `h` a constant or a variable other than `x`: `e[e']` has the
    same head, its arguments are the instances, and `Inv(e, B, ρ')` transfers by the
    substitution lemma for all three interpretations.
  - If `e = x e₁ … e_k` and `e' = h' d₁ … d_m` has a constant or variable head: `Inv(e', A, ρ)`
    gives a chain `R'₀, …, R'_{j'}`. If `j' = m`, `R'_m` is the pair of `A`, which is `R₀` of
    the chain of `e` at `ρ'`; concatenate. If `j' < m`, the chain of `e'` already ended in a
    truth value and serves for `e[e']`.
  - If `e = x e₁ … e_k` and `e'` is a λ, or `e` is not of spine form: `e[e']` is λ-headed or
    its head is determined as above.
* `eta`, conclusion `(fun x : A => e↑ x) ≡ e : ∀ x : A, B`. The left side is λ-headed; the
  right side is the subject of the premise at the same type.
* `proofIrrel`, conclusion `h ≡ h' : p`. Both sides are subjects of premises at `p`.
* `extra`. The two equations are `C ≡ fun x => …` and `Fix ≡ fun p => …`: left sides are
  bare constants at their declared types (`k = 0`), right sides are λ-headed. Clauses (1),
  (2) for the right sides are the direct computations of §22.
* `pat`, conclusion `e ≡ r.apply … : A` with premises `Γ ⊢ e : A` and the typing of the
  reduct. The left side is the subject of the first premise. The reduct is a λ-template
  applied to arguments, hence λ-headed.
* `projDF`, `projIota`, `structEta`, `unitLike`. No instance: the environment has no
  projection entry.

**Use.** In the `pat` case let `e = Eq.rec α a M m b (Eq.refl α' a')` with `⟦α⟧ρ = tT` and
fibre `⟦M b h⟧ρ = tT`. `Inv(e, A, ρ)` holds by the first premise. The declared type of
`Eq.rec` at these levels (motive universe at least 1) is a chain of six Πs; none collapses at
these arguments, because each has the non-truth-valued fibre obtained from the constant
motive, and the last, `(a = b) → T`, is a `tPiP` since its domain is true (it has the member
supplied by the major by clause (2), or else `Inv` would have stopped). So `j = 6` and the
value of the major, `r`, lies in the candidate of `@Eq α a b` at `ρ`, which contains `r`
only if the pairs of `a` and `b` are identical. Hence `⟦a⟧ρ = ⟦b⟧ρ` and `⟦e⟧ρ = ⟦m⟧ρ`, which
is the denotation of the reduct (a β-chain selecting the minor, by clause (1) for the second
premise and compositionality).

Two places where this write-up leans on something not spelled out: the substitution and
weakening lemmas for the three interpretations, and "none collapses at these arguments",
which the eighth reviewer checked for the six prefixes.

## 27. External second opinion on the write-up (2026-11-11)

An independent assessment (Astra, read-only in this worktree) of the public write-up and of
§20 to §26. Its verdict: the positive half is solid (it re-ran the Lean file and
`#print axioms`); it found no derivation of `[] ⊢ C E ≡ E` after trying abstraction over
`P`, transport of reflexivity along `H`, impredicative and type-valued motives, and
higher-order fixed points; it found no term violating the model of §25/§26; and it rates the
failure of `weakN_iff` as probable, not established. Corrections it made, all accepted:

* **`Eq` has projection metadata.** `VInductDecl.projectionEntries` registers an entry for
  every single-constructor family, so "the environment has no projection entry" (§8, §26) is
  wrong. The four projection rules are still without instances, for a different reason:
  `structEta` and `unitLike` need zero indices and `Eq` has one; `projDF` needs a field type
  and `Eq.refl` has no fields; `projIota` needs a typed projection. The inventory of the
  minimal environment has to prove this.
* **"The only fixed points of `C` are `Fix p`" is not proved** and is not what the argument
  uses; the model is.
* **"Cannot be stated as a single Lean theorem" was wrong.** The separation can be stated and
  proved conditionally on a set-theoretic universe tower (or an explicit model interface).
  What Lean cannot do is supply that tower unconditionally for all levels.
* **"No well-founded confluence join" needed a definition.** The confluence theorem does give
  `C E ≡ E` a join in the presence of a closed fixed point; what fails is justification of its
  side conditions by joins recursively.
* The supporting lemmas (substitution for the three interpretations, semantic typing of the
  partially applied `Eq.rec`, compatibility of collapse with codes and impredicative Π, the
  rank construction of universes, shapes and codes) are not routine and are not written.

Its suggested order of work: construct the minimal environment with its inventory;
consolidate §20 to §26 into one definition; prove soundness against an explicit model
interface, with the interface's existence as a visible hypothesis; then either realise the
interface in encoded sets or replace it by a syntactic logical relation.

**Second external run, briefed to refute (2026-11-11).** It did not refute the example. It
re-checked the Lean file and axioms, confirmed that `not_strengthening` instantiates
`weakN_iff` correctly (`Ctx.LiftN 1 0 [] [P]`, closed terms unchanged by the lift, the
well-formed larger context) and that `mutualDef` admits the two definitions and registers
the equations used. Attacks tried and failed: exporting the fixed point through abstraction
over `P`; the two-stage transport of §19; the proof-irrelevance witness of §10; impredicativity
and the collapse convention (`P → T`, `∀ X : Type, X → X`, `∀ q : Prop, (q → T) → E = E`);
the partial-spine case `(fun R => R b h) (@Eq.rec T a M m)` against the head invariant.
Residual doubt it names: the model needs one complete definition with a simultaneous
soundness proof; the exact environment and its inventory (including `Eq`'s projection
metadata) are not constructed; `exists_klopEnv` is an extension theorem over a given base and
not the existence of the minimal environment.

## 28. The model in the form to be formalised (2026-11-11)

Not reviewed when written. It is the model of §22 to §27 with one simplification that removes
shapes and codes: **a proposition denotes its set of realizers.** This is possible because
realizers are syntactic (closed terms of an untyped calculus, a countable set), so the set of
all candidates is a small set and `Prop` can denote it.

**Values.** `Val`: closed terms of the untyped λ-calculus with constants `r`, `⊥` and
`case`. Weak head reduction is a deterministic function: β, `⊥ v ↦ ⊥`,
`case r u v ↦ u`, `case ⊥ u v ↦ v`, and reduction of the scrutinee of `case` and of the
head of an application. `v ⇓ r` means the reduction of `v` reaches `r`. A *candidate* is a
set of values closed under weak head reduction and expansion. The value `|e|` of a term is a
syntactic translation: variables, λ and application are translated homomorphically
(binder domains dropped); sorts, Π-types and data constants go to `⊥`;
`Eq.refl ↦ λλ. r`; `Eq.rec ↦ λ α a M m b h. case h m ⊥`; `H ↦ ⊥`; `Eq`, `T`, `E`, `P`, `C`,
`Fix` go to `⊥`. It commutes with substitution on the nose.

**Denotations**, in a universe tower. A semantic type is one of:

* a candidate (tagged), the denotation of a proposition; its only element is `•`;
* `T`: the three-element set, with the total coarse relation;
* `𝒞`: the set of all candidates, the denotation of `Prop`; coarse relation: both empty or
  both non-empty;
* `𝒰ₙ`: the semantic types of level `n`; coarse relation `~`, the structural relation that
  compares candidates by emptiness;
* `Π(𝔻, 𝔹)` with not all fibres candidates: dependent functions respecting the coarse
  relations, a function constantly `•` being `•`; if all fibres are candidates, the Π is the
  candidate `{v | ∀ d ∈ 𝔻, ∀ u, v u ∈ 𝔹 d}`;
* `Πₚ(Q, 𝔹)` for a candidate `Q` and a data fibre: functions on `{•}` if `Q` is non-empty,
  the one-element type if it is empty; with candidate fibre it is the candidate
  `{v | ∀ u ∈ Q, v u ∈ 𝔹}`.

`⟦@Eq α a b⟧` is the candidate of values that, if they reduce to `r`, do so only when
`⟦a⟧ = ⟦b⟧`: all values with `⊥`-or-`r` behaviour allowed are: the closure of `{r, ⊥}` when
`⟦a⟧ = ⟦b⟧`, the closure of `{⊥}` when merely coarsely related, and the empty candidate
otherwise. `⟦@Eq.rec α a M m b h⟧`: `•` if the fibre is a candidate; `⟦a⟧ + 1` if `⟦α⟧ = T`,
the fibre is `T` and `⟦a⟧ ≠ ⟦b⟧`; otherwise `⟦m⟧`. `⟦E⟧ = 0`, `⟦C⟧ = (+1)`, `⟦P⟧ = ∅`,
`⟦H⟧ = •`, `⟦Fix⟧` the element of `Πₚ(∅, T)`. Every data type is inhabited.

**Theorem.** If `Γ ⊢ a ≡ b : A`, then at every valuation (each variable gets an element of
the denotation of its type and, independently, a value which lies in that denotation when it
is a candidate):

1. `⟦A⟧` is a semantic type and `⟦a⟧ = ⟦b⟧` is an element of it;
2. if `⟦A⟧` is a candidate, `|a|` and `|b|` at the valuation's values are in it;
3. at coarsely related valuations, `⟦a⟧` and `⟦a⟧'` are coarsely related;
4. the head invariant of §26, with "domain" now read off the tagged denotation.

Differences from §22 to §27: no shape components and no codes (a Π over a proposition domain
records the candidate in its denotation; a type family into `Prop` is a function into
candidates); type equality is equality of denotations, which now includes realizer sets, so
the two extension equations of §12 and §19 are rejected by clause 1; impredicative Π over
`Prop` quantifies over the set of all candidates.
