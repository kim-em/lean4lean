# Strengthening under canonical `Eq`: a first-principles assessment (2026-11-10)

Outcome (updated 2026-11-11): **a counterexample**, in §7. `IsDefEqU.weakN_iff` fails for a
well-formed environment with canonical `Eq` and two looping `mutualDef`s. The environment and
the derivation in the larger context are checked in Lean; non-derivability in the smaller
context is argued by a model and is not formalised. Sections 1 to 6 record the analysis that
led there; where they say the statement is probably true, §7 supersedes them. The reduction
of §1 is checked and stands.

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
