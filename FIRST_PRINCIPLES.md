# Strengthening under canonical `Eq`: a first-principles assessment (2026-11-10)

Outcome: **not solved.** No proof and no counterexample. What follows is paper analysis; nothing
here is checked in Lean. It was written without relying on the branch's ledger, and the ledger
was consulted afterwards only to see which points are already there.

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
