# Second review (Astra, gpt-6-astra): certificate architecture

Answer, verbatim:

**I would choose (A)’s certificate discipline, while reusing the existing confluence proof through a narrower version of (B)’s generic interface. I would not commit to (B)’s same-level closure claim as stated.** That claim is a substantial additional theorem, and some common uses of declarative conversion in the existing proof appear to require precisely the closure that the next level is supposed to establish.

This is an architectural assessment of the relations you described, rather than an audit of the 29k-line implementation. There is an important uncertainty: the problematic transports might admit alternative proofs that preserve the level. But those alternatives must be exhibited; they do not follow from fixed-context CR or semantic head inversion.

**1. The level hierarchy is conditional, and the proposed interface conceals the main difficulty.**

Write \(R[J]\) for the reduction relation with side conditions in \(J\), and \(F(J)\) for joining by \(R[J]\) modulo the corresponding normal equality. Suppressing the typing component, your proposal is
\[
J_{n+1}=F(J_n).
\]

If an interface \(I(J_n)\) genuinely suffices to prove confluence of \(R[J_n]\), then obtaining transitivity of \(J_{n+1}\) is plausible: join the two witnesses through their shared middle term. **Transitivity at the new level is not itself the fundamental problem.** After establishing monotonicity, completeness can raise two input certificates to a common level and compose there.

The difficult obligation is
\[
I(J_n)\Longrightarrow I(F(J_n)).
\]
Confluence proves only part of this implication.

Here is a concrete index mismatch to look for in the mainline proof. Suppose it transports an existing agreement along a reduction:
\[
J_n(\Gamma\vdash A\equiv B:s),\qquad
A\;R[J_n]\;A'
\quad\Longrightarrow\quad
J_n(\Gamma\vdash A'\equiv B:s).
\]
In the declarative development, this is routine: obtain \(A'\equiv A\) from reduction soundness and compose.

In the hierarchy, however, the immediate certificate for that reduction belongs to **\(F(J_n)=J_{n+1}\)**. Transitivity of \(J_n\) cannot consume it. Confluence already established for the representation of \(J_n\) concerns \(R[J_{n-1}]\), which need not contain this step.

This is particularly relevant when reductions occur in types, dependent arguments, or contexts. Subject reduction may sometimes be proved structurally without certifying the whole step as an equality at the same level; that would be a legitimate escape. But “use reduction soundness, then uniqueness and transitivity” does not provide that escape.

There is a useful diagnostic here. If the generic interface requires every relevant \(R[J]\)-step to be replayable as a \(J\)-equality, and requires normal-equality constructors to be replayable in \(J\), then transitivity gives
\[
F(J)\subseteq J.
\]
Such an interface asks for an already closed conversion relation. It can be excellent for instantiating the mainline with `IsDefEq`, but it does not explain how to construct the proposed increasing hierarchy.

Thus I would classify the existing side-condition arguments into three groups:

- **Semantic facts:** impossibility of certain heads, universe constraints, declarative uniqueness. These may remain consequences of soundness into `IsDefEq`.
- **Certificate transformations within the lower level:** substitution, context transport, agreement of chosen exposures.
- **New outer conversion witnesses:** equalities justified by the reductions currently being joined.

A generic refactor must distinguish the last two. Replacing every occurrence of `IsDefEq` by one predicate \(J\) loses this distinction.

There is also a base-case issue. If \(J_0\) is literally empty and every reflexive or typing leaf requires \(J_0\), the hierarchy may never start. Your certified typing component must provide explicit seeds and formation rules. An empty *conversion oracle* can be reasonable; an empty judgment supplying all typing premises generally is not.

For uniqueness and Π-injectivity, distinguish their declarative and certified conclusions. Soundness plus the available semantic theorem gives
\[
T_n(e,A),T_n(e,B)
\Longrightarrow
\operatorname{IsDefEq}(A,B).
\]
It does **not** give \(J_n(A,B)\). Similarly, semantic Π-injectivity produces declarative equality of components, without a bound on their certificate level. Invoking eventual completeness to repair this during the construction of the hierarchy would be circular.

There are possible constructive replacements:

- For synthesis, prove coherence of the synthesis derivations, including coherence of their certified head exposures.
- For certified Π-injectivity, project a joining witness between Π-types onto their domains and bodies.

The latter can use semantic head inversion to exclude impossible outer steps. But it must actually construct the component certificates. In particular, projecting body reductions requires transport between the contexts extended by the different domains. That context-conversion work is part of the theorem, not something supplied by semantic injectivity.

So my answer to “does the hierarchy close?” is: **not established by the proposed argument, and a literal genericization of the current transports is unlikely to close it.** I cannot rule out a carefully designed hierarchy. The missing evidence is a certificate-preserving proof of the interface, especially reduction transport, exposure coherence, and dependent context conversion.

Allowing these operations to increase the level is not inherently fatal to every approach. It is fatal to this particular induction unless the generic strip is redesigned to accommodate that increase with an independently well-founded dependency argument.

**2. Use support-preserving synthesis and exposure; avoid global canonicalization of arbitrary mainline witnesses.**

The required canonicity is weaker than a unique normal form or deterministic reduction strategy. What you need is **preservation of the image of context insertion**.

For a canonical reduction, the essential shape is
\[
e^\uparrow\;R\;t
\Longrightarrow
\exists t_0,\ t=t_0^\uparrow,
\]
together with descent of its certificates. For synthesis, you want
\[
\operatorname{Synth}_{\Gamma'}(e^\uparrow,T)
\Longrightarrow
\exists T_0,\ T=T_0^\uparrow
\]
and a corresponding synthesis derivation in \(\Gamma\).

The second assertion should concern synthesis, not arbitrary typing. A lifted term can certainly be assigned a non-lifted type by conversion. Your existential conclusion \(A'\) is useful precisely because you need not preserve that arbitrary assigned type.

Restricting function eta to a synthesized domain is the most promising local change, but the restriction must extend to **the exposure of the synthesized type**. Otherwise:

1. synthesize a supported type \(T\);
2. use unrestricted declarative conversion to expose \(T\) as \(\Pi A B\);
3. introduce an unsupported \(A\) by eta.

That merely moves the original problem into exposure.

There is a simple illustration. Given an inserted \(q:Q\), set
\[
D(q):=(\lambda(\_ : Q).D)\ q.
\]
A function of domain \(D\) can also be typed with domain \(D(q)\). Unrestricted eta may therefore introduce
\[
\lambda(x:D(q)).\,e\,x
\]
from a source \(e\) that does not mention \(q\). This example is easy to repair by reduction, but it shows why source support alone does not control arbitrary typing choices.

For structure eta, apply the same discipline to the exposed structure type and its parameters. For singleton reconstruction, the proved singleton-eta equality supplies the equational justification. You additionally need the extraction construction—including its Eq-cast motives and inferred types—to commute with context insertion.

**Restricting eta will break some existing proof scripts, including potentially the use in `NormalEqN.beta_aux`. It need not break the theorem.** The replacement obligation is concrete:

> Given a function with a certified chosen Π-exposure, and another certified Π-typing used by an eta comparison, construct certified agreement of their domains and the required codomain/context transports, then join the expansions.

If the chosen domain is \(A\) and the `etaBoth` branch uses \(D\), do not require a reduction to manufacture the exact lambda with annotation \(D\). Expand at \(A\), and compare with the \(D\)-annotated lambda through normal equality and certified \(A\equiv D\).

That is the purpose of domain-flexible normal equality—but its domain premise must come from the certificates. Ambient uniqueness followed by ambient Π-injectivity is insufficient.

This is where I would first test the architecture: can the revised `beta_aux` obtain that agreement at the level the strip requires?

I would not start with a global canonicalization theorem for the unrestricted relation. A theorem replacing arbitrary witnesses between lifts by supported witnesses must repair every unsupported annotation and every side condition created during that repair. That is a substantial alternative formulation of the provenance problem. Local canonicalization lemmas for individual eta or exposure cases could still be valuable.

A typed “q-erasure substitution” also does not give a general shortcut. To substitute away \(q:Q\), you need a term of \(Q\) in the smaller context, with the appropriate dependent substitution through the context. No such term is assumed. An untyped erasure would need its own preservation theorem for conversion and all the dependent computation rules.

Finally, because the hypothesis supplies well-formedness of \(\Gamma'\), make context well-formedness part of the certificate/descent story. Do not silently assume well-formedness of \(\Gamma\) if establishing it uses the same strengthening machinery.

**3. I do not see a sound shortcut from the existing fixed-context CR theorem alone.**

The proposed recursive use of CR would require a theorem saying that every side-condition certificate requested during descent is smaller in some well-founded order.

None of the obvious measures supplies that theorem:

- The side-condition derivation returned by semantic inversion need not be smaller than the original derivation.
- A CR witness may contain larger terms and more steps.
- Beta substitution, prefix unfolding, and extraction syntax obstruct a simple term-size argument.
- Large elimination and proof irrelevance do not provide a uniform decrease in type complexity.

This does not prove that no clever measure exists. It means such a measure would be a new substantive result about this confluence construction. Merely combining witness size, derivation height, and term size lexicographically does not establish it.

König’s lemma does not repair the gap. Unrestricted eta already makes finite branching problematic. Even after choosing canonical expansions, a finitely branching tree of recursively requested side conditions can have an infinite branch. König gives no contradiction without an independent reason that such a branch cannot exist. An infinite dependency tree is not a finite inductive certificate.

There is, however, a useful middle course between “rewrite everything” and “reuse CR as an opaque oracle”:

**Refactor the existing proof to retain the provenance of the side conditions it constructs, while building a separate supported certificate relation.**

Concretely, reuse the syntactic reduction calculations and overlap diagrams. For each lemma, expose exactly which certificate transformations it needs. Keep semantic head inversion available for negative facts and shape analysis. Replace positive uses that manufacture conversion premises with explicit certificate-producing operations.

This is narrower than demanding that \(J\) behave like the entire declarative theory. A particular strip case might need agreement of two Π-exposures and substitution of that agreement; it need not receive unrestricted uniqueness and context conversion as opaque axioms.

The existing CR proof remains extremely valuable as a map of the critical pairs and their solutions. What it cannot provide automatically is the support/provenance invariant on those solutions.

I would also qualify one sentence in (A): “completeness = new confluence proof by induction on certificate size” is not yet a termination argument. If joining two certificates produces a larger certificate that another recursive call consumes, ordinary size induction fails. The induction must follow proper input dependencies, a decreasing diagram label, or a proved rank discipline. Architecture (A) exposes this obligation more clearly; it does not eliminate it.

**4. My choice is (A)’s invariant, with selective generic reuse—not (B)’s full interface.**

I would proceed in this order:

1. Define supported synthesis and certified Π/structure exposure, with insertion compatibility as an explicit invariant.
2. Define canonical reductions using those exposures and the Eq-cast extraction syntax.
3. Prove a small representative group of difficult strip cases, recording the levels of every input and output certificate.
4. Only then generalize the reusable parts of the existing development.

The representative cases should include `beta_aux` against `etaBoth`, structure-eta transport, and a native iota overlap whose nonlinear checks must be transported. These exercise the main sources of newly manufactured judgments.

**The riskiest lemma is certified coherence of dependent head exposure, strong enough for eta transport and context conversion.** Schematically:
\[
\operatorname{Synth}(e,T),\quad
\operatorname{Expose}(T,\Pi A B),\quad
\operatorname{CertifiedType}(e,\Pi D E)
\]
must produce certified domain agreement and the necessary body/context agreements, at a rank compatible with the strip.

That lemma concentrates several issues:

- synthesis need not be literally unique;
- exposure may have multiple witnesses;
- semantic uniqueness supplies truth but not certificates;
- dependent bodies live in different extended contexts;
- the resulting agreements are consumed by confluence itself.

It is therefore a better early test than a broad mechanical parameterization of `FullStep`.

For size, I would budget **a substantial fraction of the existing 29k-line development, potentially comparable to it**. I do not see evidence for a small bridge proof.

A standalone implementation of (A) risks duplicating most of the confluence machinery. A wholesale implementation of (B) touches much of that machinery *and* adds the difficult hierarchy-instantiation proofs; it could cost more. Selective reuse should save the syntactic calculations and substantial overlap analysis, while the certificate-sensitive typing and transport arguments will require real redevelopment.

The practical decision point is the small prototype above. If exposure coherence and the eta/native-iota transports preserve the proposed level, then (B) becomes credible and potentially cheaper. If they require conversion certificates from the very outer strip being proved, the proposed hierarchy has not removed the circularity, and broad refactoring should wait.

## Prompt

```text
You are reviewing a proof architecture for a metatheorem about Lean 4's kernel type theory as formalized in the Lean4Lean project (de Bruijn VExpr, declarative judgement VEnv.IsDefEq env U Γ e₁ e₂ A with rules bvar, symm, trans, sort/const congruence up to level equivalence, app/lam/forallE/proj congruence, defeqDF, beta, eta, proofIrrel (h ≡ h' : p for p : Prop), extra (closed instL-instantiated rules: delta, native recursor iota, Quot.lift iota), case-schema iota on abstract eliminators, projIota, structEta, unitLike). Impredicative proof-irrelevant Prop, large elimination of syntactic subsingletons, K-like computation. Not normalizing; conversion undecidable. Please think hard; answer in prose with concrete technical content.

GOAL. Strengthening: if Γ' = Γ with extra binders inserted (Ctx.LiftN n k Γ Γ'), Γ' well formed, Γ' ⊢ e₁↑ ≡ e₂↑ : A then Γ ⊢ e₁ ≡ e₂ : A' for some A'. Known false without canonical Eq (a two-singleton countermodel); with canonical Eq present a falsification study found no counterexample, and "singleton eta" (a proof m of a large-eliminating singleton family equals the constructor applied to data read from the indices and proof fields extracted from m itself via Eq-cast motives) is now formally proved.

AVAILABLE (formal, same repo). (i) Uniqueness of types, Π- and rigid-head injectivity, sort inversion, typing inversion — from one semantic obligation (headInversion) proved elsewhere. (ii) Full Church–Rosser in any FIXED context: Γ ⊢ a ≡ b gives a ≫* a', b ≫* b', a' ≡ₚ b'. ≫ (FullStep) is a typed full reduction: ParRed core (beta, native-pattern iota whose nonlinear checks are IsDefEqU premises in Γ, case-schema iota with typing premises), native prefix unfolding (delta of recursor prefixes, with singleton reconstruction about to become the Eq-cast extraction), quotient prefix unfolding, projection iota with typing premises, structure eta expansion (HasType premises), function eta expansion e ⟶ λ(A). e↑ 0 for ANY A with Γ ⊢ e : Π A B. ≡ₚ (NormalEqN, height-indexed) has leaves refl (typed), sort/const up to ≈, proofIrrel (common Prop), and congruences appDF (both functions typed at a common Π, both args at its domain), lamDF/forallEDF (domain premises are full IsDefEq judgements Γ ⊢ A ≡ A₁), etaL/etaR/etaBoth with typing premises. CR is proved by a levelled decreasing-diagrams strip lemma (levels: NormalEq₀, ParRed, prefix/projection deltas, eta expansions). About 29k lines including inductive-generation glue; it uses uniqueness/inversion/declarative transitivity on side conditions a few hundred times.

DIAGNOSIS (from earlier review with you, agreed). Any proof must track provenance of side conditions through confluence: CR in Γ' yields witnesses for q-free endpoints whose side conditions are NEW Γ'-judgements between q-free terms (alignment checks, eta-domain agreements, proof-irrelevance type agreement, typing of reducts), and no well-founded measure orders them below the original. Hence a trans-free certified conversion with finite certificates for side conditions, whose completeness needs admissible transitivity, i.e. confluence redone with certificate premises.

TWO ARCHITECTURES. I want the cheaper sound one.

(A) Standalone certified calculus: mutually inductive Ty (syntax-directed synthesis with certified Π/sort exposure by certified reduction), Step (canonical certified parallel step: every introduced syntax is a subterm, a synthesized type, or extraction syntax), NEq (normal equality with certificate premises), Conv := join modulo NEq. Soundness easy, strengthening structural, completeness = new confluence proof by induction on certificate size. Essentially rewriting the 29k-line development.

(B) Level-indexed generic refactor: parametrize the mainline relations (ParRed/FullStep/NormalEqN and helpers) by the side-condition judgement J (a predicate family for typing and conversion), prove the mainline strip once GENERICALLY under an interface of closure properties of J (soundness into IsDefEq, uniqueness, inversion, subject reduction, substitution, weakening, transitivity, context conversion...). Define levels: J₀ = nothing (no side-conditioned rule usable), J_{n+1} = the CR-witness relation built with side conditions in J_n (plus a certified typing component). By induction on n, the interface for J_n gives the strip for level n+1 relations, which yields the interface for J_{n+1}. Completeness: every declarative derivation has a witness at some level (induction on derivation, trans via the level strip, raising the level). Mainline itself becomes the instance J := IsDefEq. Strengthening by induction on n, PROVIDED the level-n witnesses are canonical (reducts of lifts are lifts) — which mainline FullStep is not (funEta takes any domain A with e : Π A B; structEta parameters from a typing judgement).

QUESTIONS.
1. Is (B) sound as a proof strategy? In particular: does the level hierarchy close, i.e. can every closure operation the generic strip performs on level-n side conditions be realized at level n (uniqueness of synthesized types, transitivity, injectivity, subject reduction), or does something force the level up and break the induction? Where exactly do uniqueness and Π-injectivity for J_n come from without the semantic obligation (for IsDefEq they come from a semantic model)?
2. Canonicity: what is the least invasive way to make witnesses canonical for strengthening? E.g. restrict funEta/structEta to domains/parameters of a SYNTHESIZED type, or keep the non-canonical relation and prove a canonicalization lemma (any witness between lifts can be replaced by one whose intermediate terms are lifts), or handle non-canonical syntax by a "q-erasure" substitution argument. Does restricting funEta domains break the mainline's transports (NormalEqN.beta_aux uses funEta in function position to match an etaBoth side)?
3. Is there any cheaper architecture you now see — e.g. proving strengthening for the mainline witness relation directly by induction on a cleverly chosen joint measure on (witness, side-condition witnesses obtained by recursively applying the fixed-context CR), a König-style finiteness argument, or exploiting that the fixed-context CR is already proved so only "strengthening of side conditions" is missing?
4. Which of (A)/(B) would you choose and what is the riskiest lemma? Give an honest size comparison.
Be concrete and honest about uncertainty.
```
