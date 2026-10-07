# Astra (gpt-6-astra) review of the strengthening proof design, 2026-10-06

Prompt (reproduced at the end) (the obstacle of STRENGTHENING_NOTES.md section 3.2 and the certificate design). Verbatim answer:

Your diagnosis of the **gap in the CR-based argument is right**. I do not see a justified well-founded measure that closes it using the black boxes you list. But I would weaken “any proof must track provenance through confluence” to: **a proof needs an additional context-locality theorem, and fixed-context confluence does not supply it**. Certificates are one way to establish that theorem; a semantic argument or a theorem about successful checker computations could establish it differently.

For the cache application, I would pursue the successful-computation theorem first. For full declarative strengthening, your certificate proposal is credible, but its support invariant and its treatment of inferred types need more precise statements before completeness becomes a plausible theorem.

I take your singleton extraction result as a hypothesis here, rather than claiming to have independently established it for every permitted inductive declaration.

(a) The precise gap, and possible ways to reduce it.

Write \(w:\Gamma'\to\Gamma\) for the weakening substitution. Your CR theorem produces witnesses entirely inside the fibre over \(\Gamma'\). Strengthening asks for reflection along \(w\). Neither confluence within each fibre nor ordinary stability under substitution implies this reflection property.

There are two distinct obligations:

1. Reductions starting from expressions in the image of weakening can be chosen to stay in that image.
2. Their justifications can be reconstructed in the smaller context.

Canonical extraction and canonical choices of eta domains address the first obligation. They do not, by themselves, address the second. Replacing an arbitrary proof field by an extraction term removes a syntactic dependency; it does not automatically remove dependencies from the proof that the extraction term has the required type.

Consequently, I agree with your objections to the proposed measures. In particular, choosing a *minimal derivation* of the original equality does not help unless you prove that the new side-condition derivations have smaller complexity. Semantic uniqueness and injectivity supply no such bound. An ordinal measure could conceivably measure a proof transformation rather than term reduction, but establishing its decrease would itself be substantial new metatheory. Non-normalization does not rule out such proof transformations; it simply supplies no measure for them.

There is, however, an important way to reduce the obligations: **reconstruct side conditions from typing below, instead of strengthening the particular side-condition proofs above**.

For example, suppose a native recursor application with a constructor major is already well typed in \(\Gamma\). Comparing the constructor’s result type with the major’s expected inductive type, then applying rigid-head injectivity, can recover parameter and index agreements in \(\Gamma\). Some nonlinear checks therefore need no transport of their original proofs. Likewise, a uniformly proved singleton reconstruction lemma can discharge an entire replay step once its inputs have the appropriate typings below.

This does not dispose of arbitrary K endpoint comparisons, eta-domain agreements, or comparisons of independently inferred types. But I would distinguish:

- checks forced by the smaller-context typing of the redex;
- checks that contain genuinely additional equality information.

Only the latter necessarily remain conversion obligations. This distinction might substantially shrink the interface that requires certificates.

Your shadow generalization fails for the reason you identify. A repair would need a relation that permits intermediate terms with no smaller-context representative, while tracking which computations eventually discard that dependency. That is closer to a logical relation with partial information than to a stronger elementary induction hypothesis. I do not have a closed proof of its application and conversion cases.

Finally, you may not need to *duplicate* the confluence development. A promising engineering experiment is to parameterize its relevant lemmas over a relation supplying side-condition evidence, then determine which closure operations that evidence must support. If those operations can be implemented for certificates, much of the diagrammatic argument could survive. But if the proof repeatedly calls unrestricted declarative uniqueness or conversion, those calls expose exactly the missing certified lemmas. This is a possible refactoring strategy, not a consequence of the current CR theorem.

(b) What the literature actually gives.

Van Benthem Jutting’s *Typing in Pure Type Systems* proves strengthening for general PTSs through an analysis of possible types; normalization is a separate hypothesis for decidability. Thus normalization is not intrinsically necessary for strengthening. The crucial difference is that ordinary PTS conversion is external, context-independent β-convertibility. The published strengthening statement also requires the displayed type to avoid the removed variable. Your context-dependent conversion premises prevent a direct transplantation of that result. [Van Benthem Jutting, 1993](https://www.sciencedirect.com/science/article/pii/S0890540183710382)

Adams proves equivalence between external conversion and judgemental equality for functional PTSs using typed parallel reduction. Siles–Herbelin extend this to arbitrary PTSs using annotated typed reduction, without a normalization assumption. Their application annotations retain precisely the type information that otherwise becomes difficult to recover during reduction and confluence. What carries over is the strategy of making the intermediate calculus sufficiently informative to prove its own structural properties. Their results do not establish that your proof-irrelevance, singleton replay, and eta rules satisfy the corresponding properties. [Adams, 2006](https://research.chalmers.se/publication/504626/file/504626_Fulltext.pdf), [Siles–Herbelin, 2012](https://pauillac.inria.fr/~herbelin/articles/jfp-SilHer11-pts-typed-conv-all.pdf)

Van Doorn–Geuvers–Wiedijk’s *Explicit Convertibility Proofs in Pure Type Systems* is another relevant design reference: it records conversion evidence explicitly and proves equivalence with ordinary PTSs. However, explicit evidence alone does not establish your desired strengthening property. An annotation may mention variables absent from the term obtained by erasing annotations. You additionally need control over the support of the evidence. [Paper and formalization](https://florisvandoorn.com/ptsf/index.html)

For your consumer application, the closest methodological reference is Lennon-Bertrand’s *What Does It Take to Certify a Conversion Checker?* It separates positive soundness from termination, and explicitly observes that strengthening of algorithmic judgements is readily proved by induction while declarative strengthening is difficult. This supports proving locality for successful computations without proving declarative completeness. Its calculus is smaller than yours, so the result is a precedent rather than an applicable theorem. [Lennon-Bertrand, 2025, especially §§4.1–4.3](https://drops.dagstuhl.de/storage/00lipics/lipics-vol337-fscd2025/LIPIcs.FSCD.2025.27/LIPIcs.FSCD.2025.27.pdf)

Coquand’s reduction-free gluing argument does handle impredicative, proof-irrelevant propositions and eta. But the paper explicitly identifies the absence of the problematic cast operation from Abel–Coquand as a boundary of its normalization result. Its semantic architecture is relevant; its normalization/readback theorem cannot simply be extended to your system. [Coquand, 2023](https://research.chalmers.se/publication/547117/file/547117_Fulltext.pdf)

I do not know a published strengthening theorem covering your exact combination of typed conversion, large elimination from syntactic subsingletons, K, eta, and non-normalization.

(c) A semantic proof is possible in principle, but completeness is only half the requirement.

Non-normalization does not preclude a sound and complete semantics for derivability. The syntactic term model already provides one. What it precludes here is the usual package of effective normalization to finite canonical representatives with decidable comparison.

For already well-typed terms, the semantic property you need is that reindexing along a context projection reflects equality:
\[
w^*a=w^*b\quad\Longrightarrow\quad a=b.
\]
For your full existential-typing statement, you also need a way to recover smaller-context typing of raw expressions that descend syntactically.

Neither property holds automatically in a model of dependent type theory. In a set model, equality under \(\Gamma,q:Q\) says
\[
\forall\gamma\;\forall q\in Q(\gamma),\quad
\llbracket a\rrbracket(\gamma)=\llbracket b\rrbracket(\gamma).
\]
At a valuation where \(Q(\gamma)\) is empty, this says nothing. A generic variable in a presheaf model avoids having to choose a closed inhabitant, but does not automatically make restriction along context extension injective.

Likewise, Yoneda’s full faithfulness does not imply that every context projection is an epimorphism. Passing to the syntactic category merely restates the required reflection property there.

A plausible semantic proof would therefore construct a model or gluing in which:

- descending expressions have interpretations retaining their smaller-context origin;
- all declarative rules preserve that information;
- equality of such interpretations yields a finite derivation below.

The output need not be a normal form. It could be a derivation or a finite conversion certificate. That is compatible with non-normalization and undecidability.

The difficult part is validating the model’s conversion and elimination operations without assuming the reflection property being proved. A gluing predicate defined as “this expression has a smaller-context representative” immediately encounters your shadow problem in applications and discarded arguments.

Domain-theoretic interpretations are promising for weaker properties: recent work proves definitional inversion without normalization. But an interpretation that exposes constructor shape is not thereby equality-reflecting; in particular, a domain semantics may identify distinct divergent expressions. The additional readback property would be a substantial strengthening. [Carneiro et al., *Definitional Inversion, Without Normalisation*, 2026](https://arxiv.org/abs/2607.13662)

Thus I regard semantics as a legitimate alternative research direction, not presently a cheaper completed argument.

(d) The cache application admits a substantially narrower target.

Merely saying that the binder came from `withLocalDecl` gives no declarative restriction: such a binder can have an arbitrary well-formed type. The useful restriction is **how the cached fact was obtained**.

I would formulate a theorem about a finite successful execution or its inductively defined trace:

> A successful conversion computation can be replayed after removing declarations outside the dependency support of its inputs, provided its initial cache satisfies the same locality invariant.

The support must include declarations transitively referenced by the inputs’ local-variable types and values. For a type-directed operation, it must also include the expected type. Any auxiliary inference, proof classification, endpoint comparison, or cache lookup belongs to the trace.

The intended proof is mutual induction on successful traces of conversion, type inference, reduction, and their helper operations. Recursive calls are smaller *trace derivations*, even when their expressions or inferred types are larger. Diverging computations produce no successful trace and need not be considered. No declarative completeness theorem is required.

The cache invariant is crucial. “Every entry is declaratively true in the current context” is insufficient. A useful invariant is instead:

> Every entry is valid in every well-formed context agreeing with its recorded dependencies, subject to the input-typing preconditions of the conversion operation.

Alternatively, carry a replayable certificate establishing that property. The certificate may be ghost evidence used only in the soundness proof; the executable need not store it.

Cache hits must consume previously justified evidence. A timestamp or creation order can make the dependency graph acyclic. For caches that store transitive closures or equivalence classes, dependencies must also account for the edges used to establish an equality.

There are two qualifications:

- If conversion soundness assumes the inputs are already well typed, replay alone does not establish their typing below. The caller must provide it, or you must prove locality of the relevant typing computations simultaneously.
- If a binder-free query can consume a cached fact whose justification depends on the removed binder, syntactic inspection of the query does not suffice. The stronger cache invariant is what prevents this circularity.

Your executable’s refusal to reconstruct arbitrary singleton proof majors is helpful because those problematic steps are absent from the trace language. But this restriction must extend to its auxiliary checks: allowing arbitrary declarative equalities as trace premises would reintroduce the original problem.

If the existing checker satisfies this operational locality, the theorem can justify its existing retention policy. If it does not, recording dependency footprints and invalidating entries whose footprints mention the closed binder is a smaller implementation change than establishing full declarative strengthening.

(e) The certificate design needs three distinctions.

First, **finite evidence is not the same as support-controlled evidence**.

Replacing every declarative premise by another finite certificate makes induction available, but does not guarantee that the induction hypothesis applies. You need a rule-by-rule property resembling
\[
\operatorname{supp}(\text{auxiliary inputs and synthesized outputs})
\subseteq
\operatorname{depSupp}(\text{rule inputs}),
\]
with the appropriate treatment of locally introduced binders.

This is a support property, not a literal subterm property. Instantiated definition bodies, substituted codomains, extraction terms, and eta expansions can be much larger than their inputs while still satisfying it.

An unrestricted transitivity constructor violates the desired input-support discipline: its middle expression may mention the removed variable. An arbitrary common-type witness in a proof-irrelevance rule can violate it too. These are not repaired merely by making the premises certified.

Second, **completeness at an arbitrary displayed type differs from completeness at a synthesized type**.

Even if \(c:T\) is closed, in \(\Gamma,q:Q\) it can be typed at
\[
(\lambda z:Q.\,T)\,q.
\]
Thus binder-free endpoints need not have a binder-free displayed type in the original judgement.

A checking certificate that takes that displayed type as an input may legitimately depend on \(q\). Its ordinary strengthening lemma therefore will not prove your existential-type conclusion.

The formulation I would prefer is a synthesizing equality judgement whose primary inputs are the two expressions, and which returns a type together with certified evidence. Its support theorem must cover that returned type. Completeness can then assert the existence of such a certificate, with a separate theorem relating its synthesized type to the original displayed type. Your strengthening conclusion does not require transporting that original type.

This avoids one unnecessary obligation, but type coherence still has to be handled during composition.

Third, **“inferred types only” should allow certified exposure and alignment, not demand syntactic identity**.

Suppose
\[
f:\Pi x:D.\,E
\]
and it is compared with \(\lambda x:A.\,t\). In a function position, expanding \(f\) using \(D\) leaves a domain comparison \(D\equiv A\). Expanding using \(A\) requires certified conversion of the function typing to that domain. Either presentation is reasonable.

What looks too restrictive is requiring every eta annotation to be literally a fixed inferred domain while providing no way to compare that domain with another valid presentation. After reduction, a term’s inferred type may also change syntactically while remaining convertible. Confluence therefore needs coherence between inferred presentations.

I would allow finite certificates for exposing a synthesized type as a Π-type and for aligning its domain with the comparison domain. These certificates need not be produced by a terminating deterministic inference algorithm. Conversely, a design that insists on normalizing every inferred type before proceeding can lose completeness even for reflexivity of terms at divergent types.

The hardest obligations are likely to be:

- **Certified context conversion:** relating bodies under \(\Gamma,x:A\) and \(\Gamma,x:B\), using certified domain equality.
- **Certified type coherence:** obtaining usable equality between synthesized types, rather than invoking unrestricted declarative uniqueness as an oracle.
- **Dependent application and substitution:** transporting codomains and evidence through substitution without requiring expression-size decrease.
- **Proof-irrelevance leaves:** synthesizing and aligning the proposition types, rather than guessing an arbitrary common proposition.
- **Uniform singleton extraction:** certified formation, alignment, and constructor-branch computation across the permitted declaration schema.
- **Composition:** removing unsupported middle expressions while retaining certificates for every newly generated alignment.

The last item is indeed the central completeness problem. Adding unrestricted transitivity makes completeness easy but loses the strengthening argument. Removing it makes support control plausible but demands an admissibility theorem.

I therefore would not yet assert `IsDefEq → CertEq` for the informal design as stated. I would regard it as a plausible target after specifying synthesized versus checked inputs, certified type exposure, context conversion, and support preservation. The canonical `Eq` infrastructure must also be an explicit environment hypothesis wherever singleton extraction is needed.

My concrete next step would be to formalize the successful-trace locality theorem for the cache, and separately prototype the certificate rules for **eta comparison at application heads** and **proof irrelevance with independently synthesized types**. Those two cases should reveal whether the proposed certificate interface closes the actual gap before committing to a full reconstruction of confluence.

## Prompt

```text
You are reviewing a proof design for a metatheorem about a dependent type theory (Lean 4's kernel theory as formalized in the Lean4Lean project). Please think hard; this is a research question. Answer in prose with concrete technical content (no code needed).

SYSTEM. Declarative judgement Γ ⊢ e₁ ≡ e₂ : A (de Bruijn, explicit contexts) with rules: bvar, symm, trans, sort/const congruence (universe levels up to ≈), app/lam/forallE congruence, defeqDF (type conversion), beta, eta (λx:A. e x ≡ e when e : Πx:A.B), proofIrrel (h ≡ h' : p whenever p : Prop, h : p, h' : p), extra (closed definitional rules instL-instantiated: delta for definitions, native recursor iota rules rec ps M minors idx (ctor ps fields) ≡ rhs, Quot.lift iota), projection congruence/iota, structure eta (S.mk (proj 0 e) .. ≡ e for zero-index structures), unit-like (any two inhabitants of a zero-field zero-index structure are equal). Impredicative proof-irrelevant Prop, universe polymorphism, large elimination of inductive propositions only for Lean's syntactic subsingletons (≤1 constructor, every non-Prop field occurs literally among the result indices), K-like reduction (Eq.rec on a proof of a = a) arises as proofIrrel to Eq.refl then iota. NOT normalizing (Abel–Coquand: proof-irrelevant impredicative Prop + K; Acc; looping unsafe defs), conversion undecidable.

STATEMENT (Strengthening). If Γ' is Γ with extra binders inserted (Ctx.LiftN n k), Γ' well formed, and Γ' ⊢ e₁↑ ≡ e₂↑ : A, then Γ ⊢ e₁ ≡ e₂ : A' for some A'. (Equivalently typing strengthening; the two are interderivable using injectivity.)

KNOWN. (1) False in general: two indexed singleton Prop families I, J over opaque C, F : C → Type, c, P : F c → Prop with mk (v : F c) (h : P v) : I c v (leftMap v) (J similar with rightMap); in Γ = (v, p : I c v (leftMap v), r : J c v (rightMap v)), the terms SI := I.rec (λ_.Type) K p and SJ := J.rec (λ_.Type) K r are equal in Γ, q : P v (proofIrrel p ≡ I.mk v q, iota, ...) but separated by a groupoid model in Γ (ℤ/3 action, the constructor origin o(p) differs from the index v). (2) With canonical Eq (Eq, Eq.refl, Eq.rec + iota, universe-polymorphic) present, a falsification study found no counterexample: every proof field of a large-eliminating singleton is extractable from the major itself (motive with type-level equations IdxTy(i') = FieldTy(d'), casts by Eq.rec, K computes in the constructor branch), so p ≡ mk(readData idx, extract p) ("singleton eta") holds in Γ; Quot.{0} similarly; all other mechanisms reduce to conversions between binder-free terms. (3) Available as black boxes: uniqueness of types, Π-injectivity, rigid-head injectivity, sort inversion (from a separate semantic development); full Church–Rosser in any fixed context: Γ ⊢ a ≡ b implies a ⇒* a', b ⇒* b' and a' ≈ b' (NormalEq), where ⇒ is a TYPED parallel/full reduction (beta, delta, native iota on constructor majors with nonlinear pattern checks (conversions between subterms), a 'singleton prefix replay' step that rebuilds a proof major as a constructor after a typing check in the current context, quotient prefix step, projection iota, structure eta expansion and function eta expansion with the domain taken from a typing in the current context) and NormalEq is a congruence with leaves for sorts/consts up to ≈, proof irrelevance (both sides typed at a common Prop), eta (etaL/etaR/etaBoth with typing premises), lam/forallE congruence whose domain premises are full judgements Γ ⊢ A ≡ A₁. All side conditions of ⇒ and ≈ are judgements of the full declarative system IN THE SAME CONTEXT. CR is proved by a levelled decreasing-diagrams strip lemma, about 15k lines of Lean.

THE OBSTACLE. To prove strengthening from CR in Γ': the witness for q-free e₁, e₂ lives among q-free terms if reductions are canonical (proof-major steps rebuild fields by extraction, eta domains are inferred types), but its typed side conditions (typing of reducts, nonlinear pattern checks, alignment checks of singleton steps, eta domain agreements A ≡ dom(type of e') in own-type comparisons such as etaL at the function position of an application, proof-irrelevance type agreement at roots) are NEW judgements in Γ' between q-free terms, i.e. new strengthening instances, not subderivations. I found no well-founded measure: inferred types of subterms are not smaller (multiset of declaration ranks fails because instantiation duplicates arguments), derivation height is lost through uniqueness/injectivity (proved semantically, no height control), derivation size is not preserved by substitution, universe stratification fails with impredicative Prop. The design on the table is a 'conversion-certificate calculus' CertEq: reduction + NormalEq leaves whose every side condition is itself a certificate (or a certified syntax-directed typing), whose rules only introduce subterms, inferred types and extraction terms (so strengthening is a plain induction), with completeness IsDefEq → CertEq proved by induction on derivations; that needs admissibility of transitivity in CertEq, i.e. redoing the whole Church–Rosser development with certificate premises (Siles–Herbelin style typed parallel reduction). Estimated 20–40k lines.

QUESTIONS.
(a) Is my diagnosis right that any proof must track the provenance of side conditions through confluence (i.e. that there is no cheap measure), or do you see a well-founded measure or an induction (e.g. on the declarative derivation in Γ', with a cleverly generalized statement) that avoids redoing confluence? Note: generalizing to 'for all q-free shadows a₀ ≡ a, b₀ ≡ b, Γ ⊢ a₀ ≡ b₀' makes the trans case trivial but breaks the congruence cases (q may occur in data positions with no shadow, e.g. (λz.c) q).
(b) Is there a known technique (literature) for context strengthening / conservativity of a fresh hypothesis in dependent type theories with TYPED conversion (proof irrelevance, eta) and WITHOUT normalization? E.g. Siles–Herbelin 'PTS conversion is always typable', Adams, van Benthem Jutting's strengthening for PTSs, Kripke/presheaf term models, gluing, Coquand's work on irrelevance. What exactly carries over?
(c) Could a semantic method prove derivability here (a model whose soundness plus a completeness/readback property gives strengthening) without normalization, given the non-normalization results?
(d) Any alternative formulation of the conjecture that is cheaper to prove but still implies the consumer uses: the binders removed in practice are binders opened by a type checker (withLocalDecl) whose cached definitional-equality facts about binder-free terms are kept after the binder is closed; the executable never reconstructs a non-K, non-structure proof major as a constructor.
(e) Critique the certificate design: what are the hardest points, and is completeness IsDefEq → CertEq even true as stated (e.g. is the requirement that steps introduce only inferred types compatible with confluence, given funEta must be allowed in function position)?
Be concrete and honest about uncertainty.
```
