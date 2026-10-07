# Third review (Astra, gpt-6-astra): termination of certified transitivity

Answer, verbatim:

**I do not have a justified well-founded measure for your proposed mutual proof.** Siles–Herbelin do not supply one that transfers directly: their auxiliary calculus permits precisely some of the intermediate syntax your certificates exclude. There are useful reorganizations, but none of the changes in (b)–(c), by itself, closes the gap.

There is also an important ambiguity: **if your η constructors are literal η-equation leaves, the proposed `Conv` is not transitive.** I will address that first, then distinguish established results from possible approaches.

Take a context containing non-propositional base types \(A,B,C\) and
\[
f:A\to B\to C.
\]
Put
\[
u=\lambda x:A.\,f\,x,\qquad
v=\lambda x:A.\lambda y:B.\,f\,x\,y.
\]
Then `NEq f u` follows by an η leaf, and `NEq u v` follows by λ-congruence and an η leaf in the body. But `NEq f v` cannot follow from congruence, proof irrelevance, or a literal η leaf. All three terms are β-normal, so adding your outer `Red*` witnesses cannot help.

This counterexample does **not** apply if “η leaves” actually means recursive rules comparing a body with an application, such as
\[
\frac{\operatorname{NEq}_{\Gamma,x:A}(m,f\,x)}
     {\operatorname{NEq}_{\Gamma}(\lambda x:A.m,f)}
\]
with suitable typing premises and the symmetric rule. The exact η constructors therefore matter before discussing termination measures.

**(a) What Siles–Herbelin actually prove.** Here is the dependency order, with their numbering.

Applications carry both annotations, \(M_{\Pi x:A.B}N\). Typing is the diagonal of typed parallel reduction \(\Gamma\vdash M\triangleright N:A\). The auxiliary relations include typed multistep reduction and a transitive type equality whose steps may use different sorts. The β rule carries a common ancestor for the abstraction/application domain annotations.

| Result | Induction or dependency |
|---|---|
| Weakening, context conversion, left reflexivity, parallel substitution: 3.2–3.5 | Successive mutual structural inductions on the reduction derivations |
| Type exchange: 3.8 | First reduction derivation; generation on the second |
| Multistep congruence: 3.10 | Multistep derivation, using type exchange |
| Diamond: 3.14 | First typed parallel derivation; generation on the second |
| Church–Rosser: 3.15 | Multistep derivations |
| Confluence: 3.16 | Conversion-path derivation |
| Weak Π-injectivity: 3.17 | Confluence and preservation of Π shape |
| Subject reduction: 3.18 | Untyped parallel-reduction derivation |
| Annotation confluence: 4.1; lifting: 4.4 | Annotated term; PTS typing derivation, respectively |

The crucial substitution conclusion is
\[
\Gamma_1\Gamma_2[P/x]\vdash
M[P/x]\triangleright N[P'/x]:B[P/x],
\]
from a derivation over \(\Gamma_1,x:A,\Gamma_2\) and \(\Gamma_1\vdash P\triangleright P':A\).

Type exchange preserves the reduction while exchanging available types. Diamond joins reductions at both source types. Weak Π-injectivity produces component conversion, without requiring one uniform sort throughout. [Siles–Herbelin, §§3–4](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/0BFD4C10E4EBB7884E906982CD1B017F/S0956796812000044a.pdf/div-class-title-pure-type-system-conversion-is-always-typable-div.pdf).

For your problem, the decisive distinction is between **substitution into a derivation that already checks at \(A\)** and substitution into a derivation that synthesizes its own type.

In the former, the variable case can return the supplied derivation at \(A\). In your system, substituting \(a\) for \(x:A\) returns `Synth a S`, together with `Conv S A`; subsequent typing rules must absorb that discrepancy. This is exactly where your composition obligation enters. An induction valid for the former judgement is not automatically valid for the latter.

Likewise, permitting conversion chains in an *auxiliary metatheory* is legitimate. But translating its result back into your certificate language is a separate elimination theorem. You cannot assume that translation preserves the induction measure.

For typed η and proof irrelevance, the transferable ideas are explicit typing information, strong substitution statements, and separately established transport lemmas. What does not transfer automatically is the diamond argument:

* Typed η introduces interactions between application and abstraction that ordinary β-generation does not settle.
* Proof irrelevance relates terms with unrelated syntax. It therefore requires transport of their proof status and proposition types.

For a concrete η warning, unrestricted reduction on annotated raw terms has the peak
\[
\lambda x:A.(\lambda y:B.y)\,x
\;\longrightarrow_\beta\; \lambda x:A.x,
\qquad
\lambda x:A.(\lambda y:B.y)\,x
\;\longrightarrow_\eta\; \lambda y:B.y.
\]
For unrelated \(A,B\), these need not join. Typed η excludes inappropriate instances, but establishing and transporting the typing restriction is part of the work—not something raw β-confluence proves.

**(b) The proposed measures do not presently justify the recursion.**

**Certificate height with substituted-variable subtrees ignored.** This can justify a *single structural substitution traversal*: recurse on the original derivation, and use the substitution evidence at variables without traversing it.

It does not automatically justify the subsequent composition call. After substitution, an application can expose structure originating in the substituted term, and a synthesized result type can contain duplicated copies of that term. A composition procedure may have to inspect exactly the evidence the proposed height ignores.

A provenance-labelled measure could conceivably work. Its required theorem would be:

> Every recursive composition/transport call has strictly smaller provenance rank, including calls that enter evidence supplied by the substitution.

Merely retaining the original derivation skeleton does not establish this. Some form of cut rank or independent accessibility evidence is needed at that boundary.

**Universe level.** This is not a suitable general cut rank. Π-domains need not lie below the product’s universe level; with impredicative Prop they can lie arbitrarily higher. Moreover, arbitrarily complicated dependencies and function types already occur at one fixed universe level. Putting universe level second in a lexicographic order does not repair an uncontrolled first component.

**Height of a declarative derivation.** Ordinary completeness induction handles proper premises. In the declarative transitivity case it produces two certificates and then needs to compose them. Calling completeness on a newly constructed declarative derivation of their composite does not decrease anything: that derivation contains the transitivity step being eliminated.

There is a legitimate stronger approach: interpret each declarative derivation as something stable under arbitrary suitable substitutions, and prove a fundamental theorem by induction on that derivation. But then composition must already be supported by the interpretation. Choosing an interpretation with this property—and extracting your finite certificates from it—is the substantive theorem.

**Length or structure of the β-peak.** This cannot be the sole measure. The proof-irrelevance/congruence problem remains when all β paths are reflexive.

For example, consider
\[
P:\mathrm{Prop},\quad p,q:P,\quad
F:P\to\mathrm{Prop},\quad
k:\Pi r:P.F\,r,\quad h:F\,p.
\]
Compose proof irrelevance \(h\equiv k\,p\) with congruence \(k\,p\equiv k\,q\). The direct proof-irrelevance certificate needs the proposition conversion \(F\,p\equiv F\,q\). Everything here is β-normal. This small example is easy to certify, but it demonstrates that the relevant obligation is invisible to β-path length.

Induction on a parallel-reduction derivation remains useful **after** the required typing/substitution transport has been established. Carrying those premises along does not establish their closure.

A related idea appears in Carneiro’s thesis: stratify judgements by alternations between typing and equality, then use lower-stage typing information when analysing equality. That is more relevant than universe level, but it is not automatically a certificate rank. [Carneiro, *The Type Theory of Lean*, unique-typing development](https://raw.githubusercontent.com/digama0/lean-type-theory/master/unique.tex).

For your system, such a stratification needs explicit rank bounds for substitution, coherence, and rechecking. In particular, substituting higher-stage evidence into a lower-stage derivation need not preserve its stage. Until those bounds are proved, “induction on alternation depth” is another proposed organization, not a solution.

**(c) What the suggested reorganizations achieve.**

**A common checked type helps locally, but does not solve substitution.** Suppose you have
\[
E_\Gamma(a,b;T),\qquad E_\Gamma(b,c;T),
\]
with checks of all endpoints at \(T\), and evidence that \(T\) is a proposition. Then proof-irrelevance composition is immediate: use the checks of \(a,c\). No coherence theorem for \(b,c\) is needed in that case.

The application case still involves different instantiated codomains. From a function type \(\Pi x:A.B\), arguments \(u,v\) yield types \(B[u/x]\) and \(B[v/x]\). Relating the applications at a common checked type requires substitution and conversion between those instances. Supplying checks at every node makes existing premises accessible; it does not explain how substitution constructs new checks.

There is also a strengthening issue with an **arbitrarily chosen common type**. Even if \(a,b\) omit a variable \(z:D\), a common type could be
\[
T'=(\lambda w:D.T)\,z.
\]
Both endpoints may check at \(T'\), although \(T'\) is not a lift across deletion of \(z\). Thus either:

* strengthening must assume that the common type is also a lift; or
* the type must be selected by a support-preserving discipline.

Existentially hiding an arbitrary common type does not satisfy your original endpoint-only requirement.

**A separate `NEq.conv` lemma needs careful specification.** There are two different tasks:

1. Relabel equality from \(T\) to \(U\), given endpoint checks at \(U\).
2. Construct those endpoint checks from checks at \(T\) and `Conv T U`.

The first may be structurally manageable. The second already contains conversion composition. Indeed, expanding your definition of `Check` gives
\[
\operatorname{Synth}(a,S),\quad
\operatorname{Conv}(S,T),\quad
\operatorname{Conv}(T,U),
\]
and the required output is `Conv S U`.

Calling this operation “retyping” does not make it independent of transitivity.

**Substitution only for `NEq` and `Red` is insufficient with embedded certificates.** At a proof-irrelevance or typed η node, substitution must transform the embedded typing evidence. You need either a substitution theorem for that evidence or a replacement representation whose substitution operation is already available.

Using declarative typing in these leaves would make that transformation easier, but those declarative derivations may contain the forbidden intermediates. A later translation back to certified typing must still eliminate them.

**Changing synthesis can move the difficult operation, but canonical exposure alone does not remove it.** Exact synthesis substitution is generally the wrong statement. The appropriate target is more like
\[
\operatorname{Synth}_{\Gamma,x:A}(e,T)
\;\land\;
\operatorname{Check}_{\Gamma}(a,A)
\Longrightarrow
\exists S.\;
\operatorname{Synth}_{\Gamma}(e[a/x],S)
\land
\operatorname{Conv}_{\Gamma}(S,T[a/x]).
\]
Your variable case already explains why the existential \(S\) is necessary.

Weak-head exposure does not commute strictly with substitution: a neutral type can become a redex after substituting for its head variable. More importantly, β exposure cannot canonicalize distinctions caused by typed η or proof irrelevance. For example, neutral types \(F\,p\) and \(F\,q\) can remain syntactically different while being convertible because \(p,q\) are proofs.

Allowing a fixed number of arbitrary conversion intermediates does not preserve your support condition either. Even one hidden intermediate can mention the deleted variable. The relevant restriction is its provenance, not the length bound.

The organization I would investigate is therefore a **separate auxiliary typing/equality calculus with structurally stable substitution**, followed by a theorem eliminating its unrestricted conversions into the restricted certificates. That separates two issues cleanly:

* auxiliary substitution may use ordinary conversion;
* the elimination theorem must output only permitted certificate syntax.

But I do **not** know an elimination proof for your exact calculus. Saying “use an annotated auxiliary calculus” without proving that final theorem would leave your central problem unresolved.

**(d) I would not claim normalization is necessary.**

First, certificate elimination and term normalization are different assertions. A finite conversion derivation might admit a finite restricted certificate even when its terms have no normal forms. Conversely, knowing some term normalization theorem does not automatically prove that every typing witness in the extracted certificate satisfies your support restriction.

Second, there is now relevant work beyond normalization: the July 2026 preprint *Definitional Inversion, Without Normalisation* proves Π-injectivity using a domain-theoretic logical relation for a theory with typed η and type-in-type, and discusses an extension with a universe of definitionally proof-irrelevant propositions. Its induction is organized using finite semantic approximations. This addresses the claim that η-compatible injectivity must require normalization. It does **not** establish your trans-free certificate completeness theorem. [Carneiro et al., §§2.6–2.8 and 3.6](https://arxiv.org/html/2607.13662v1).

Even independently obtained **declarative** Π-injectivity would only remove part of your cycle. It gives declarative component conversions; producing your **certified** component conversions still requires a translation theorem.

My precise assessment is:

* With literal η leaves, the candidate fails by the counterexample above.
* With recursive η rules, the measures you propose have unproved decrease obligations at exactly the output-composition calls you identified.
* Common checked types improve the local proof-irrelevance case but do not establish closure of certified checks under substitution.
* I know neither a complete normalization-free organization satisfying all your restrictions nor an impossibility theorem against one. I would describe the missing result as **a conversion-elimination theorem with the required support property**, rather than assert that this is a settled open problem or that normalization is unavoidable.

## Prompt

```text
Focused technical question (dependent type theory metatheory; please think hard and be concrete; prose answer).

Setting: a certified (trans-free, finite-certificate) conversion for a dependent type theory with Π, λ, application, sorts (impredicative Prop), constants, untyped β, TYPED η and TYPED proof irrelevance (h ≡ h' when both are proofs of convertible propositions). This is the core fragment of Lean's kernel theory. The certificate calculus must satisfy: (1) soundness into the declarative theory; (2) strengthening by structural induction (every term occurring in a certificate whose endpoints are lifts is itself a lift — so certificates may only mention subterms, synthesized types, and reducts; NO arbitrary intermediate terms, hence no transitivity constructor); (3) completeness from declarative derivations, which requires admissibility of transitivity.

Candidate definitions: untyped parallel β (Red, confluent, canonical). Certified synthesis Synth Δ e T (syntax-directed: var from context, const from environment, λ ⇒ Π, app needs an EXPOSURE of the function's synthesized type F to a Π (say by weak-head β-reduction, deterministic) and a CHECK of the argument: Check Δ a A := Synth Δ a S ∧ Conv Δ S A). Normal equality NEq with congruence nodes, a proof-irrelevance leaf (needs certified typing of both proofs and certified conversion of their propositions), η leaves with certified typing. Conv Δ a b := ∃ a' b', Red* a a' ∧ Red* b b' ∧ NEq Δ a' b'.

The problem: proving Conv.trans by well-founded induction. Dependencies I find:
 - Conv.trans needs β-confluence (untyped, fine), transport of NEq along β (heterogeneous substitution of NEq-related arguments into NEq), and NEq.trans.
 - NEq.trans at a proof-irrelevance leaf composed with a congruence derivation needs "type coherence" (NEq y z, Synth y T₁, Synth z T₂ ⇒ Conv T₁ T₂), whose application case needs injectivity of Conv on Π and the substitution lemma.
 - The substitution lemma for Synth/Check (substitute x with Check x A into a derivation over A::Δ) needs, at the variable case and at application nodes above it, composition of the given Conv S_x A with conversions produced by the substitution — i.e. Conv.trans applied to OUTPUTS of earlier lemma calls, not to sub-certificates of the inputs.
 - Allowing chains of conversions in Check (to avoid trans in substitution) breaks strengthening, because completeness then routes chains through non-lifted intermediate types.
So trans ↔ substitution ↔ coherence are mutually dependent and the recursive calls are on outputs whose sizes can grow (substitution duplicates certificates). I need a well-founded measure or a different organisation.

Questions:
 (a) How exactly did Siles & Herbelin ("Pure Type System conversion is always typable", JFP 2012) break this circularity for PTS (β only)? Describe the precise induction (typed parallel reduction Γ ⊢ M ▷ N : A, annotated syntax PTS_atr, which lemma is proved by induction on what, where Π-injectivity comes from). What carries over to typed η and typed proof irrelevance, and what does not?
 (b) Is there a measure that works here, e.g. a lexicographic order on (certificate height ignoring substituted-variable subtrees, type level), or a "height of the derivation of the declarative judgement that the certificate came from", or an induction on the untyped β-reduction length / derivation of the β-peak with the typing premises carried along?
 (c) Is there a smarter organisation that avoids recursing on outputs: e.g. proving trans only for NEq at a common CHECKED type (typed NEq Δ a b T with Check premises of both sides at every node), proving "NEq.conv" (retyping along Conv) separately, or proving substitution only for NEq/Red and never for Synth, or defining Synth in a substitution-stable way (e.g. allowing a bounded number of conversions, or synthesizing up to a canonical exposure that commutes with substitution)?
 (d) If you believe no such organisation exists without a normalization-like argument, say so and explain the obstruction precisely.
Be honest about uncertainty; I would rather have a precise "this is open" than a hand-wave.
```
