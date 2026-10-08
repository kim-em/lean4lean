# Astra review: a choice-free proof of the projection-walk corner?

Second opinion requested by the lead on 2026-10-08 (`codex exec -m gpt-6-astra`).

## Question

You are reviewing a Lean 4 metatheory development (lean4lean: a verified reimplementation of the Lean 4 kernel; abstract calculus `VExpr` with dependent types, universes, impredicative Prop with proof irrelevance, eta, inductive types with large/singleton elimination rules, projections, structure eta, unit-like eta, quotients, no normalization proof and no Church-Rosser without a canonical-Eq hypothesis). The type theory is declarative (typing judgments `HasType U Γ e A` with a conversion rule using an untyped-ish defeq `IsDefEq`).

The question is about ONE remaining hypothesis of the top-level theorem. Everything else is proved. The theorem now assumes the environment contains the prelude's `Nonempty`, `Nonempty.intro` and the axiom `Classical.choice` with their stored types (`VEnv.HasCanonicalChoice`). It is used at exactly one place, the "projection-walk corner":

The kernel's `infer_proj` for `.proj S j e'` walks the constructor telescope of the structure `S`, instantiating the parameters with `params` and the first j field binders with the projections `.proj S k e'` (k < j), even when such a projection is NOT typable (the typical case: `S : Prop` is a structure-like proposition such as `Exists`, field k is data, so `.proj S k e'` fails the universe guard "resultLevel never zero or field sort is zero"). The implementation of the verified checker matches the C++ kernel. The theorem-side translation relation `TrExprS venv Us Δ body body'` (translation of a kernel `Lean.Expr` `body` into a `VExpr` `body'` in context Δ; it carries typing side conditions at some constructors, e.g. projections need the major typed) was derived under the walked binder `(none, .vlam D) :: Δ`, with the source `body` CLOSED (no loose bound variables) so `body'` does not mention the binder. Needed:

  theorem projectionWalkCorner ... (henv : venv.WF) (hΔ : Δ.WF ...) (hinfo : venv.projections S info)
    (he' : venv.HasType U Δ e' (S ls (params ++ idx)))
    (hwalk : instantiateProjectionParameters T₀ (params ++ (List.range j).map (fun k => .proj S k e')) = some (.forallE D body'))
    (hD : venv.IsType U Δ D)
    (hguard : ∀ u, venv.HasType U Δ D (.sort u) → ¬ ((info.resultLevel.inst ls).IsNeverZero ∨ u ≈ .zero))
    (H : TrExprS venv Us ((none, .vlam D) :: Δ) body body') (hc : Closed body) :
    ∃ b₀, TrExprS venv Us Δ body b₀ ∧ body' = b₀.lift

i.e. strengthening of the translation (and of the typing judgments it carries) across one unused binder `d : D`, where `D` is a data type that is "inhabited in Prop" (the major `e' : S ...` and S's constructor has a field of type D, so `Nonempty D` is provable in Δ by eliminating S into Prop) but no term of type D is available in Δ without `Classical.choice`. With canonical choice the proof is by substitution `d := Classical.choice (S.casesOn e' (fun fields => Nonempty.intro field_k))`, and that is what is implemented.

General strengthening (`Γ, A ⊢ e : B`, e and B not mentioning the variable, implies `Γ ⊢ e : B`) is unproved for this theory. Earlier analysis (two previous reviews by you) concluded that it reduces to a conversion-elimination / certificate-calculus problem with no known proof organisation, because the derivation under the binder may route conversions through `d`-dependent intermediates (e.g. `(fun _ => T) d`, proof terms `out d : P v` feeding singleton or proof-irrelevance computation), and the theory has no normalization and no measure.

Available tools now proved for every WF environment (no extra hypotheses): head inversion / unique typing (Pi injectivity, sort separation, rigid head injectivity, projection field-type inversion), built via a sound shape/observation model with a history induction (`WF.soundEnv`). Church-Rosser is proved only under canonical Eq.

QUESTION: Is there a proof of THIS RESTRICTED corner statement that does not assume `Classical.choice`-style constants, and that avoids the general conversion-elimination problem? Consider in particular: (1) exploiting that the binder type D is in the restricted position (a data field of a Prop structure whose major is in Δ); (2) exploiting the proved unique typing / head inversion; (3) an erasure or environment-extension argument (adjoin a fresh constant c : ∀Δ, D, substitute, then remove c — is there a conservativity/strengthening-over-constants theorem that is easier than strengthening over variables? we believe not, but say why or why not); (4) a Nonempty-indexed semantic argument: since `Nonempty D` holds, is there a way to transport derivations without a term; (5) any published result (e.g. for declarative PTS/CIC strengthening: Geuvers–Nederhof, Luo, Siles–Herbelin; thinning/strengthening in Barendregt's lambda cube) that applies to this theory with proof irrelevance, singleton elimination and eta, and why it does or does not transfer. Be concrete and honest. If the answer is "no known route other than the general problem", say so plainly and estimate what the general problem would take. Also assess: is assuming `HasCanonicalChoice` (true of every real Lean environment after `Init.Prelude`) a reasonable final hypothesis, given the theorem already assumes canonical `Eq`?

## Answer

**I do not know a proof of this restricted corner that avoids both choice and a substantial strengthening/conversion-locality argument.** The additional inversion results are useful, but I do not see them closing the remaining gap. I also found no published theorem that directly covers your calculus.

This is an assessment of available proof routes, not an impossibility result. In particular, I would **not** claim that the corner implies general strengthening, or that choice is logically necessary for it.

1. **The field position supplies propositional inhabitation, but does not constrain the translation’s certificates sufficiently.**

   Taking your derivation of `Nonempty D` as established, the useful information is:
   \[
   \Delta\vdash h:\operatorname{Nonempty}D.
   \]
   It is not that `D` has a particularly simple computational structure. A Prop-valued constructor can package an arbitrary data type as a field.

   Likewise, the closedness of `body` constrains the translated expression, but does not require every type, proof, or conversion intermediate in `H` to avoid `d`. The actual `TrExprS` rules reinforce this distinction: applications, binders, lets, and projections carry typing premises, some with existentially chosen types.

   Eliminating the major into Prop can discharge an **object-level propositional consequence** of having the field. It does not directly discharge a metatheoretic typing certificate that was constructed using the field.

   A possible narrower route would exploit additional *provenance*: perhaps translations produced by this particular telescope walk admit certificates whose dependencies are controlled. But that requires a new invariant on the construction of `H`. It is not supplied by the displayed statement, which accepts any `H` satisfying the translation relation.

2. **Unique typing and head inversion solve identification problems, not removal of dependencies from derivations.**

   Suppose inversion identifies the function type needed by a closed application, or the field type needed by a projection. That tells you which types must agree **in the extended context**. It does not produce their typing or equality derivations in the smaller context.

   The conversion case still has the schematic form
   \[
   \frac{\Delta,d:D\vdash e:C(d)\qquad
         \Delta,d:D\vdash C(d)\equiv B}
        {\Delta,d:D\vdash e:B},
   \]
   where `e` and `B` avoid `d`. Neither premise satisfies the intended induction hypothesis.

   Unique typing can compare `C(d)` with a proposed alternative type. It cannot supply a derivation of that alternative in `Δ`, or remove `d` from the comparison. The same issue occurs with transitivity through a `d`-dependent term.

   The new inversion theorems nevertheless represent real progress: they remove obstacles that often make syntax-directed reconstruction circular. They could support a general reconstruction proof. They are not themselves a reconstruction theorem.

   One technical refinement from the local definitions: `HasType` is reflexive `IsDefEq`, and `IsDefEq` already carries a type index and typing premises. Thus “introduce typed equality” is not, by itself, the missing step. What is missing is a presentation or transformation with **controlled dependencies in intermediate judgments**.

3. **Adding and then removing a fresh constant relocates the same obligation.**

   After adjoining
   \[
   c:\Pi\Delta.\,D
   \]
   and substituting `c Δ`, the resulting expression may contain no `c`, while its derivation contains `c` in intermediate types and equality proofs.

   An environment-restriction theorem requiring the **whole derivation** to avoid `c` is straightforward and useful. Indeed, the local `EnvironmentRestriction.lean` explicitly uses a derivation-level `UsesOnly` predicate for precisely this reason. Substitution does not establish that predicate.

   What you need instead is:
   \[
   E,c:C;\Delta\vdash e:A,\quad
   c\notin FV(\Delta,e,A)
   \quad\Longrightarrow\quad
   E;\Delta\vdash e:A.
   \]
   For an opaque constant with no computation rules, the closed-context case already has essentially the variable-strengthening problem: abstract the constant as a variable, or substitute the constant for the variable. There is no unfolding operation that removes it.

   With a parameterized global constant, there is an additional qualification: arbitrary derivations can use it at other arguments, so unrestricted conservativity may demand more than removing the particular local witness used by your substitution.

   Nor does ordinary logical conservativity automatically establish this result. You need preservation of typing for the **specified expression and type**, not merely preservation of provability of some proposition.

4. **A `Nonempty`-indexed semantic argument needs an additional reflection or descent theorem.**

   There are three different statements here:
   \[
   \Delta\vdash h:\operatorname{Nonempty}D,\qquad
   \llbracket D\rrbracket_\rho\ne\varnothing,\qquad
   \exists t,\ \Delta\vdash t:D.
   \]
   The first can imply the second in a suitable sound model. Neither automatically implies the third.

   For example, in an open context containing an abstract type `D` and `h : Nonempty D`, inversion on the typing of the neutral term `h` does not reveal an object-language witness.

   The tempting argument that “the desired theorem is a proposition, so eliminate `Nonempty` into it” mixes levels. `TrExprS` and `HasType` are propositions in the **metatheory**; the available `h` is syntax representing a proof in the **object theory**. An object-language eliminator does not eliminate that syntax into an arbitrary metatheoretic proposition.

   Semantically, you might prove that a judgment independent of `d` holds at every base valuation by extending valuations with an element of `D`. But recovering a syntactic derivation in `Δ` needs completeness, reflection, or an appropriate locality theorem. A sound shape model yielding injectivity supplies no such converse.

   A syntactic or logical-relations model could conceivably establish precisely that locality property. This would be a substantive alternative proof of strengthening, not a consequence of propositional inhabitation alone. **Failure to extract a witness does not prove that witness-free derivation transport is impossible.**

5. **The literature supplies techniques, but not an applicable theorem for this collection of rules.**

   Geuvers–Nederhof’s functional-PTS strengthening, and the lambda-cube results in this tradition, concern a much more restricted conversion theory. Van Benthem Jutting subsequently proved strengthening for general PTSs using a structural analysis of possible types. These results are evidence that normalization is not inherently required for strengthening; they do not establish that unique typing alone suffices for an arbitrary context-dependent equality relation. [Van Benthem Jutting, *Typing in Pure Type Systems*](https://www.sciencedirect.com/science/article/pii/S0890540183710382)

   Luo’s ECC development likewise provides an important strengthening precedent, with a strengthened induction statement and supporting conversion metatheory. ECC’s result does not directly cover your combination of judgmental proof irrelevance, restricted inductive elimination, projection rules, structure/unit-like eta, and quotients. Transferring it means proving that the supporting argument survives those rules. [Luo, *An Extended Calculus of Constructions*](https://www.cs.rhul.ac.uk/~zhaohui/ECS-LFCS-90-118.pdf)

   Siles–Herbelin prove equivalence between ordinary and typed-equality presentations for **all PTSs**, without a normalization assumption, using annotated typed reduction. Their paper explicitly treats extensions to ECC/CIC and eta as further work. It offers a serious proof architecture, not a ready-made theorem for your calculus. Moreover, making conversion typed is only part of your dependency-removal problem. [Siles–Herbelin, *Pure Type System conversion is always typable*](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/0BFD4C10E4EBB7884E906982CD1B017F/S0956796812000044a.pdf/pure-type-system-conversion-is-always-typable.pdf)

   Since your final theorem already assumes canonical `Eq`, its Church–Rosser theorem is available for an attempted replacement proof under that assumption. That is worth exploiting. However, joining conversion endpoints is not enough unless the joining reductions and their typing premises can themselves be reconstructed without the removed binder. In this calculus, that additional obligation must be checked explicitly.

My estimate is that removing choice should be treated as a **separate metatheory project**, with roughly these deliverables:

- A reconstruction or certificate judgment recording the types and dependencies needed by applications, projections, and eliminators.
- A completeness transformation from the existing declarative judgments.
- A support/strengthening theorem handling conversion intermediates, proof irrelevance, and all the computation and eta rules.
- Transfer back to `TrExprS`, including removal beneath further binders.

There may be a substantially shorter proof using the new inversion infrastructure. I cannot presently provide the induction invariant that makes it work. For planning, I would budget weeks for finding and validating the argument and potentially months for the complete formalization, with considerable uncertainty—not treat this as one remaining routine lemma. Full normalization need not be the target.

**Keeping `HasCanonicalChoice` is a reasonable final hypothesis for soundness over standard post-`Init.Prelude` Lean environments.** The declarations really are present there with the stated types. [Lean’s `Init.Prelude` source](https://github.com/leanprover/lean4/blob/master/src/Init/Prelude.lean)

It is a concrete, checkable environment condition, and the substitution proof gives it a precise purpose. Assuming canonical `Eq` already makes a theorem scoped to canonical library infrastructure a natural presentation, although `Eq` and choice have different logical significance.

I would state the scope explicitly: soundness in environments containing the canonical declarations. This does **not** establish soundness for arbitrary choice-free WF environments, or preservation of the checked term’s minimal axiom dependencies. Subject to that distinction, I would retain the hypothesis and regard its removal as an independent strengthening result, rather than hold up the completed verification for an unestablished shortcut.
