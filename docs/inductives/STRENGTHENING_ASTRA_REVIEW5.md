The frozen-check idea fixes one local problem, but **it does not establish the proposed input-size induction**. Output compositions survive in certified substitution, synthesis coherence, and context transport. There are also problems before completeness: section 2.1 omits typing needed for soundness, and unrestricted frozen ancestry invalidates its stated support invariant.

I distinguish below between failures of the architecture **as stated** and obligations that might be discharged by a substantially stronger certificate calculus.

**1. Frozen checks and the critical pairs**

There is an initial correction to the diagram being sought. The existing calculus does not supply the exact diamond
`CStep a b → CStep a c → ∃ d, CStep b d ∧ CStep c d`.
Its actual strip theorem returns **two further reducts related by normal equality**, with potentially multiple reduction steps: [LevelledReduction.lean:4593](/home/kim/worktrees/lean4lean/lean4lean-strength2/Lean4Lean/Theory/Typing/LevelledReduction.lean:4593). The different-prefix beta joins are one reason. Freezing checks does not change this syntactic issue.

*(i) Singleton/K against argument reduction.*

For a simple alignment guard, freezing does accomplish something real. Suppose the residual redex has indices `x₁,y₁`, and carries

```text
c : CConv x₀ y₀
rx : CStep* x₀ x₁
ry : CStep* y₀ y₁.
```

When its arguments reduce further, retain `c` and append to `rx,ry`. Soundness derives the current alignment declaratively. No normalization of `c` against the argument reductions is necessary.

This replaces precisely the kind of composition visible in `CaseRedex.congr`: current-source equality is composed with the old guard and generated-LHS congruence at [CaseReduction.lean:780](/home/kim/worktrees/lean4lean/lean4lean-strength2/Lean4Lean/Theory/Typing/CaseReduction.lean:780).

But a singleton unfolding carries more than an alignment equation. Its generated program has a dependent telescope. Changing arguments changes that telescope, the capture types, and the reconstructed constructor. The existing transport explicitly:

- constructs an equality between generated types;
- derives a context conversion between the two telescopes;
- changes capture types;
- transports the resulting checks into the new telescope.

See [ArgumentCongruence.lean:228](/home/kim/worktrees/lean4lean/lean4lean-strength2/Lean4Lean/Theory/Typing/PrefixUnfolding/ArgumentCongruence.lean:228) and especially lines 273–290.

Freezing **the entire replay check in its original telescope**, together with enough transport data, could postpone this work to declarative soundness. Merely freezing index equalities cannot. The former is a new judgment with historical contexts and transport witnesses, whose substitution and support properties must themselves be proved.

Also, the document’s claim that two checks frozen at different ancestors “must be composed” is unjustified. For the same rule and current arguments, the generated RHS does not depend on the proof of its guard. One can retain either valid frozen check and extend its history. `PrefixUnfold.unique` depends on generation, not check identity: [Rule.lean:64](/home/kim/worktrees/lean4lean/lean4lean-strength2/Lean4Lean/Theory/Typing/PrefixUnfolding/Rule.lean:64). Two historical guards are not even necessarily directly composable—their endpoints can differ.

*(ii) Two different prefix lengths.*

At fixed arguments, this case is comparatively benign. If `Pₖ` is the program generated at prefix length `k`, then supplying the additional arguments beta-reduces `Pₖ.rhs` to the longer-prefix program’s RHS.

The implementation is explicit: `prefixUnfolding_supply_many` builds a finite chain of `.beta .rfl .rfl` steps, at [LevelledReduction.lean:2372](/home/kim/worktrees/lean4lean/lean4lean-strength2/Lean4Lean/Theory/Typing/LevelledReduction.lean:2372), with the beta constructor at line 2407. `PrefixUnfold.supply_many` packages this at line 2409.

**This beta chain does not inherently require composing frozen guards.** It creates beta/congruence certificates, not new alignment checks.

When the two branches have also developed their arguments differently, however, first bringing their generated programs into agreement requires argument and telescope transport. The existing `SpineRule.congr_delta` even returns a reduction **plus a `NormalEq₀` comparison**, rather than literal agreement: [LevelledReduction.lean:2668](/home/kim/worktrees/lean4lean/lean4lean-strength2/Lean4Lean/Theory/Typing/LevelledReduction.lean:2668). Freezing the original guard does not remove that comparison.

*(iii) Beta against a body step carrying a bound-variable-dependent check.*

This is a definite surviving obstruction.

The residual of a body step is obtained by substituting into its **whole certificate**, including `CTy` and exposure premises. Substituting its endpoint terms is insufficient.

For an application synthesis node, write the original premises schematically as

```text
CTy f F
R : CExpose F (Π A. B).
```

After substitution, the induction hypothesis generally supplies

```text
CTy fσ S
d : CConv S Fσ.
```

The transformed exposure `Rσ` starts at `Fσ`, not at `S`. To use section 2.1’s application constructor, one must expose `S` to a suitable Π and reconcile its domain and codomain with those obtained from `Rσ`.

The tempting composition

```text
d ; asConv(Rσ)
```

has **outputs of certificate substitution** as arguments. Moreover, this composition only produces a conversion to a Π; turning that into a reduction-only `CExpose` is another required lemma.

At a substituted variable, `d` can come directly from the substitution’s supplied `CCheck`. That does not rescue the general application case: transformed exposures and recursively produced synthesis comparisons are still outputs.

Freezing the body step’s guard changes none of this. The underlying beta rule actually substitutes developed arguments into developed bodies: [ChurchRosser.lean:763](/home/kim/worktrees/lean4lean/lean4lean-strength2/Lean4Lean/Theory/Typing/ChurchRosser.lean:763).

*(iv) `funEta` against reduction of the function.*

Suppose the input eta uses

```text
CTy e F
F →* Π A. B,
```

while `e → e₁`. The straightforward diagram wants

```text
λ A. e↑ 0 →* λ A. e₁↑ 0 ←eta e₁.
```

**Which domain does the right-hand eta use?** Under section 2.1, it must use a domain exposed from a synthesis certificate for `e₁`. Call that domain `A₁`. There is no rule allowing it to use `A` merely because `e` had that domain.

There are two options:

- Resynthesize `e₁`, use `A₁`, and establish certified coherence between the old and new function types, followed by domain comparison and context transport.
- Retain `A` using a new historical-typing/subject-reduction constructor. That changes the stated syntax-directed `CTy`, and requires its own support theorem.

The existing proof can retain an old domain because declarative subject reduction retains an arbitrary assigned type. This freedom appears in `EtaPar.root_fun`: [LevelledReduction.lean:3189](/home/kim/worktrees/lean4lean/lean4lean-strength2/Lean4Lean/Theory/Typing/LevelledReduction.lean:3189). The proposed synthesis discipline deliberately removes that freedom.

Thus frozen **alignment** checks do not solve eta. A newly produced synthesis-coherence certificate still needs composition with exposure or domain-comparison certificates.

*(v) `structEta` against `projIota`.*

For expansion of the major, the term-level calculation is straightforward:

```text
projᵢ (Ctor ps fs)
  → projᵢ (Ctor ps′ [projⱼ (Ctor ps fs)]ⱼ)
  → projᵢ (Ctor ps fs)
  → fsᵢ.
```

The extra projection contraction is the reason this is a finite lower-level path, not necessarily a single step.

But its projection check is **new**: it types a projection of a freshly constructed expansion. The existing proof obtains it by subject reduction, then constructs `.projIota`; see [LevelledReduction.lean:3340](/home/kim/worktrees/lean4lean/lean4lean-strength2/Lean4Lean/Theory/Typing/LevelledReduction.lean:3340), especially lines 3345–3352. The developed-argument case similarly constructs fresh projection and selected-field typing at [LevelledReduction.lean:3653](/home/kim/worktrees/lean4lean/lean4lean-strength2/Lean4Lean/Theory/Typing/LevelledReduction.lean:3653).

These are not copies of input `CCheck`s. With certified synthesis they require synthesis, subject reduction, and dependent field-type coherence.

There is also root `structEta` on the *projection result* versus its `projIota` contraction. Expanding the selected field must use parameters exposed from that field’s synthesized type. Relating those parameters to the expansion chosen before projection repeats the function-eta coherence problem.

So I would not claim a mandatory `CConv.trans` in every syntactic projection overlap. I would claim that the proposed “all output checks are inherited input checks” invariant already fails there.

**2. Tiling and the proposed measure**

Ordinary tiling may legitimately feed diamond outputs into later diamonds. Once a diamond operation is independently proved total, strip induction does **not** require diamond outputs to be smaller.

Here, however, diamond construction calls the very transitivity operation being defined. Therefore a recursive call from a later tile must decrease relative to the **original enclosing transitivity problem**. Being a subcertificate of the current tile’s input does not establish that: the current input may already be a large earlier output.

The outputs divide as follows:

- An unchanged frozen alignment proof can literally be an input subcertificate.
- Its extended ancestry paths are newly constructed; they may contain earlier tile outputs.
- A weakened or substituted frozen proof is a transformed certificate, not literally a subtree. Substitution may insert or duplicate the argument’s typing evidence.
- Different-prefix joining creates beta/congruence certificates.
- Eta creates typing/exposure coherence obligations.
- Projection and dependent capture transport create new checks.
- Normal-equality transport creates new proposition/type comparisons at proof-irrelevance leaves.

The existing global strip makes the output-composition issue especially visible: its final expression is `a2.trans … (b2.symm …)`, where `a2,b2` are **outputs** of converting the joined lower-level paths back into full reductions and normal equalities: [LevelledReduction.lean:4602](/home/kim/worktrees/lean4lean/lean4lean-strength2/Lean4Lean/Theory/Typing/LevelledReduction.lean:4602). The subsequent confluence proof again composes output normal equalities at line 4618.

Those are `NormalEq.trans` calls today, not `CConv.trans` calls. In the proposed calculus, their proof-irrelevance and domain cases consume certified type conversions. Freezing redex guards does not address that traffic.

An upper bound `size(output) ≤ f(size(inputs))` is also insufficient by itself. You need a decreasing rank for recursive calls, or a stable stratification whose closure properties have been proved. The proposed frozen representation establishes neither.

**3. Heterogeneous substitution at proof irrelevance**

The statement needs typed substitutions at the binder type `A`; `CNorm n n'` alone does not say that either term checks at `A`. The existing heterogeneous substitution helper explicitly assumes typing of the substituted term: [ChurchRosser.lean:557](/home/kim/worktrees/lean4lean/lean4lean-strength2/Lean4Lean/Theory/Typing/ChurchRosser.lean:557).

With that corrected, take the leaf

```text
CTy h p
CTy h' p'
k : CConv p p'
CSort p 0.
```

After substitution by `n` on the left and `n'` on the right, ordinary synthesis transport gives something like

```text
CTy h[n] S       dL : CConv S p[n]
CTy h'[n'] S'    dR : CConv S' p'[n'].
```

The new proof-irrelevance leaf needs `CConv S S'`. A standard construction is

```text
S  ~  p[n]  ~  p'[n]  ~  p'[n']  ~  S'.
   dL        k[n]       subst-congr    dR⁻¹
```

Here `dL,dR,k[n]`, and the heterogeneous congruence certificate are transformation outputs. Even a stronger heterogeneous substitution lemma directly producing `p[n] ~ p'[n']` leaves its composition with `dL,dR`.

**Adding frozen types with a `CConv` to current synthesized types does not close this.** It relocates these bridges into the typing certificate. When the bridge is extended or the frozen type must be exposed, the same composition reappears.

One could introduce suspended substitutions and explicit, unnormalized transport histories, with declarative soundness interpreting them. That might avoid *immediate* normalized composition. But it would be a materially different calculus, and would need a new support invariant and a proof explaining how its histories are eventually consumed without circularity.

**4. Descent: useful choices, but not yet a sound specification**

The strict, unfrozen synthesis choices are largely appropriate for descent. Several details need repair.

*Proof irrelevance.* This is the right local choice. If `h,h'` avoid the removed variable, strict synthesis should produce types `p,p'` that also avoid it. Then both endpoints of the proposition-comparison certificate are lifts, so its descent hypothesis applies. Choosing an arbitrary common proposition instead would lose this property.

*Unit-like equality.* Reading both structure types from synthesis and exposure similarly makes their parameters supported. The constructor must additionally enforce the same registered family, compatible universe instantiations, zero indices, zero fields, and certified parameter agreement. These correspond to the conditions in [Basic.lean:117](/home/kim/worktrees/lean4lean/lean4lean-strength2/Lean4Lean/Theory/Typing/Basic.lean:117).

*`elimDF`.* The schema’s generic type is closed, so it introduces no unsupported local variable. But **permission data alone is not all the current typing rule requires**. `IsDefEq.elimDF` also requires the instantiated generic type to inhabit a sort: [Basic.lean:34](/home/kim/worktrees/lean4lean/lean4lean-strength2/Lean4Lean/Theory/Typing/Basic.lean:34), particularly line 42. Retain a certified sort premise, or supply a separate theorem deriving the required typing from the registry. Closedness makes that premise support-compatible; it does not justify silently deleting it.

*Projection synthesis.* Computing `fieldType` from synthesized parameters and the actual major is a good repair. The implementation substitutes parameters and preceding projections of that major: [ProjectionFieldType.lean:17](/home/kim/worktrees/lean4lean/lean4lean-strength2/Lean4Lean/Theory/ProjectionFieldType.lean:17). Its precise lifting theorem is already available at line 73.

This avoids the arbitrary `sourceMajor` permitted by declarative `projDF`. Nevertheless, field-type formation and the projection guard must be certified or separately derived. They are genuine premises of [Basic.lean:49](/home/kim/worktrees/lean4lean/lean4lean-strength2/Lean4Lean/Theory/Typing/Basic.lean:49).

*Unfolding captures and domains.* **Yes, the remaining domains are functions of the arguments.** Generation supplies arguments into the recursor type before taking its remaining forall telescope: [Generation.lean:134](/home/kim/worktrees/lean4lean/lean4lean-strength2/Lean4Lean/Theory/Typing/PrefixUnfolding/Generation.lean:134).

This is compatible with descent, but with binder-aware lifting:

```text
domain j:      liftN n (k+j)
capture:      liftN n (k+numberOfRemainingBinders).
```

It is not an ordinary componentwise lift at one fixed cutoff. The existing `renameDomains` and `PrefixUnfolding.rename` encode exactly this distinction: [Renaming.lean:15](/home/kim/worktrees/lean4lean/lean4lean-strength2/Lean4Lean/Theory/Typing/PrefixUnfolding/Renaming.lean:15) and line 54.

The real hidden-term problem is **`major_prop`**. It existentially chooses `majorType` and checks the fresh major and reconstructed constructor at it: [Rule.lean:40](/home/kim/worktrees/lean4lean/lean4lean-strength2/Lean4Lean/Theory/Typing/PrefixUnfolding/Rule.lean:40). Replacing those typing premises by `CCheck`s leaves `majorType` arbitrary. It can contain the removed variable while being convertible to the supported lookup type.

A support-preserving replacement should use the major’s synthesized lookup type `P`, certify `CSort P 0`, and check the constructor against that `P`. Likewise, “a `CCheck` of the projection redex” does **not** fix its type: by definition `CCheck e A` allows conversion to the externally chosen `A`.

There are two broader failures.

First, **the stated unconditional soundness theorem is false with the listed untyped congruences**. From sort reflexivity, unrestricted `CNorm.appDF` would relate `app Prop Prop` to itself, although this application is ill-typed. Even retaining typed normal reflexivity does not repair `CConv`: an untyped core beta step can take the ill-typed term

```text
(λ x : Prop. Prop) Prop
```

to the well-typed `Prop`.

Existing `FullStep.defeq` therefore requires source typing: [FullReduction.lean:60](/home/kim/worktrees/lean4lean/lean4lean-strength2/Lean4Lean/Theory/Typing/FullReduction.lean:60). You need certified endpoint/source typing or suitable conditional soundness statements. Lambda/product normal congruence also needs domain formation, not merely equality of arbitrary terms.

Second, **“ancestors, hence still lifts” is false**. In context `q : Prop`,

```text
(λ z : Prop. Prop) q →β Prop.
```

The reduct avoids `q`; the ancestor does not. The checked partial file already contains this `badDomain` syntax: [StrengtheningPartial_2026-10-08.lean:182](/home/kim/worktrees/lean4lean/lean4lean-strength2/docs/inductives/history/StrengtheningPartial_2026-10-08.lean:182).

A history generated from an already supported origin remains supported. But a judgment existentially admitting arbitrary ancestors cannot infer that origin’s support from its current endpoints. This breaks the claimed structural descent proof, although it does not itself disprove the existence of some different descending certificate.

Frozen variable types have the same defect: the historical type can mention the removed variable even when the current lookup type does not.

Consequently, I would not classify theorems 1–3 as routine yet. The proposed certified `lam_body` argument also needs a proof-irrelevance case between lambdas, not just `lamDF` and eta; `NormalEqN.proofIrrel` has unrestricted endpoint shapes.

**5. A shortcut to `Cancel`**

I do not see one justified by the available results.

The one-context formulation is valuable, but `lamDF` immediately enters `Q :: Γ`. At `IsDefEqStrong.trans`, the intermediate term need not be a lambda, much less a constant lambda: [Strong.lean:39](/home/kim/worktrees/lean4lean/lean4lean-strength2/Lean4Lean/Theory/Typing/Strong.lean:39). A useful generalized induction hypothesis would have to assign stable “constant values” through arbitrary intermediates and through typing conversions. That is another form of the missing support/coherence theorem.

The common Π type does not solve this:

- `Π Q. T` does not supply an inhabitant of `Q`.
- Syntactic independence of a body does not force every type assigned to it to be syntactically independent of the binder.
- Recovering a supported typing for the body is itself part of strengthening.
- Even a common independent codomain supplies no general cancellation rule for equality of functions on an uninhabited domain.

The established `lam_body` theorem reaches exactly the remaining boundary: equality of the bodies **in the extended context**, using application to the fresh variable and beta: [Cancel.lean:63](/home/kim/worktrees/lean4lean/lean4lean-strength2/Lean4Lean/Theory/Typing/Strengthening/Cancel.lean:63). The inhabited/retraction cases then close by substitution, as already proved at lines 93–109.

A support-indexed logical relation or a direct conservativity proof might avoid this particular completeness theorem. I see no reason to regard either as a shortcut.

**6. Section 5 and groupoid models**

The claim needs qualification, and the sentence about the motive’s functorial action is wrong as a general statement.

In the standard Hofmann–Streicher interpretation, identity proofs are arrows. Allowing distinct parallel arrows is incompatible with proof irrelevance for identity proofs; indeed, the model was constructed to refute uniqueness of identity proofs. [Hofmann–Streicher, LICS 1994](https://www.lfcs.inf.ed.ac.uk/events/lics/1994/HofmannStreicher-Thegroupoidmodelref.html).

Thus, **with that interpretation of `Eq` and ordinary semantic equality of proofs**, the relevant groupoids must be thin. This excludes the usual non-thin groupoid countermodel. It does not exclude all intensional semantics, nor prove that every conceivable groupoid-based interpretation is impossible.

But in a thin groupoid equipped with coherent dependent transport, the displayed motive

```text
(e : n = c) → P (cast e x)
```

can have a perfectly good functorial action. Along `α : n → n'`, transport `x` to `x'` and replace `e` by `e' = e ∘ α⁻¹`. Then

```text
transport e' (transport α x) = transport e x,
```

and dependent functoriality transports the `P` evidence. Thinness does not obstruct this calculation.

The correct rejection of a particular countermodel is therefore: **its chosen equality interpretation, transports, or family action cannot satisfy all the required rules**, or its proposed separation collapses once the extraction term is interpreted. It is not that this syntactically valid motive universally lacks a functorial interpretation.

I found no new concrete counterexample mechanism. However, section 5’s coverage claim remains an argument about known examples, not an exhaustion theorem. In particular, closed definitions can still be applied to context-dependent arguments; closedness alone does not settle interactions involving nontermination, conversions of dependent types, and arbitrary transitivity intermediates.

My assessment is therefore: **retain freezing as a local guard-transport optimization, but reject it as the missing well-foundedness argument in its present form.** Before implementing the large certificate development, repair source typing, canonicalize `major_prop` and projection result types, state an explicit support condition for histories, and test certified substitution and eta coherence. Those tests already contain the unresolved output compositions.
