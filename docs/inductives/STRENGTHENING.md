# Dependent singletons and context strengthening

The two-family construction below gives a mathematical countermodel to
unrestricted equality strengthening in the opaque-constants-plus-inductives
fragment. It also challenges strengthening at a fixed result type. This is a
stronger obstruction than the earlier failure of a deterministic selector or
of literal inverse reduction.

The evidence has distinct scopes. `SingletonStrengthening.lean` checks source
admissibility and the exact combination of the branch's equality inference
rules. `SingletonStrengtheningModel.lean` checks the finite semantic
calculations, beta and naturality for arbitrary fibers with object transport,
and the different types returned by the actual generic extensions. The
groupoid interpretation and its soundness for the selected
fragment are argued below; they are not a Lean formalization of the complete
`VEnv.WF` installation and syntax-soundness theorem. Neither milestone is
complete, and no final correctness theorem is claimed proved by these files.

## The claim being challenged

`IsDefEqU.weakN_iff` in `Theory/Typing/UniqueTyping.lean` asserts, in particular,

```text
Γ, q : Q ⊢ e₁↑ ≡ e₂↑     implies     Γ ⊢ e₁ ≡ e₂
```

for every well-formed environment and context, provided the endpoints do not
mention `q`. It does not require an inhabitant of `Q` in the smaller context,
an equality datatype in the environment, or a derivation whose intermediate
terms avoid `q`.

The earlier example `S↑ ≡ fun p => K m v q` did not directly challenge this
claim: its right endpoint mentions `q`. Here **both endpoints omit `q`**.

## Accepted source and the larger-context derivation

Take these earlier opaque constants; in particular they are not parameters
that can be specialized after the inductive declaration:

```text
C : Type
F : C → Type
c : C
P : F c → Prop
leftMap, rightMap : F c → F c
```

Declare two independent families:

```lean
inductive I : (n : C) → F n → F n → Prop where
  | mk (v : F c) (h : P v) : I c v (leftMap v)

inductive J : (n : C) → F n → F n → Prop where
  | mk (v : F c) (h : P v) : J c v (rightMap v)
```

Lean accepts both and generates arbitrary-`Sort u` recursors, with three
indices, zero parameters and `isK = false`. The data field `v` occurs
literally in the result indices; the other field is a proof. This is exactly
the branch's declaration-derived `SingletonElimination` condition. The
headers and fields are well typed using just earlier constants, and there
are no recursive occurrences, lowering auxiliaries or fresh source universes.
The ordinary finite compilation uses the identity source model/restoration.
No equality datatype is needed to form or type these declarations.

In the smaller context take

```text
K : (v : F c) → P v → Type
v : F c
p : I c v (leftMap v)
r : J c v (rightMap v)

SI := I.rec (motive := fun _ _ _ _ => Type) K p
SJ := J.rec (motive := fun _ _ _ _ => Type) K r
```

Both `SI` and `SJ` already have type `Type` there. Add `q : P v`. Proof
irrelevance identifies each major with its own constructor at the **literal
same indices**, giving

```text
SI ≡ I.rec K (I.mk v q) ≡ K v q ≡ J.rec K (J.mk v q) ≡ SJ.
```

Every link has the same sort as its result type. The proof
`InductiveStrengtheningPressure.Abstract.proofMajorJoin` checks this
combination of `IsDefEq.proofIrrel`, `appDF`, iota premises, symmetry and
transitivity in the actual abstract relation. It imports only `Typing.Basic`
and uses no inversion, uniqueness, strengthening or object-language Eq.
Its natural typing/iota premises are explicit; it does not itself build the
entire environment-formation certificate.

The separate source-level `withProof` theorem records the same chain with
Lean's propositional equality. That theorem is not the evidence for abstract
definitional equality, nor a claim that kernel reduction directly compares
the two neutral recursor heads. Lean's imported Eq is not part of the
selected object-language countermodel environment.

## A smaller-context interpretation that separates the endpoints

Let `C` be the one-object groupoid with automorphism group `Z/3`, and let `F`
be its regular action on the discrete fiber `{0,1,2}`. The closed constant
`c` selects its unique object. The fixed type `F c` is discrete, so arbitrary
opaque maps and predicates on it are permitted. Choose:

| v | P v | leftMap v | rightMap v |
|---|-----|-----------|------------|
| 0 | true | 0 | 1 |
| 1 | true | 2 | 1 |
| 2 | false | 2 | 2 |

The index groupoid `(n : C), (v : F n), (w : F n)` is the diagonal cyclic
action on pairs. Its components are classified by `w - v mod 3`. The action
is free: between two points in a component there is exactly one arrow.

The constructor context is the discrete two-point set of inputs satisfying
`P`. For `I`, inputs `0` and `1` land in components `0` and `1`, respectively.
For `J`, they land in components `1` and `0`. Interpret either proposition
family as true on those two components and false on the third. Its proof
fibers are empty or terminal groupoids. Each constructor map is fully faithful
and essentially surjective onto its support.

This interpretation supplies **all dependent large motives**. At a supported
point `x`, let `o(x)` be its unique constructor origin, and `g_x` the unique
arrow from that constructor point to `x`. For any groupoid-valued motive `M`
and constructor branch `s`, define

```text
rec(M, s)(x) = M(g_x)(s(o(x))).
```

For an arrow `h : x → y`, uniqueness gives `o(y) = o(x)` and
`g_y = h + g_x`. Functoriality supplies the section's transport and composition
laws. At a constructor point, the origin is that input and the arrow is the
identity, so beta holds strictly. The construction is natural in motives and
branches and stays in the motive universe. Dependence on the major proof
adds no choice because its fiber is terminal. This is not an interpretation
only of a constant-motive or Prop-elimination fragment.

Now evaluate the smaller context at `v = 2`. Both major types are true at the
pair `(2,2)`. For `I`, that point has constructor origin `0` and connecting
shift `2`. For `J`, it has origin `1` and shift `1`. A shared branch can take
`K(0,*)` to the empty type and `K(1,*)` to the terminal type. The constant
universe motive transports identically, so `SI` and `SJ` denote different,
indeed nonisomorphic, universe objects in an inhabited smaller context.
Meanwhile `P 2` is false. Adding `q : P v` removes this distinguishing point
from the context, exactly as required for soundness of the larger-context
derivation.

Thus unrestricted context reflection would force an equality contradicted
by this interpretation. Choosing the outputs in the opposite order also
refutes reflection at a fixed type: add `z : SI` to the smaller context,
interpret `SI` as terminal and `SJ` as empty, and use the larger-context
equality to cast `z` to `SJ`. Such a term cannot exist at the smaller-context
point. We do not infer failure of existential `VExpr.WF` strengthening just
from this argument; excluding every alternative typing requires more work.

## Base rules, extra rules and limitations

The underlying dependent-Pi and universe interpretation is the groupoid
model of [Hofmann and Streicher](https://people.csail.mit.edu/jgross/personal-website/papers/academic-papers-local/agroupoidinterpretationoftypetheroy.pdf),
sections 4.6–4.8 and 4.12. These supply dependent products, lambda/application
with beta/eta, universes containing small groupoids, and their syntax/equality
interpretation. The specific Prop extension and the two inductive families
here are additional constructions, not results attributed to that paper.

Interpret `Prop` as the discrete two-code type `{false,true}`, decoded as
empty/terminal groupoids. A Pi into Prop is true exactly when every fiber is
true, including when its domain lies in a higher universe. Proof products
are therefore impredicative and their proofs strictly irrelevant. Lambda and
application for proofs are the unique-section correspondence; higher-sort
products use ordinary groupoid sections. Nested size bounds provide the
predicative universe levels. This model does not include a Prop-valued
identity eliminator.

Current formation automatically registers projection metadata even for these
indexed singleton families. Those rules also have an interpretation: return
`o(x)` for the data projection and its unique `P(o(x))` proof for the proof
projection. Their constructor computations hold. Returning the constructor
origin does not identify it with the observed index `v`. The indexed families
do not satisfy the zero-index hypotheses of structure eta or unit-like
equality. There are no quotient declarations or K-like recursors. The native
equations and abstract case equations are covered by the same all-motives
construction. The final desugared-projection theory therefore has the same
obstruction without needing the transitional primitive projection rules.

Adding Eq/HEq later may invalidate this model and supply new extraction
terms. That does not justify a theorem over every earlier `env.WF`: the
equality judgment fixes its environment, and `WF'` does not require Eq to be
present. No Lean-valid source declaration should be rejected to avoid this
example.

## Consequence for the next proof attempt

Do not continue the staged singleton proof while assuming unrestricted
strengthening is an eventual corollary. Check the remaining model/formation
boundary if needed, then design the foundation to retain the context where
an equality was established. Forward weakening and substitution are
unaffected. Inverse transport is justified by an actual typed retraction,
such as an inhabitant of the removed binder type in the smaller context.

For eta, closing equality of fresh-variable applications by lambda congruence
and eta is a sound alternative to erasing a fresh binder from arbitrary head
equality. The current `NormalEq.trans` eta/eta case instead calls
`NormalEq.weakN_iff`; the replacement normal-form argument must handle that
case and its inversion consequences, not merely add a new helper lemma.
A candidate bound indexes comparison derivations by a Nat, charging two for
eta and one for application. In the new eta-both/arbitrary pair, removing
eta costs two while expanding the other comparison costs one, so the sum
of bounds decreases. This avoids a type-normalization assumption and does
not try to compute a Nat by eliminating a Prop-valued proof. Bound-preserving
context transport remains required.

The next difficult call is type alignment: in application/application
transitivity the common function can be assigned two dependent telescopes.
The current proof aligns them using `uniqU`; giving both outer applications
one result type does not supply this missing domain conversion. Eta-both
composition has a related endpoint-retyping call. These must be justified
below inversion before developing the surrounding new comparison library.
Head separation is another necessary case: sorts and forall expressions must
be excluded from function typings and inappropriate proof-irrelevance leaves.
Otherwise eta-both and function eta expansion prevent purely syntactic head
inversion. Restricting eta to neutral syntax would move this requirement to
coverage, not prove it.
Checker cache/context consumers likewise need evidence derived from their
actual origin contexts rather than this generic reflection theorem. Final
checker/producer caller contracts must stay unchanged.

Commands for the design evidence:

```sh
lake env lean docs/inductives/SingletonStrengthening.lean
lake env lean docs/inductives/SingletonStrengtheningModel.lean
```

## The inductive checker's narrow checker context

`AddInductive.Context` carries two local contexts. The main `lctx` holds every
binder the inductive checker opens and is the one read by `getType`,
`mkForall`, `mkLambda` and the generated recursor telescopes. The second,
`checkLCtx`, is the only context embedded `TypeChecker` runs see (the
`MonadLift` instance in `Lean4Lean/Inductive/Add.lean`). Parameters, header
indices, constructor fields, positivity and recursive-argument binders,
recursor indices and higher-order argument binders are opened in both
(`withCheckedLocalDecl`). Majors, motives, minors and induction hypotheses
are opened only in the main context. Closed inputs are checked under `{}`,
cached parameter steps under the first `i` parameters, constructor and
recursor field telescopes on top of all parameters, and each recursive
field's argument telescope under the fields before it.

The point is that every checker fact is then produced in the narrow scope
its verification needs, so no fact has to be strengthened out of a larger
context (the unrestricted strengthening challenged above). Facts about the
main context follow by weakening, which is valid.

Fidelity: the C++ kernel keeps one growing local context and shows each
call all of it. The results agree because a checker run consults the local
context only through `find?` on free variables reachable from its inputs and
their declarations, plus its own fresh binders: it never reads the context
globally. This locality argument is not formalized; binders whose checker
context changed are marked "checker context narrowed" in the source.
