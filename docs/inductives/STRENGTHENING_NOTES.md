# Strengthening with canonical `Eq`: falsification study and proof notes

Obligation (b) of `docs/inductives/GOAL.md`:

```lean
theorem VEnv.strengthening_of_canonicalEq (henv : VEnv.WF env) (heq : env.HasCanonicalEq) :
    env.Strengthening
```

`VEnv.Strengthening` (`Theory/Typing/UniqueTyping.lean`): for `Ctx.LiftN n k Γ Γ'` with
`Γ'` well formed, `Γ' ⊢ e₁↑ ≡ e₂↑` implies `Γ ⊢ e₁ ≡ e₂`. The removed binders may sit
anywhere in the context (the `k` later binders are lifts), and may be proofs or data.

## Part 1: falsification study (verdict)

**Verdict: no refutation.** Every mechanism by which a removed binder `q` can produce a
conversion between `q`-free terms reduces, in an environment with canonical `Eq`, either to
a conversion between `q`-free subterms (handled by induction) or to one of two
*reconstruction* facts that hold in the smaller context:

* **singleton eta**: a proof `m : I ps idx` of a large-eliminating Prop family whose type
  is aligned with the constructor pattern is proof-irrelevantly equal to
  `mk ps (readData idx) (extract m)`, where the data fields are read from their literal
  index positions and the proof fields are extracted from `m` itself (section 1.2);
* **quotient eta at `Prop`**: a proof `x : Quot.{0} r` is equal to
  `Quot.mk r (Quot.lift id _ x)` (section 1.6).

The study therefore keeps the statement of `strengthening_of_canonicalEq` unchanged. The
statement is still a conjecture: the argument below is a proof *plan* whose load-bearing
step is the completeness of a conversion-certificate calculus (Part 3), which in turn rests
on confluence (obligation (c)) and on uniqueness/injectivity (obligation (a)).

Kernel-checked evidence: `docs/inductives/StrengtheningFalsification.lean` (plain Lean, no
lean4lean imports, `lake env lean docs/inductives/StrengtheningFalsification.lean`). For
every attacked mechanism it checks the larger-context chain and the smaller-context
replacement, each link an instance of `proofIrrel`, iota, K (= `proofIrrel` + `Eq.rec`
iota), `appDF`, `symm`, `trans`.

### 1.1 Where `q` can enter a chain

In `VEnv.IsDefEq` a binder `q` that occurs in an intermediate term but in neither endpoint
must be erased by some rule. The rules that erase subterms are: `beta` (an unused
argument), `extra`/`elimIota` (unused minor premises, fields, or arguments of a definition),
`projIota` (other fields), `proofIrrel` and `unitLike` (both sides arbitrary). The first
three are untyped erasures: reduction never *introduces* a variable, so in a confluence
argument (reduce both endpoints to a common normal-equal pair) they produce no
`q`-dependence. What can make `q` matter is a step that fires in `Γ'` and not in `Γ` on a
`q`-free redex. Inspecting the rules, the only such steps are:

1. **Iota on a proof major**: `rec … m` with `m` a `q`-free proof (a variable, or neutral)
   becomes `rec … (mk … q …)` by `proofIrrel`, then iota exposes the fields, including `q`,
   in relevant positions (the countermodel). This is the only place where *inhabitation*
   of a proposition (as opposed to a conversion) changes definitional equality.
2. **Typed side conditions** that are themselves conversions between `q`-free terms: the
   K check (`Eq.rec` on `h : a = b` needs `a ≡ b`), the singleton alignment check
   (`idx ≡ pattern(readData idx)`), the domains of `eta`, the propositions of
   `proofIrrel`, the structure types of `structEta`/`unitLike`, the field types of
   `projDF`, `defeqDF` type conversions. These are handled recursively *provided* the
   certificate for the outer conversion contains certificates for its checks (Part 3).

So a counterexample with `Eq` present needs a proof major `m`, `q`-free, whose fields
cannot be rebuilt in `Γ`. The major is `q`-free and typed in `Γ` (it is a subterm of a
reduct of a `q`-free endpoint, in a certificate whose reductions are canonical), so the only
question is whether the fields can be rebuilt **from `m` alone**.

### 1.2 Large-eliminating Prop families: extraction from the major

Lean admits large elimination for an inductive proposition exactly when (C++
`elim_only_at_universe_zero`, lean4lean `isLargeEliminator`, the branch's
`SingletonElimination`): the block has one family with at most one constructor, and every
constructor field after the parameters whose sort is not *syntactically* zero occurs
*literally* among the arguments of the constructor's result type (necessarily at an index
position). Sort-polymorphic families (`Sort u`) are judged by the same syntactic test,
so their `u = 0` instances are covered too. Zero constructors give no iota; zero fields
give K-like families (section 1.3).

For the one constructor `mk : (ps) → (d, h : fields) → I ps pattern(d, h)`, let data field
`dᵢ : Aᵢ(ps, d<ᵢ)` sit at index position `π(i)`, whose *generic* type is
`IdxTyπ(i)(ps, i'<π(i))`. The two types agree at the constructor (`pattern(d,h)` is
well typed), but **not** at generic indices `i'`: in the countermodel `v : F c` sits at a
position of generic type `F n`. This mismatch is exactly why the family's own recursor is
not enough without `Eq` (the spike's `orig p : F c`, `origProof p : P (orig p)` are typed,
but `P v` needs `orig p ≡ v`, the equation the countermodel separates).

**Extraction scheme (no `HEq`, no telescope equalities).** Cast each data field along a
*type-level* equation, an instance of `@Eq (Sort u)`:

```text
d'ᵢ(i', e) := cast eᵢ i'π(i)        where eᵢ : IdxTyπ(i)(ps, i'<π(i)) = Aᵢ(ps, d'<ᵢ)
extractⱼ m := I.rec ps
    (motive := fun i' _ => ∀ e₁ … eₙ (z<ⱼ : T<ⱼ(d', z)), Tⱼ(ps, d', z<ⱼ))
    (fun d h _ e z => hⱼ) idx m rfl … rfl extract<ⱼ(m)
```

* The motive is well typed at generic indices: each equation compares two types that are
  typable there.
* In the constructor branch `i' = pattern(d, h)`, each `eᵢ` is an equation between
  definitionally equal types (by uniqueness of types at the constructor), so `cast eᵢ dᵢ`
  computes by K (`proofIrrel` with `Eq.refl`, then `Eq.rec` iota); hence `d' ≡ d`, and
  `hⱼ : Tⱼ(d, h<ⱼ)` has the expected type `Tⱼ(d', z<ⱼ)` using `proofIrrel` for `z ≡ h`.
* At the major, `rfl` proves each equation once the major's type is aligned with the
  pattern; then `d' ≡ readData idx` by `Eq.rec` iota.
* Proof fields depending on earlier proof fields take the earlier ones as motive arguments
  (any proof will do by irrelevance). Recursive fields (`Acc`) only add unused induction
  hypotheses to the branch. Proof fields occurring as indices are ordinary proof fields.
  Index patterns before a data position that mention later fields are harmless: the
  equations mention only `d'<ᵢ`.

Lean-checked instances (`StrengtheningFalsification.lean`): the countermodel `I`/`J`
(section 0, including the full smaller-context chain `SI ≡ SJ`), a three-index dependent
family whose two data slots both need casts and whose second proof field depends on the
first (section 1), a proof index with a non-injective pattern before a cast data slot
(section 2), a `Sort u` family at `u = 0` (section 3), `Acc` (section 4), a nested
singleton (section 5), `Quot.{0}` (section 6), K-like `Eq`/`HEq` (section 7).

**When `Eq` is genuinely needed.** Only when some data slot's generic index type differs
from the field type (as in the countermodel). When every data field's slot type is
generically the field type (e.g. `Acc`, families indexed by plain variables), the motive
`fun i' _ => Tⱼ(readData i', …)` works with the family's recursor alone.

### 1.3 K-like reduction (`Eq.rec`, `HEq.rec`, any zero-field singleton)

A K step on a neutral major `h : I ps b` needs the index check `b ≡ pattern` (for `Eq`,
`b ≡ a`). Nothing is extracted. The check compares terms of the redex; if they are
`q`-free the check strengthens by induction. Attack: an index equality that holds only
through a singleton chain, e.g. `h : orig p = v` with `orig p ≡ v` only via `q`. With `Eq`,
`orig p ≡ v` already holds in `Γ` (`p ≡ I.mk v (extract p)` by `proofIrrel`, then iota), so
the K step fires in `Γ` as well. Without `Eq` this is the countermodel again.

### 1.4 Unit-like types and structure eta at `q`-dependent types

`unitLike` and `structEta` require zero indices; their typed premises are the structure
type of the `q`-free endpoints. In `Γ` these endpoints have inferred types that are
convertible in `Γ'` to the `q`-dependent one, hence to each other, and those conversions
are between `q`-free terms (induction). Inhabitation plays no role (`unitLike` relates any
two inhabitants, `structEta` builds its constructor from projections of the endpoint).
Prop structures with data fields cannot be eta-expanded (the data projections violate the
`projDF` guard), so no proof major is turned into data by eta.

### 1.5 Removed data binders (item (iv))

`Γ, d : D` with `out : D → P v` in `Γ` (or any function from data to a proof): the
larger-context chain uses `out d` as the proof field. A counterexample needs a redex whose
major is a proof that `d` makes reducible. The major is a subterm of the redex, hence
`q`-free and present (typed) in `Γ`, and section 1.2 extracts the field from it; `out` and
`d` are never needed (`StrengtheningFalsification.lean` section 8, including the case
where the major is bound inside an endpoint's own lambda). There is no variant in which an
endpoint typable in `Γ` reduces through a proof major that is absent from `Γ`: a major
that mentions `d` occurs only in intermediate terms, and the canonical certificate never
passes through such terms (reducts of `q`-free terms are `q`-free once proof-major iota is
the canonical step). The E1 projection corner (a Prop structure with an earlier data
field) concerns typing of untypable projections in the translation, not a conversion
between typable `q`-free terms; it is not a strengthening counterexample.

### 1.6 Quotients

`Quot.{u} r : Sort u`, so `Quot.{0} r` is a proposition and every `x : Quot r` is
proof-irrelevantly `Quot.mk r a` for any `a : α` of the larger context; `Quot.lift f h x`
then computes to `f a`. In `Γ`, `a` is extracted as `Quot.lift (fun a => a) (fun _ _ _ =>
rfl) x : α` (its compatibility proof is `Eq.refl` at a proposition, via `proofIrrel`;
`Quot.lift`'s own type already requires `Eq`). Checked in section 6. `Quot.ind` lands in
`Prop` (irrelevant). `Quot.sound` is an axiom of a proposition and has no computation.

### 1.7 Definitions and `extra` rules

`extra` rules are closed (only `instL`): definitions, native iota rules, quotient rules.
Their instances never mention context variables, and untyped erasure introduces no
`q`-dependence (1.1). The only typed native iota is on proof majors (1.2). Abstract
`.elim` eliminators cannot large-eliminate a proof: `CaseSchema.Permission` requires
`sourceLevel.IsNeverZero ∨ target ≈ 0`, and a proof major needs `sourceLevel ≈ 0`.
Projections cannot read data out of a proof (`projDF` guard).

### 1.8 Universe levels

Strengthening changes only the term context; the universe context `U`, level
well-formedness and `≈` are untouched. Casts use `Eq.{u+1}` at `Sort u`, available since
`Eq` is universe polymorphic in `HasCanonicalEq`.

### 1.9 Unsafe environments

`HasCanonicalEq` does not exclude unsafe declarations. They add (a) delta rules for
possibly looping definitions (`def T := T`): orthogonal, untyped, harmless for a
confluence argument (no normalization is used anywhere); (b) non-positive inductives,
whose large-elimination criterion is the same syntactic test (lean4lean's
`isLargeEliminator` and the C++ kernel do not consult `isUnsafe`), so 1.2 applies; (c)
closed proofs of `False` (e.g. via a non-positive Prop or a looping unsafe definition),
which only make every proposition inhabited in `Γ`, making strengthening easier.

### 1.9a Addendum (found while building the reconstruction): recursor universes

Section 1.2 assumes the family can be eliminated into `Prop`. Lean's kernel always gives a
large-eliminating family a recursor whose motive universe is a fresh parameter, which can
be instantiated at zero. The formal `Instance.Admissible` constrains the target only by
well-formedness, so `VEnv.WF` admits a large singleton whose *only* recursor has motive
universe `succ (param 0)`. Then no proof field is extractable: the recursor's results
live in `Sort (u+1)` (no cumulativity), and `Eq.rec` needs an `Eq` proof, which only `refl`
provides. In the countermodel with such recursors and canonical `Eq`, `SI ≡ SJ` holds in
`Γ, q` and no derivation in `Γ` is apparent; the groupoid separation no longer applies
(`Eq.rec` into `F` cannot be natural on the `ℤ/3` loops), so this is an open candidate,
not a refutation. It does not concern environments built by the checker
(`getElimLevel` returns a fresh `.param`). Decision proposed to the coordinator: tighten the
generative specification so that a target is `≈ zero` or a parameter not occurring in the
instance's levels; meanwhile the native extraction takes that shape as an explicit hypothesis.

### 1.10 Summary table

| Mechanism | Outcome with canonical `Eq` | Evidence |
|---|---|---|
| (i) proof irrelevance + iota of a large-eliminating Prop family | fields rebuilt from the major (singleton eta) | sections 0-5 |
| (i) nested singletons, `Acc`, dependent proof fields, proof indices, non-injective patterns | same | sections 1, 2, 4, 5 |
| (i) `HEq`-like families | K-like, no fields | section 7 |
| (ii) K on an index equality holding only via `q` | equality holds in `Γ` by induction / by singleton eta | 1.3 |
| (iii) unit-like and structure eta at `q`-dependent types | induction on the type conversions | 1.4 |
| (iv) removed data binders, `out : D → P v` | major present, extraction from it | section 8 |
| (v) definitions, `extra` rules | closed, untyped erasure | 1.7 |
| (vi) `Quot` over `Prop` | quotient eta at `Prop` | section 6 |
| (vii) universe levels | unaffected | 1.8 |
| (viii) unsafe environments | same criteria; nontermination harmless | 1.9 |

What remains open is not a candidate counterexample but the proof: a calculus in which
"reducts of `q`-free terms are `q`-free" holds *and* which is complete for `IsDefEq`.

## Part 3: the proof obligation after the study

### 3.1 What is available (2026-10-06, after merging mainline `fe03b4c3`)

* `IsDefEq.full_church_rosser` (`FullChurchRosser.lean`), now without `sorry`
  (`FullStep.strip` is proved by the levelled decreasing-diagram development,
  `LevelledReduction.lean`), under the `Params` and `FullEquationCoverage`
  instances: `Γ ⊢ a ≡ b` gives `a ≫* a'`, `b ≫* b'` and `a' ≡ₚ b'`, all in the
  *same* context `Γ`.
* Uniqueness of types, Π- and rigid-head injectivity, sort inversion, through
  `VEnv.WF.headInversion` (obligation (a)).
* Singleton eta with canonical `Eq` (Part 2; formalized, see below).

The remaining sorries of the project are `VEnv.WF.headInversion` and
`VEnv.strengthening_of_canonicalEq`.

### 3.2 Why confluence in `Γ'` does not by itself give strengthening

For endpoints `e₁, e₂` not mentioning the removed binder `q`, confluence in `Γ'`
gives a witness among `q`-free terms *provided* every reduction step is canonical
(eta domains and structure parameters taken from inferred types, proof-major
computation rebuilding fields by extraction rather than by replaying a typing
check in the current context). The witness's *side conditions* are judgements of
`VEnv.IsDefEq` in `Γ'`:

1. typing of reducts (subject reduction; harmless once the step itself is valid in
   `Γ`);
2. nonlinear pattern checks of native iota (`rec ps … (mk ps' fields)`: `ps ≡ ps'`,
   index agreement): *forced* by typing of the redex in `Γ` via injectivity, so
   harmless;
3. alignment checks of proof-major computation (K: `Eq.rec … b h` with
   `h : a = b` needs `a ≡ b`; singleton: `idx ≡ pattern(readData idx)`): **not**
   forced by typing; a new strengthening instance between subterms of a *reduct*;
4. normal-equality leaves: in a congruence the two sides' types are forced by the
   heads (variables and constants have declared types; arguments are compared at
   the head's instantiated domain), *except* for eta at the function position of an
   application and `etaBoth` between functions of different `Γ`-types, where
   `λ (x : A). e ≡ₚ e'` needs `A ≡ dom(type of e')` in `Γ`: a new strengthening
   instance between a lambda domain and the domain of an inferred type;
5. proof irrelevance at the root needs the two `Γ`-propositions convertible: a new
   instance at the level of types (harmless: one level up the next comparison is at
   a sort).

Items 3 and 4 are strengthening instances that are not subderivations of anything
in hand. No well-founded measure orders them below the original instance:

* inferred types of subterms are not smaller (the multiset of declaration ranks
  fails because instantiating a declared type duplicates arguments, which may
  contain later declarations);
* derivation *size* is not preserved by substitution; derivation *height* is
  additive under substitution but lost through uniqueness and injectivity, which
  come from the semantic obligation (a) without height control;
* universe stratification fails with impredicative `Prop`;
* reducts are unbounded (no normalization), and the checks of item 3 compare
  subterms of reducts.

Generalizing the statement to "for all `q`-free shadows `a₀ ≡ a`, `b₀ ≡ b` in
`Γ'`, `Γ ⊢ a₀ ≡ b₀`" and inducting on the `Γ'` derivation makes the `trans` case
trivial (a shadow of one endpoint of the left premise is a shadow of the middle
term), but breaks every congruence case: a shadow of `f x` need not decompose into
shadows of `f` and `x` (with `x` a data occurrence of `q`, as in `(λ z. c) q`, there
is no shadow of `x`).

Conclusion: any proof has to keep the provenance of side conditions through
confluence. This is the design's conversion-certificate calculus: certificates
whose side conditions are themselves certificates, so that strengthening is a
structural induction, and whose completeness `IsDefEq → CertEq` needs
transitivity to be admissible for certificates, i.e. the strip lemma redone with
certificate premises (Siles and Herbelin's method for PTS conversion, for the
much richer rule set here).

### 3.3 Pilot: strengthening a normal-equality witness without certificates

Setting: `Γ' ⊢ x↑ ≡ₚ[n] y↑` (`NormalEqN true n`), `x`, `y` typed in `Γ`. Induction
on `n` in two modes: *common* (`Γ ⊢ x : T`, `Γ ⊢ y : T`) and *own* (each side its
own `Γ`-type, neither side a proof). Uniqueness, injectivity and inversion in `Γ`
are used freely (obligation (a)).

Cases that close:

* common mode at a proposition `T`: `proofIrrel` in `Γ`, whatever the rule;
* `refl`, `sortDF`, `constDF`, `elimDF`;
* `forallEDF`: domains at a common sort (`Γ' ⊢ A₁ ≡ A₂` gives `Sort u₁ ≡ Sort u₂`,
  hence `u₁ ≈ u₂`; levels are context-free);
* `lamDF`, `etaL`, `etaR` in common mode: `T ≡ Π A T_e` from the lambda's own typing,
  injectivity aligns domains and bodies are compared at a common type;
* application spines whose head is a variable, constant or abstract eliminator: argument
  types are forced by the head's declared type;
* eta at an application head, `(λ A. e) a₁ ≡ₚ e' a₂`: if the arguments are proofs,
  substitute `a₁`/`a₂` heterogeneously (each `refl` leaf on the bound variable becomes a
  `proofIrrel` leaf, index preserved), giving `e[a₁] ≡ₚ[n₁] e' a₂` with
  `n₁ < n₁ + n₂ + 3`; otherwise compare the arguments first (own mode, index `n₂`),
  which aligns `A` with `dom(type e')` through uniqueness, then substitute the same
  argument (`NormalEqN.instN`, index preserved) and close with congruence in `Γ`;
* lambda-headed redexes `(λ A₁. e₁) a₁ ≡ₚ (λ A₂. e₂) a₂`: the same two cases.

**Statements that fail** (each is a strengthening instance between `q`-free terms
that is not bounded by `n`):

1. `lamDF`/`forallEDF` in *own* mode (bare lambdas compared as non-proof arguments or
   in function position): the domain premises are full judgements
   `Γ' ⊢ A ≡ A₁ : Sort u`, `Γ' ⊢ A ≡ A₂ : Sort u`, and the step needs
   `Γ ⊢ A₁ ≡ A₂`.
2. `projDF` with majors of different `Γ`-types `S ps₁`, `S ps₂`: needs
   `Γ ⊢ ps₁ ≡ ps₂` (the two field types are computed from independently synthesized
   parameters).
3. `etaBoth` at a type `T` that is a `Π` only after reduction: needs
   `Γ ⊢ T ≡ Π A B`, i.e. the reduction of `T` valid in `Γ`.
4. Reduction steps of the witness: K and singleton alignment checks
   (`Γ' ⊢ a ≡ b` for `Eq.rec … b h`, `h : a = b`; `idx ≡ pattern(readData idx)`).

A certificate calculus closes 1–3 locally: the needed agreement is obtained by
certified transitivity from sub-certificates (the typing certificates of the two
sides), and 4 by making the check a sub-certificate. All of them then rest on one
global fact, admissibility of transitivity for certificates. That is the strip
lemma with certificate premises. The mainline strip cannot be reused by
instantiation: its proofs call uniqueness, inversion and declarative transitivity on
premises several hundred times (`LevelledReduction`: 17 `uniq`, about 120 inversion and
95 transitivity uses), and for certificate premises each of these needs certified
transitivity on smaller certificates, so the strip has to be restated as an induction
over certificate size.

## Part 2: singleton eta (formal, abstract layer)

`Lean4Lean/Theory/Typing/CanonicalEqTyping.lean`: typing of `Eq`, `Eq.refl`, `Eq.rec`
applications under `HasCanonicalEq`; the type cast `typeCast u X Y e x` along
`e : @Eq (Sort u) X Y`; K for casts (`IsDefEq.typeCast_refl`: proof irrelevance to
`Eq.refl`, then the stored `Eq.rec` iota rule).

`Lean4Lean/Theory/Typing/SingletonExtraction.lean` (no `sorry`; uses uniqueness of types,
i.e. obligation (a)):

* `CastSpec` and `CastSpec.tel`: the cast telescope, parametric in providers (parameter
  and index arguments); `tel_subst`, `target_subst` (substitution of providers),
  `tel_instOuter`, `tel_dom_instOuter`, `target_instOuter` (instantiating the cast binders);
* `tel_typed`: the telescope is well formed and the cast substitution is a typed field
  instance, at any typed providers;
* `tel_branch`, `tel_branch_target`: in the constructor branch every cast computes (K);
* `PropElim`, `PropElim.WF`: an abstract interface for elimination of the family into
  `Prop` (the `elim` field is the eliminator's typing for an arbitrary motive and branch);
* `PropElim.value_typed`: the closed extraction function of proof field `j` is well typed
  (a function of parameters, generic indices, major and the cast telescope);
* `PropElim.occ`, `occ_typed`: at an occurrence aligned with a typed field instance, the
  reconstruction (data from indices, proofs by extraction with `Eq.refl` cast arguments) is
  a typed field instance equal to it field by field;
* `PropElim.singleton_eta`: `m ≡ mk ps (reconstructed fields)`.

From a registered native recursor to `PropElim.WF` (no `sorry`; the only
`sorry` dependency is `VEnv.WF.headInversion`):

* `Lean4Lean/Theory/Inductive/InstanceSpecialize.lean`: `Instance.specialize` and
  `recursorType_specialize`. Instantiating a generated recursor type's universes gives
  the recursor type of the specialized instance.
* `Lean4Lean/Theory/Typing/NativeSingletonTyping.lean`: the telescopes of a singleton
  family are typed from the recursor type alone. The family and constructor headers are
  only related to the normalized telescopes up to definitional equality in larger
  contexts, so they cannot supply this typing. The motive is instantiated at
  `fun is m => ∀ p : Prop, p → p` (`trueTy`). Every induction hypothesis is then
  inhabited (`HasType.inhabit_trueFamily`). Instantiating the minor premise's context
  gives the field telescope's typing (`minorFields_inst`, `minorHyps_inst`), and the
  constructor's result indices typed along the index telescope (`minorBody_inst`). The
  sort of a data field equals the sort of its index slot, by uniqueness of types
  (`sort_agree`). `Instance.singletonElim_wf` assembles `PropElim.WF` for any instance
  with elimination universe zero.
* `Lean4Lean/Theory/Typing/NativeSingletonPropElim.lean`: `SingletonFacts`
  (`singletonFacts`), the definitions `castSpec`, `castSpecGeneric`, `propElim`,
  `propParams`, `genericSorts`, and `NativeRecursorData.propElim_wf`. The occurrence's
  specification is by definition the universe instantiation of the generic one. The data
  sorts are chosen with `Classical.epsilon` at the generic universes. The eliminator is
  the native recursor itself, with its free elimination universe (`Instance.FreeTarget`)
  set to zero.

The integration into `NativePrefixProgram` is done on the confluence branch. It replaces
the `Eq`-free proof selectors, which are ill typed for families such as the
countermodel's.

## Part 3 design: the conversion-certificate calculus

### What has to be certified

From the pilot (3.3) and the K-evidence analysis: the strengthening phase is structural
except where a premise compares two `q`-free terms whose types are not forced by the
heads. These premises are (a) alignment checks of proof-major computation (K and
singleton steps, quotient lifts at `Prop`), whose evidence originates in (b) the type
agreement of proof-irrelevance leaves between independently typed proofs, which in
turn requires (c) agreement of synthesized types of subterms (application domain
against argument type, lambda domains in own mode). (c) is typing strengthening, which
is equivalent to strengthening (each is derivable from the other with injectivity), so
typing has to be certified as well: the calculus is a *synthesizing* certified typing
together with certified conversion, as Astra recommends.

### Judgements (all in one context `Δ`, mutually inductive)

* `CTy Δ e A`: syntax-directed typing; `A` is synthesized from `e` and the context
  (variables, constants with `instL`, `Π`/`λ`/application with certified domain
  agreement `CEq Δ dom(T_f) T_a`, projections, eliminators). Every type that appears is
  built from subterms of `e`, context entries and constant types.
* `CStep Δ a a'`: one step of the full reduction with every typed premise replaced by a
  certificate: beta; delta and native iota on constructor majors (their nonlinear
  checks become `CEq` of subterms); proof-major computation with the `Eq`-cast
  reconstruction of Part 2 (premise: certified alignment of the indices); quotient
  lift at `Prop` via extraction; projection iota; function and structure eta expansion
  whose domain and parameters are the *synthesized* ones (`CTy`).
* `CNorm Δ a b`: deep normal equality: congruences, `≈` levels, proof irrelevance with a
  certificate `CEq Δ T_a T_b` of the synthesized types, eta (`etaL`/`etaR`/`etaBoth`)
  with synthesized domains, and *domain* premises of `λ`/`Π` given as `CNorm` (not full
  judgements).
* `CEq Δ a b := ∃ a' b', CStep* a a' ∧ CStep* b b' ∧ CNorm a' b'`.

### Theorems

1. Soundness: `CTy → HasType`, `CEq → IsDefEqU` (each rule is an `IsDefEq` instance;
   the proof-major step uses `PropElim.singleton_eta`).
2. Strengthening: every rule's premises and introduced terms are subterms, synthesized
   types or `Eq`/extraction syntax built from them, all of which are lifts when the
   conclusion's terms are; induction on the certificate.
3. Completeness: `IsDefEq Δ a b A → CEq Δ a b` (and certified typing of both sides), by
   induction on the declarative derivation. All cases are direct except transitivity,
   which needs `CEq.trans`: confluence of `CStep` modulo `CNorm`, i.e. the strip lemma
   restated with certificate premises and proved by induction on certificate size, so
   that every premise rebuilt inside a peak comes from certified transitivity,
   inversion and uniqueness applied to strictly smaller certificates.

The mainline strip (`LevelledReduction`, decreasing diagrams over levels 0–3) is the
template: its diagram analysis carries over verbatim; what changes is every place where
a premise is produced, which must now produce a certificate.

## Part 3 status (2026-10-06): the missing metatheorem

Two further design reviews were recorded in `STRENGTHENING_ASTRA_REVIEW2.md`
(architecture) and `STRENGTHENING_ASTRA_REVIEW3.md` (termination of certified
transitivity).

The certificate route needs the following theorem. Let `Synth`, `NEq` and `Conv` be a
certified typing / normal equality / join calculus for (at least) the fragment
Π, λ, application, sorts, constants, untyped β, typed η, typed proof irrelevance. Each of
them contains only subterms, synthesized types and reducts of its endpoints, so it has
no transitivity constructor. The theorem says: for these relations transitivity is
admissible, `Conv Δ a b → Conv Δ b c → Conv Δ a c`.

Every organisation tried so far has a circular dependency.

* Transitivity needs NEq to be transported along β, which is a heterogeneous
  substitution of NEq into NEq.
* That substitution passes through the typing evidence embedded in the
  proof-irrelevance and η leaves, so it needs substitution for `Synth`/`Check`.
* Substitution for `Synth` needs conversion composition already at the variable case:
  `Synth x S`, `Conv S A`, `Conv A T[x]` must give `Conv S T[x]`. The arguments of this
  composition are outputs of earlier calls, not sub-certificates of the inputs, and
  substitution duplicates certificates, so their size grows.
* Checking at a common type removes the proof-irrelevance case. It does not remove the
  substitution case.
* Allowing chains of conversions inside `Check` breaks strengthening, because the
  middle types may mention the removed binder.
* Neither universe level, derivation height, nor β-peak structure gives a decreasing
  measure (see the review).

Siles and Herbelin's typed parallel reduction (PTS, β only) does not transfer directly.
Their auxiliary calculus allows exactly the intermediate syntax that the support
discipline forbids, and they never translate back into support-preserving
certificates.

No proof organisation of this conversion-elimination theorem that avoids a
normalization-like argument is known, nor any argument that one cannot exist. Lean's
theory does not normalize. So at this point route (b) rests on an open metatheorem;
the remaining work is not merely large.

## Assessment: the restricted projection-walk corner (`ProjectionWalkCorner`, branch -e1)

Statement (Verify/Typing/ProjectionCorner.lean on agent/verify-inductives-e1). There is a
structure `S` with a typed major `e' : S params idx` in `Δ`. The projection walk reaches
the binder `∀ D, body'` for a field `j` whose projection fails the guard: `S` may be in
`Prop` and `D` is not. A closed source `body` translates to `body'` under `d : D`. The
claim is that it translates without the binder, to the unlifted residual.

**Without a term of `D`, the restriction gives no measure.** The typing derivation of
`body` under `d` may route conversions through arbitrary `d`-dependent intermediates.
Examples are `(fun _ => T) d`, and proofs `out d : P v` that feed singleton or
proof-irrelevance computation, as in the countermodel. The major does give, in `Δ`, every
*closed* proposition that is provable from `d`: eliminate `S` into `Prop` with a constant
motive and use the field in the minor. That is a semantic fact. It does not bound the
intermediate syntax of a declarative derivation. Rebuilding the derivation in `Δ` is
therefore the same conversion-elimination problem as in the general case (Part 3 status
above), restricted only in which binder is removed. For the extreme instance `S := Nonempty D`
the corner *is* strengthening across `d : D` under the hypothesis `Nonempty D`.

**With canonical `Nonempty` and `Classical.choice`, the corner is provable now, by
substitution, without certificates.** Both are declared in `Init.Prelude`
(`class inductive Nonempty (α : Sort u) : Prop | intro (val : α)` at line 792,
`axiom Classical.choice {α : Sort u} : Nonempty α → α` at line 818). So every environment
that replays the prelude, and so contains canonical `Eq`, contains them too.
Construction in `Δ`:

1. Eliminate `S` into `Prop`: use `S`'s registered native recursor with target universe 0,
   the motive `fun x => Nonempty D[x]` (where `D[x]` is the walked binder type with `e'`
   replaced by `x`), and the minor `fun fields => Nonempty.intro field_j`. This gives
   `hne : Nonempty D`. The minor is typed because in the constructor branch the projections
   in `D[mk ps fields]` reduce by `projIota` to the fields. `IsType D` in `Δ` ensures that
   `D` mentions only projections that pass the guard, that is proof fields when `S` is in
   `Prop`.
2. Take `d₀ := @Classical.choice D hne : D` in `Δ`.
3. Substitute `d := d₀` in the translation and typing derivation of `body` under the binder.
   Since `body` is closed, its translation `body'` does not mention `d`, so
   `body'[d₀] = b₀` with `body' = b₀.lift`. This needs a substitution lemma for `TrExprS`
   at a bound variable instantiated by a typed term. Instantiation lemmas for free
   variables exist (`TrExprS.instantiateFVar` and relatives).

What this costs: a hypothesis `VEnv.HasCanonicalChoice` (the exact types of `Nonempty`,
`Nonempty.intro`, the recursor `Nonempty.rec`, and `Classical.choice`, as installed by the
prelude replay), stated like `HasCanonicalEq` and discharged where `HasCanonicalEq` is.
Adding it to `addDecl.WF_of_canonicalEq` changes the top-level hypotheses, so it is a lead
decision.

The construction above is about 1-2k lines. Most of it is typing the elimination of `S`
into `Prop` with a projection-bearing motive, plus the `TrExprS` substitution lemma.

`Classical.choice` does not similarly reduce *general* strengthening. Removing `q : Q`
needs `Nonempty Q` in the smaller context, which is not available. Substituting
`q := choice h` only replaces the binder by the `Prop` hypothesis `h : Nonempty Q`, and
that is strengthening again.

### Implementation status (2026-10-07): ordinary case proved

The corner is proved for ordinary structures, that is one family and one constructor, without
nested auxiliaries.

- `VEnv.corner_inhabit` (`Theory/Typing/ProjectionCornerElim.lean`): at a typed major of `S`,
  the binder `D` reached by the walk past a field that fails the guard has an inhabitant in
  `Δ`.
- `projectionWalkCorner_of_choice` (`Verify/Typing/ProjectionCornerChoice.lean`) has exactly the
  conclusion of `ProjectionWalkCorner` for one environment. Its two extra hypotheses are
  `venv.HasCanonicalChoice` and `venv.StructurePropRecursor Us.length S info ls`.

The construction differs from the sketch above in one point: the motive does not abstract the
major. It is the constant `fun _ => Nonempty X`, where `X` is the walked binder at the actual
major `e'` and is level-equivalent to `D`. Everything is built in `Δ`, after instantiating the
recursor's parameters at the actual parameters:

- `minor_instOuter` computes the instantiated minor premise as a substitution.
- The field variable's type is `X` lifted, by `VProjectionInfo.field_of_walk` at the major
  `e'` lifted past the fields. The projections that `X` uses are proof fields, equal to the
  corresponding field variables by proof irrelevance.
- The constructor application is typed along the source constructor telescope. This uses the
  context equality between the signature's telescope and the source constructor's, which
  comes from `NativeRecursorRegistered.ordinary`.

No `TrExprS` induction is needed beyond `weakBV_inv₁_inhabited`.

`StructurePropRecursor` bundles the following facts:
- the registered native recursor data;
- the one-family and one-constructor sizes;
- the family name and its empty indices;
- the constructor name;
- the parameter count;
- the field count `nparams + fields = ctorType.forallArity`;
- universe levels `ls0` with `data.target.inst ls0 = 0`, whose family levels are equivalent to
  `ls`.

The last three cannot be derived from `NativeRecursorRegistered` alone:
- `Instance.Admissible` does not tie `g.levels` to the source universes;
- the field count follows only from the literal constructor tail, a Verify-level fact, or from
  head inversion.

They are for the call site (E1).

`#print axioms VEnv.corner_inhabit` shows `sorryAx`. It comes only through unique typing
(`IsDefEq.uniqU`), which depends on the open `headInversion` and `strengthening_of_canonicalEq`
sorries, like every other use of uniqueness in the branch.

## Parked (2026-10-07): state of the obstacle, for Mario

Route (b), declarative strengthening `VEnv.strengthening_of_canonicalEq`, is parked. It is no
longer on the critical path. The E1 cone contains no `Strengthening` hypothesis, and the
projection-walk corner, the one place E1 needed a restricted form, is now discharged by
substitution of an inhabitant (above). The certificate-calculus prototype (option 1) was
never started.

The state of the obstacle, in one place:

1. **What is proved.**
   - Strengthening holds wherever the removed binder is inhabited in the smaller context:
     `TrExprS.weakBV_inv_inhabited`, `Verify/Typing/InhabitedStrengthening.lean`. The proof
     is substitution followed by cancelling the lift, with no hypothesis on the environment.
   - Confluence of the canonical reduction in a fixed context is available.
   - Singleton eta has a formal, abstract-layer proof (Part 2).
   - The unrestricted statement is false in a two-family model (`STRENGTHENING.md`), so any
     proof has to use something specific to Lean's environments.

2. **What is missing.** A conversion-elimination theorem for a support-preserving
   ("certified") presentation of definitional equality. Statement: in the fragment of Π, λ,
   application, sorts, constants, untyped β, typed η and typed proof irrelevance,
   transitivity of the join relation `Conv` is admissible when `Conv` contains only subterms,
   synthesized types and reducts of its endpoints. From that theorem, strengthening follows
   by induction on certificates. A derivation in the smaller context exists because no
   certificate mentions syntax outside its endpoints.

3. **Why it is stuck** (Part 3 status above). Each candidate organisation is circular:
   - transitivity needs NEq to be transported along β;
   - transport is substitution through the typing evidence in the proof-irrelevance and η
     leaves;
   - substitution for `Synth` needs `Conv` composition at the variable case, on outputs
     rather than sub-certificates.

   The candidate measures fail as follows:
   - universe level fails because proof irrelevance is level-blind;
   - derivation height fails because substitution duplicates certificates;
   - β-peak count fails because η-expansion creates new peaks.

   Siles and Herbelin's typed parallel reduction covers β-only PTS. Its auxiliary calculus
   is exactly what the support discipline forbids.

4. **The open question for Mario.** Is there a proof of admissible transitivity, or of
   strengthening, for λΠ with typed η and definitional proof irrelevance that does not go
   through normalization? Alternatively, is there a counterexample in a non-normalizing
   extension? Either answer settles route (b). In the meantime nothing in E1 depends on it.
