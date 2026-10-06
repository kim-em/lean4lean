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
