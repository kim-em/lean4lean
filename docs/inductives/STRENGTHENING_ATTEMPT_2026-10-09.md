# Strengthening with canonical `Eq`: attempt of 2026-10-09

Branch `agent/verify-inductives-strengthening2` (worktree `lean4lean-strength2`), off
`agent/verify-inductives` at b8fb81be. Target:

```lean
theorem strengthening_of_canonicalEq (henv : env.WF) (heq : env.HasCanonicalEq) :
    env.Strengthening
```

with `VEnv.Strengthening` restored in `Lean4Lean/Theory/Typing/Strengthening/Cancel.lean`.
Prior study: the recovered files in `docs/inductives/history/` and the notes summarised in
section 1. This document records the architecture chosen for this attempt, the exact lemmas,
the induction measure where one exists, and the reasons each previously failing piece is or
is not handled. It is updated as the attempt proceeds (section 6).

## 1. Starting point

### 1.1 The one-context form of the problem (proved, `Strengthening/Cancel.lean`)

For every well-formed environment (no `Eq` hypothesis), `Strengthening` is equivalent to

```lean
def Cancel (env : VEnv) : Prop :=
  ∀ ⦃U Γ Q a b⦄, OnCtx Γ (env.IsType U) →
    env.IsDefEqU U Γ (.lam Q a.lift) (.lam Q b.lift) → env.IsDefEqU U Γ a b
```

(`strengthening_iff_cancel`; Astra's derivation of 2026-10-08, adapted). The removal of
arbitrary `Ctx.LiftN n k` insertions, the recovery of `OnCtx Γ`, and the typed forms
(`IsDefEq.weakN_iff'`, `IsDefEq.skips`) all follow from `Cancel` by `lamDF` abstraction,
`IsDefEqU.lam_body` (equal abstractions with the same domain have equal bodies: apply to
`bvar 0` and beta) and unique typing, by induction on `(k, n)`. The inhabited case
(`Cancel.inhabited`) and the typed retraction case (`IsDefEqU.retract`) are substitution.

So the theorem to prove is: **two definitionally equal constant functions have definitionally
equal values**, in one well-formed context, with no inhabitant of the domain and no hypothesis
that the values are typable in `Γ` (their typability is part of the conclusion).

### 1.2 What the hypothesis can and cannot do

* Without canonical `Eq` the statement is false (`STRENGTHENING.md`: two singleton `Prop`
  families with large elimination; the larger-context derivation is formalised, the groupoid
  separation is on paper and cannot be built in Lean, `COUNTERMODEL_STATUS.md`).
* With canonical `Eq`, every known mechanism by which a binder `q` can produce a conversion
  between `q`-free terms collapses: a proof major whose fields are needed is itself a `q`-free
  subterm, and its fields are extracted by `Eq.rec` casts (`SingletonExtraction`, the
  `singletonCoverage` of `WFParams.lean`). No counterexample is known (section 5).
* Normalisation is not available and cannot be made available: the object theory is Lean's
  own (all universes, impredicative `Prop`, large elimination), so a normalisation proof for it
  would prove its consistency inside Lean. Every proof here must be normalisation-free, as the
  observation model behind `VEnv.WF.headInversion` is. (Strengthening itself does not imply
  consistency: in an inconsistent environment with `Eq` every type is inhabited, by casting
  along a proof of `Sort 0 = Q`, and `Cancel` follows by substitution.)
* The theory admits non-terminating definitions (`VDecl.WF.mutualDef` has no termination
  condition), so even "benign" normalisation of the terms involved is unavailable.

### 1.3 The circularity (unchanged)

Every organisation of a proof of `Cancel` reduces to the same statement: a *support-preserving*
presentation of definitional equality (certificates mentioning only subterms, synthesised types
and reducts of their endpoints) is complete for `IsDefEq`. Completeness needs admissible
transitivity of the certified join, i.e. confluence of the certified reduction modulo certified
normal equality, and the diagram proof manufactures new side conditions (K and singleton
alignment checks, eta domains, agreement of synthesised types at proof-irrelevance leaves)
by composing certificates that are *outputs* of earlier diagram steps, whose size and nesting
depth are not bounded by the inputs. Section 3 gives the precise form in which this attempt
meets it. Astra's two checked obstructions (`history/StrengtheningPartial_2026-10-08.lean`)
are the test cases for any candidate presentation:

* `eta_does_not_preserve_support`: `FullStep.funEta` rewrites the closed `λ x : Prop. x` to a
  term whose domain annotation mentions the inserted variable (`f : Π x : (λ z. Prop) q. Prop`
  by conversion). A direct descent of arbitrary `FullReduction` witnesses is impossible; the
  presentation must choose domains.
* `compress_domain_equality`: `NormalEqN false 1 Γ (λ A. Prop) (λ B. Prop)` for *any*
  declaratively equal `A`, `B`: the `lamDF` index does not count the domain comparison, so the
  `NormalEqN` index gives no induction handle on hidden domain conversions. (`forallEDF` does
  count its displayed domains but keeps an uncounted premise relating the context domain.)

## 2. Architecture: a support-preserving certificate calculus over the full theory

The proof of `Cancel` is organised as four theorems about one new family of relations, all in a
single context, mutually inductive. The design follows the Part 3 design of
`STRENGTHENING_NOTES.md` and Astra's review 2 (support-preserving synthesis and exposure,
chosen eta domains, Eq-cast extraction for proof majors), made precise against the current
definitions of `FullStep`, `ParRed`, `PrefixUnfold`, `QuotPrefixUnfold`, `CaseIota` and
`NormalEqN`.

### 2.1 Judgements

Fix `env`, `U` and the confluence parameters `henv.params U` (so `Pat`, `recursorData` are the
registry's). All judgements are over a context `Γ : List VExpr`.

* `CTy Γ e T` (**certified synthesis**). Syntax-directed; `T` is a function of `e` and the
  derivation:
  - `bvar i`: `T` is the looked-up type;
  - `sort l`: `T = sort (succ l)`, `l.WF U`;
  - `const c ls`: `T = ci.type.instL ls`, levels well formed;
  - `elim`: the schema's generic type, as in `IsDefEq.elimDF`;
  - `app f a`: `CTy f F`, `CExpose F (forallE A B)`, `CTy a A'`, `CConv A' A`, `T = B.inst a`;
  - `lam A b`: `CSort A`, `CTy (A::Γ) b B`, `T = forallE A B`;
  - `forallE A B`: `CSort A` at `u`, `CSort B` at `v` under `A`, `T = sort (imax u v)`;
  - `proj S i e`: `CTy e M`, `CExpose M (mkApps (const S ls) (ps ++ idx))`, `T` the field
    type computed by `info.fieldType` from `ls`, `ps`, `e`, with the `projDF` guard.
  - `CSort Γ A u := ∃ S, CTy Γ A S ∧ CExpose S (sort u)`.
  - `CExpose Γ T T' := CStep* Γ T T'` with `T'` of the required head (sort, `forallE`, rigid
    spine). Exposure is by certified reduction only, never by conversion.
* `CStep Γ a b` (**certified parallel step**). The constructors of `FullStep`, with every
  premise rewritten:
  - `core`: `ParRed` with the pattern check `r.2.OK (CConv Γ)` and `CaseRedex` whose `guard`
    and `CaseArguments` typing premises are `CConv`/`CCheck` (`CCheck Γ e A := ∃ S, CTy e S ∧
    CConv S A`);
  - `delta`, `quotDelta`: `PrefixUnfold`/`QuotPrefixUnfold` whose `UnfoldingCheck` fields
    `source_typed`, `captures_typed`, `major_prop` are `CCheck`s and whose `recursor_lhs`
    (`ConstSpineDefEq`) is pointwise `CConv`; the generated program (`singletonUnfolding`,
    `QuotPrefixUnfolding.generate`) is unchanged: it is a deterministic function of the
    arguments, so its output commutes with `liftN` (this is what the existing
    `PrefixUnfold.weakN` proves);
  - `projIota`: `CCheck` of the redex (which fixes the field type);
  - `structEta`: `CTy e M`, `CExpose M (mkApps (const S ls) ps)`: the parameters are read
    from the *synthesised* type, not from a typing premise;
  - `funEta`: `CTy e F`, `CExpose F (forallE A B)`, target `lam A (app e.lift (bvar 0))`: the
    domain is the exposed synthesised domain (this is the repair of
    `eta_does_not_preserve_support`);
  - congruences `app`, `proj`, `lam`, `forallE` unchanged.
* `CNorm Γ a b` (**certified normal equality**). `NormalEqN` without indices, with:
  - `lamDF`: `CConv Γ A₁ A₂` and `CNorm (A₁::Γ) b₁ b₂` (the domain comparison is a certificate,
    the repair of `compress_domain_equality`; the body is compared under the *left* domain and
    context transport is a lemma, section 3.4);
  - `forallEDF`: likewise;
  - `appDF`, `projDF`: congruence without typing premises;
  - `etaL`/`etaR`/`etaBoth`: with the domain taken from the exposed synthesised type of the
    non-lambda side (`CTy e' F`, `CExpose F (forallE A B)`), body compared under `A`;
  - `proofIrrel`: `CTy h p`, `CTy h' p'`, `CConv p p'`, `CSort p 0`;
  - `refl`, `sortDF`, `constDF`, `elimDF`: level equivalence only (`elimDF` with the
    permission data instead of a typing premise).
* `CConv Γ a b := ∃ a' b', CStep* Γ a a' ∧ CStep* Γ b b' ∧ CNorm Γ a' b'`.

Every term occurring in a certificate of `CConv Γ a b` is a subterm of `a` or `b`, a reduct of
such, a synthesised type of such (built from context entries, constant types, `fieldType`,
generated programs and substitution), or generated syntax of the unfolding programs. This is the
**support invariant**: if `a = a₀.lift` and `b = b₀.lift` in `Q :: Γ`, every term in the
certificate is a lift, because each constructor's terms are computed from its premises' terms
by operations that commute with `liftN` (`inst`, `instL`, `mkApps`, `fieldType`,
`singletonUnfolding`, `generate`, pattern `apply`), context lookups above `Q` are lifts, and
constant types are closed.

### 2.2 Theorems

1. **Soundness** (`CConv.defeq : CConv Γ a b → IsDefEqU Γ a b`, with `CTy.hasType`,
   `CStep.defeq`, `CNorm.defeq`), by mutual induction, each case an existing soundness lemma
   (`ParRed.defeq`, `PrefixUnfold.defeq`, `FullStep.defeq`, `NormalEqN.defeq`) applied to the
   declarative premises obtained from the induction hypotheses. Routine.
2. **Descent** (`CConv.descend : CConv (Q::Γ) a.lift b.lift → CConv Γ a b`, with the
   analogues for `CTy`, `CStep`, `CNorm`, generalised to `Ctx.LiftN n k`), by mutual
   structural induction on the certificate, using injectivity of `liftN` and the commutation
   lemmas of the support invariant. Routine but long (every constructor, every generated
   program).
3. **Cancel from completeness.** From `IsDefEqU Γ (λ Q. a↑) (λ Q. b↑)` and completeness,
   `CConv Γ (λ Q. a↑) (λ Q. b↑)`; a certified `lam_body` lemma (reducts of a lambda are lambdas
   or eta-expansions of lambdas; `CNorm` between lambdas is `lamDF` or eta; in each case a
   `CConv (Q::Γ) a↑ b↑` is read off, using certified substitution of `bvar 0` only) gives
   `CConv (Q::Γ) a↑ b↑`; descent gives `CConv Γ a b`; soundness gives `IsDefEqU Γ a b`.
4. **Completeness** (`IsDefEqU Γ a b → CConv Γ a b`, with `HasType Γ e A → CCheck Γ e A`), by
   induction on the declarative derivation. Every rule but `trans` and `defeqDF` is a direct
   closure property (section 3.1); `trans` needs `CConv.trans`, and `defeqDF` for `CCheck`
   needs `CConv.trans` at types. `CConv.trans` is the open metatheorem (section 3.2).

Theorems 1 to 3 are provable with known techniques; theorem 4 is where every previous attempt
stopped, and where this one is expected to stop unless section 3.3 produces a measure. The
value of formalising 1 to 3 is that the open problem becomes one Lean proposition,
`CComplete env U`, with `strengthening_of_cComplete : (∀ U, CComplete env U) →
env.Strengthening` machine-checked, instead of a prose reduction.

## 3. The completeness theorem: lemmas and measure

### 3.1 Closure properties that are structural

* Symmetry: `CNorm` and `CConv` are symmetric (swap the join; `lamDF` body is under `A₁`, so
  symmetry of `lamDF` needs context transport along `CConv A₁ A₂`, section 3.4).
* Congruence: `CConv f f'`, `CConv a a'` give `CConv (app f a) (app f' a')` (join the
  components, `appDF`); likewise `proj`, `lam` (needs the domain certificate and transport),
  `forallE`.
* Reduction rules: `beta`, `extra`, `elimIota`, `projIota`, `structEta`, `eta`, `unitLike`
  (unit-like equality is `CNorm`? no: `unitLike` has no normal-equality counterpart; it is added
  to `CNorm` as a leaf with `CTy e M`, `CTy e' M'`, `CExpose` of both to the unit-like structure
  type and `CConv` of the parameters), `proofIrrel`: each is one certified step plus `refl`,
  given completeness of typing for the premises.
* Weakening (`CConv.weakN`), substitution of a certified-typed term (`CConv.instN`), context
  conversion along `CConv` (`CConv.defeqDFC`): by structural induction, *provided* the
  variable case of `CTy.instN` is handled; the variable case gives `CTy (e[a]) S` with
  `CConv S A[a]` from `CCheck a A`, so the substitution lemma for `CTy` must return a
  `CCheck`, and the application case must then compose `CConv S (A[a])` with the domain
  agreement of the exposed Π: **this is a transitivity call on outputs** (Astra review 3, item
  (b)). So even weakening-free substitution needs `CConv.trans` at types.

### 3.2 `CConv.trans`

Statement: `CConv Γ a b → CConv Γ b c → CConv Γ a c`. Proof shape (strip lemma):
`b ⟶* b₁` and `b ⟶* b₂` are joined by confluence of `CStep` (`b₁ ⟶* b₃ ⟵* b₂`); `CNorm a' b₁`
is transported along `b₁ ⟶* b₃` to some `a' ⟶* a''`, `CNorm a'' b₃`; likewise on the right;
then `CNorm.trans`. The three ingredients and their side-condition traffic:

* **Confluence of `CStep`** (`CStep a b → CStep a c → ∃ d, CStep b d ∧ CStep c d` and its
  strip). The critical pairs are those of `LevelledReduction.lean`. A step with a side
  condition (pattern check `CConv x y`, `UnfoldingCheck`, `CaseRedex.guard`) overlapping a
  reduction of its own arguments (`x ⟶ x'`) yields a step whose side condition is
  `CConv x' y'`, obtained from `CConv x y`, `x ⟶ x'`, `y ⟶ y'` by **`CConv.trans` on the
  outputs** `x' ⟵ x`, `CConv x y`, `y ⟶ y'`, i.e. by the strip lemma on
  (`x ⟶ x'`, the join inside `CConv x y`). Its inputs are a sub-derivation of the second step
  and a sub-certificate of the first: smaller. But the strip lemma tiles diamonds along the
  join, and from the second tile on, the diamond's inputs are outputs of the first tile.
* **Transport of `CNorm` along `CStep`** (`CNorm a b → CStep b b' → ∃ a', CStep* a a' ∧
  CNorm a' b'`): at a beta redex `(λ A. m) n` matched by `lamDF`/`appDF` congruence,
  `CNorm (m[n']) (m'[n])`-shaped goals need heterogeneous substitution of `CNorm n' n` into
  `CNorm m m'`, which passes through the `CTy`/`CConv` premises of the `proofIrrel`, `lamDF`
  and eta leaves of `m ≡ m'`: substitution for `CTy` with the output composition of 3.1. At a
  K or singleton step matched by congruence, the side condition is transported as above.
* **`CNorm.trans`**: `proofIrrel` against a congruence needs coherence of synthesised types
  (`CNorm h' h'' → CTy h' p' → CTy h'' p'' → CConv p' p''`), whose `app` case needs
  `CConv (B[a]) (B'[a'])` from `CConv (forallE A B) (forallE A' B')` (certified Π-injectivity,
  a projection of the join, fine) and `CNorm a a'` (heterogeneous substitution again).

### 3.3 Measures examined

The recursion is: `trans` → strip → diamond → (`trans` on sub-certificates: fine) and
(diamond on outputs: not fine); `trans` → transport → heterogeneous substitution → `CTy`
substitution → `trans` on outputs. Candidates for a well-founded measure, each with the case
that breaks it:

1. *Certificate size* (total, including nested side conditions). Diamond on an output of a
   previous diamond: the output can be larger than both inputs (a K-step whose check is the
   strip of a check against an argument reduction has a larger check than the input step).
2. *Nesting depth of side conditions.* A diamond between a K-step of depth `d` (check of depth
   `d-1`) and an argument reduction of depth `d` produces a K-step whose check is a strip of a
   depth-`d` reduction against a depth-`(d-1)` join; the strip output has depth `d`, so the new
   step has depth `d+1`. Tiling `ℓ` times along a join of length `ℓ` reaches depth `d+ℓ`. The
   depth of the *smaller-depth input* does decrease along one strip (`d-1`, `d-2`, ...), but the
   K case of the diamond also joins the two strip outputs (both of unbounded depth) at the
   common reduct of the original check.
3. *Side conditions as zigzags instead of joins.* Transport along reduction is then trivial
   (prepend the inverse step) and `trans` of the top-level relation is trivial, but the
   intermediate terms of a zigzag are arbitrary, so the support invariant fails. This is
   `IsDefEq` restated.
4. *Universe level of the compared type*, *height of the declarative derivation*, *β-peak
   length*: refuted in Astra review 3 (proof irrelevance is level-blind, `Prop` is
   impredicative; completeness of `trans` would call itself on a derivation containing the
   step being eliminated; `F p ≡ F q` for proofs `p`, `q` is β-normal).
5. *Coinductive certificates* (greatest fixed point: every check is again a certificate,
   possibly infinitely deep). Descent is then by coinduction and completeness is a productive
   corecursion (the reduct terms and step skeletons of a diamond are determined by the redexes
   fired, independently of the checks). But soundness fails: a circular check (a K-step whose
   check is justified by the K-step itself) is a valid coinductive certificate with no
   `IsDefEq` derivation. So the certificates must be inductive, and the question is exactly
   the termination of the corecursion above.

No candidate survives. The attempt therefore proceeds as in section 4: formalise theorems 1 to
3 of section 2.2 so that the open problem is the single proposition `CComplete`, try the
counterexample direction (section 5), and keep looking for a measure in the K case, which is
the one place where the depth grows: a K-step's check compares the two index arguments of a
redex, and the only reason the check grows is that the arguments were reduced. A presentation
in which the K-check is stated on the *unreduced* arguments (the check is a `CConv` between the
index terms as they were when the redex was first formed, carried along as a frozen
certificate while the arguments reduce) would make transport trivial, but the redex *is*
syntax, and after a reduction of its arguments the certificate no longer mentions subterms of
the redex: support is preserved (the frozen terms are reducts' ancestors, hence still lifts),
but the certificate is no longer determined by the term, and soundness needs
`IsDefEq x x'` for the ancestor `x` of `x'`, which holds (reduction is sound) at the cost of a
`trans` in the *declarative* theory, which is fine. This "frozen check" variant is the one
new idea of this attempt; its difficulty is the strip lemma itself: the two steps being
joined may carry checks frozen at different ancestors of the same arguments, and the common
reduct's step must carry one check, so the two frozen certificates must be composed:
`trans` again, on sub-certificates of the inputs this time (the frozen checks are
sub-certificates of the two input steps), with no output involved. Whether the whole diagram
proof can be arranged so that every `trans` call is on sub-certificates of the *inputs* of
the current diamond is the question to put to the second opinion (section 6).

### 3.4 Context transport

`CNorm (A₁::Γ) b₁ b₂` with `CConv Γ A₁ A₂` must give `CNorm (A₂::Γ) b₁ b₂` (for symmetry of
`lamDF`, and for the body comparisons of eta). Certificates mention the context only at `bvar`
lookups in `CTy`, which return the looked-up type; after transport, `CTy (A₂::Γ) (bvar 0)
A₂.lift` instead of `A₁.lift`, and every consumer of that type (an `app` whose function is
`bvar 0`, a `proofIrrel` whose proof is `bvar 0`) needs its exposure or conversion
re-established from `CConv A₁ A₂`: `CExpose A₁.lift (forallE ..)` and `CConv A₁ A₂` give
`CExpose`-up-to-`CConv` for `A₂.lift`, which is a `trans`. So context transport is also a
`trans` consumer. The frozen-check idea applies: a `CTy` leaf at a variable may carry the
looked-up type of the context in which the certificate was *built*, with a `CConv` to the
current context's entry; transport then only extends that `CConv`, by `trans` on
sub-certificates.

## 4. Formalisation plan (bottom-up, each step committed at zero `sorry`)

1. `Strengthening/Cancel.lean` (done): statement, `Front`, `Cancel`, equivalences, inhabited
   and retraction cases, former consumers.
2. `Strengthening/Support.lean`: the support invariant as a predicate `Supported n k`
   (`VExpr.Skips n k` on every term) and the commutation lemmas for the operations used by the
   certificate constructors (`inst`, `instL`, `mkApps`, `fieldType`, pattern `apply`,
   `singletonUnfolding`, `QuotPrefixUnfolding.generate`, `etaOpen`, `wrapLams`), most of them
   extracted from the existing `weakN` proofs.
3. `Strengthening/Certificate.lean`: the mutual inductive `CTy`/`CStep`/`CNorm`/`CConv`
   (section 2.1), soundness (theorem 1).
4. `Strengthening/Descent.lean`: theorem 2.
5. `Strengthening/Complete.lean`: `CComplete`, theorem 3, and the structural closure
   properties of 3.1 that do not need `trans`.
6. `Strengthening/Trans.lean`: the frozen-check variant of 3.3 if the second opinion does not
   refute it; otherwise the precise statement of the missing lemma.
7. If `CComplete` is proved: `strengthening_of_canonicalEq`, audit root, and the consumers
   switch from the hypothesis to the theorem.

Sizes: step 2 about 1k lines, step 3 about 1.5k, step 4 about 2k, step 5 about 1k.

## 5. Counterexample direction

A counterexample needs a `Prop`-typed or data-typed `Q` and `q`-free `a`, `b` with
`Γ ⊢ λ Q. a↑ ≡ λ Q. b↑` and `Γ ⊬ a ≡ b`. The second part needs a separating model that is
sound for the full theory *with* `Eq`, proof irrelevance and K; set-theoretic models are
sound and separate only extensional coincidences, which definitional equality does not create
(head separation holds in every well-formed environment). Intensional models (groupoids) are
not sound for `Eq.rec` with definitional proof irrelevance unless the index groupoid has at most
one arrow between any two objects, which is exactly what the extraction `extract p : P v` of
`STRENGTHENING.md` exploits: with transport along the unique arrow, the motive
`λ n x _ _. (e : n = c) → P (cast e x)` has no functorial action, so the groupoid model of the
countermodel is not a model of the theory with `Eq`. The inhabitation-sensitive rules are
`proofIrrel` (through the typing of `q`-free proofs at `q`-dependent propositions) and the
typing premises of every other rule; the falsification study (`STRENGTHENING_NOTES.md` Part 1)
shows each reduces to extraction from a `q`-free major. The non-canonical recursor universes of
section 1.9a there (a singleton whose only recursor eliminates into `Sort (u+1)`) do not escape
either: the motive `λ n x _ _. (e : n = c) → ∀ X : Sort u, (P (cast e x) → X) → X` lands in
`Sort (u+1)` and at `u = 0` gives `P v` by instantiating `X := P v`. No new mechanism was found
in this attempt. The remaining unexplored direction is an environment with non-terminating
definitions whose unfolding is needed to expose a proof major: this adds no inhabitation
sensitivity (definitions are closed) and is covered by the same argument.

## 6. Log

* 2026-10-09: sections 1 to 5 written; `Strengthening/Cancel.lean` committed (fe0c738f).
  Second opinion requested (`STRENGTHENING_ASTRA_REVIEW5.md`) on: (a) the frozen-check variant
  of 3.3/3.4, specifically whether every `trans` call in the strip can be arranged on
  sub-certificates of the diamond's inputs; (b) whether the certificate calculus of 2.1 is
  the right shape for theorems 1 to 3 or whether a different shape (e.g. checking at a common
  type) is needed for descent of `proofIrrel`; (c) anything in section 5.
