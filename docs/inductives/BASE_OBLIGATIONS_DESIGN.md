# Design: a non-circular proof of the remaining base obligations

Scope: worktree `/home/kim/worktrees/lean4lean/lean4lean-base`, branch
`agent/verify-inductives-base` at 070911e. Read-only study. The design assumes:
the `NormalEqN`/`etaBoth` re-indexing (step 1 of `docs/inductives/BASE_SORRIES.md` 3a,
branch `agent/verify-inductives-cr`) lands; the final theorem may assume
`env.HasCanonicalEq`; and strengthening is stated as
`strengthening_of_canonicalEq : env.WF -> env.HasCanonicalEq -> env.Strengthening`
(branch e3, `Theory/Typing/UniqueTyping.lean:232` there).

## 0. Verdict

1. The intended derivation "Injectivity from confluence" cannot close in this repo.
   Every confluence argument for this calculus retypes terms, and retyping needs
   uniqueness of types. Uniqueness needs Pi injectivity, and Pi injectivity needs
   confluence. The height-stratified simultaneous induction proposed in
   BASE_SORRIES.md 3c is not well-founded either. Typing height does not bound the
   conversions inside a typing derivation (section 1.3).
2. A normalization-based proof is impossible, not just expensive. The declarative
   theory does not normalize: Abel and Coquand (2020) show this for impredicative
   proof-irrelevant `Prop` with K-like `Eq`. `Acc` large elimination also loops,
   and `VDecl.mutualDef` admits `def T := T`. So reducibility logical relations
   (Abel, Ohman and Vezzosi) and NbE completeness (Abel, Coquand and Pagano) do not
   apply.
3. The one known technique that needs neither normalization nor uniqueness is a
   semantic adequacy argument over finite approximations: Coquand and Huber,
   "An Adequacy Theorem for Dependent Type Theory", TOCS 2019. The repo already
   prototypes it, upstream, by Mario Carneiro:
   `Lean4Lean/Experimental/ShapeLogRel.lean` (6100 lines) and
   `ShapeLogRelAdequacy.lean` (473 lines) prove `forallE_inv`, `sort_inv` and
   `sort_forallE_inv` for a core calculus `SExpr`. That core has beta, eta,
   proof irrelevance and pattern rules, with 9 sorries and the axiom
   `Params.extra_pat`. `Experimental/UniqueTyping.lean` then derives uniqueness
   without stratification, using a heterogeneous `trans'` rule. This is the only
   non-circular template in sight. The recommendation is to build on it.
4. Confluence (`FullReduction.church_rosser`) is then needed only for
   strengthening. Once injectivity and uniqueness come from the semantic layer, the
   existing confluence development is no longer circular: it may keep using `uniq`.
5. Canonical `Eq` matters for both halves. It is the standard for strengthening.
   I also argue (section 2.4) that the semantic adequacy proof needs it, or else a
   Kripke-glued semantics, to give a syntactic weak-head step for large
   elimination on neutral proof majors. Both halves need the same new lemma:
   "singleton eta" built from Eq extraction.
6. Frank total: about 30k-55k lines of new Lean. Phase 1 (the semantic layer)
   carries real research risk. The cheap, immediately valuable step is Phase 0,
   about 2k lines. It reduces the six cone sorries (five Injectivity lemmas plus
   `saturated_of_hasType`), and the two missing separation lemmas, to one stated
   base theorem `VEnv.WF.headInversion` whose statement is exactly what Phase 1
   must deliver.

## 1. Dependency structure

### 1.1 Nodes

- `CR`: `IsDefEq.church_rosser` (FullChurchRosser.lean:52) and its parts:
  `FullStep.strip` (FullReduction.lean:841, sorries :863-865),
  `NormalEq.fullStep` (:528, sorries :640, :648, :693), `NormalEq.headParallel`
  (ChurchRosser.lean:2163), `NormalEq.trans`/`symm`/`defeq`, and `ParRed.triangle`.
- `SE`: spine exposure (`NormalEqN.spine_expose`, BASE_SORRIES 3b; not yet written).
- `HS`: head separation. Sort vs Pi is `sort_forallE_inv`. Rigid vs Pi, sort vs
  rigid, and distinct rigid heads are missing.
- `INJ`: `IsDefEqU.sort_inv`, `forallE_inv_stratified`, `sort_forallE_inv`,
  `fieldType_inv_stratified`, `rigidApp_inv` (Injectivity.lean).
- `UNIQ`: `IsDefEq.uniq` (UniqueTyping.lean:13).
- `SAT`: `VConstructorShape.saturated_of_hasType` (RecursorLemmas.lean:430).
- `STR`: `strengthening_of_canonicalEq`.

### 1.2 Current edges and the cycles

Write `X <- Y` for "X uses Y".

- `UNIQ <- INJ`: the stratified induction calls `forallE_inv_stratified` (app
  case), `fieldType_inv_stratified` (proj case) and `sort_inv`, 8 times.
- `INJ <- CR` is the intended route, per the Injectivity.lean docstring ("all of
  them are consequences of confluence ... ChurchRosser.lean").
- `CR <- UNIQ` is pervasive, not 11 call sites. Counting `.uniq`/`.uniqU`,
  `trans_l/r`, `transU_l/r`, `of_l/of_r`, `defeqU_l/r`, `IsDefEqU.trans` and
  `IsDefEqU.defeqDF`, all of which are derived from `uniq`: about 110 uses in
  ChurchRosser.lean and 20 in FullReduction.lean. `NormalEq.defeq`
  (ChurchRosser.lean:290) already needs `.of_l`. `FullStep.defeq`
  (FullReduction.lean:58) needs `trans_l` and `uniq`. Subject reduction is
  therefore downstream of `UNIQ`.
- `CR <- INJ`: `IsDefEqU.forallE_inv`/`sort_inv` is used 7 times in
  ChurchRosser.lean (for example `parRed_beta`, :1831).
- `CR <- STR` through the old `weakN_iff`: 26 mentions in ChurchRosser.lean
  (`NormalEq.trans` eta/eta via `NormalEq.weakN_iff`, `ParRed.weakN_inv`,
  `hasType_app_bvar0`, `parRed_beta`). The cr branch removes the `trans` use;
  the others need the separate fixes listed in BASE_SORRIES 3a item 4.
- `SAT <- HS` (rigid vs Pi) and `UNIQ`. The proof copies
  `HasType.mkApps_sort_arity` (SignatureArity.lean:11).
- `SE <- UNIQ, INJ(sort_inv)`, for "a Pi into Prop propagates proofness".
- `STR <- CR, UNIQ, INJ`, plus Eq extraction (section 3).

The cycles are `INJ -> CR -> UNIQ -> INJ` and `INJ -> CR -> INJ`. The legacy
`CR -> STR` edge is not a cycle in the cone, because CR is outside the
`addDecl.WF` cone, but it would become one if STR is proved via CR. It has to be
cut, as the cr branch is doing.

Cone membership (BASE_SORRIES 1): INJ x5, SAT and STR are in the `addDecl.WF`
cone. `headParallel` and the FullReduction sorries are not. So confluence is a
means, not an obligation. In the recommended plan it is needed only for STR.

### 1.3 Why the stratified simultaneous induction does not close

The report's plan: for each height n, prove (i) uniq, (ii) CR for terms whose
types have height < n, (iii) head preservation, (iv) inversions. This needs a
measure that bounds every typing used as a side condition inside the CR argument
for a conversion appearing at height n. None exists:

- `HasTypeStratified.defeq` (Strong.lean:1316) takes an unstratified
  `Γ ⊢ A ≡ B : sort u`. CR is proved by induction on that derivation. Its
  `trans` case goes through arbitrary intermediate terms, and the `FullStep` and
  `NormalEq` side conditions (`funEta`, `structEta`, `projIota`, `appDF` typings)
  type arbitrary terms.
- Stratifying `IsDefEq` too does not help. The CR proof builds new typings for
  reducts by substitution. Beta and iota typings of `b[a]` have height up to
  `h(b) + h(a)`, which can exceed the redex height, so the measure is not
  preserved.
- Universe level is not a measure either. Comparing two Props (types at
  `sort 0`) compares Pi domains at any level, by impredicativity, and polymorphic
  levels are not numbers.
- The "type of the type" rank is not well-founded. To compare terms at a type T,
  we need Pi injectivity for the types of T's subterms, for example `f` in
  `Vec Nat (f x)`. Those types are again types of unrelated size.

`forallE_inv_stratified` and `fieldType_inv_stratified` encode only `uniq`'s own
internal height bookkeeping, which is the output bounds. They do not make the
inversions themselves stratifiable.

## 2. Non-circular architecture

### 2.1 What is and is not provable for declarative `VEnv.IsDefEq`

Already proved here without uniqueness: weakening and substitution
(`IsDefEq.weakN`, `instN`, `Lemmas.lean:696/915`; `IsDefEq.subst`), context
conversion (`IsDefEq.defeqDFC`, `Lemmas.lean:1044`), syntax-directed inversion
through `IsDefEqStrong.hasType'`/`HasTypeStrong` (Strong.lean:188, 1076), and
typing inversions (`HasType.forallE_inv`/`app_inv`/`lam_inv`/`proj_inv`). These
form the uniq-free base, L0.

Believed true and targeted: uniqueness of types, the five inversions, head
separation, SAT, subject reduction for `FullStep` (already proved given uniq),
and CR modulo `≡ₚ` for `FullReduction` with singleton reconstruction.

False, so do not try:

- Weak or strong normalization (Abel and Coquand 2020; `Acc`; `mutualDef` loops).
- Decidability of `IsDefEq`: Carneiro's thesis, via `Acc`.
- Transitivity of the kernel's algorithmic relation (Carneiro).
- Unrestricted strengthening: the STRENGTHENING.md countermodel without `Eq`.
- Rigid-head injectivity at term level. `Or.inl h ≡ Or.inr h'` by proof
  irrelevance, and `S.mk (proj e) ≡ e` by `structEta`. The sort-typing hypothesis
  of `rigidApp_inv` is essential.
- Any untyped CR covering `proofIrrel`, and untyped beta-eta CR with
  domain-annotated lambdas (Nederpelt's counterexample).

Open: STR with canonical `Eq`.

### 2.2 How the literature handles typed proof irrelevance with K and iota

- Werner, "On the strength of proof-irrelevant type theories", LMCS 2008.
  Conversion modulo erasure of proof subterms, with normalization obtained by
  translation into a theory with strong normalization. Not applicable here: it
  needs SN of the target and restricts large elimination. Lean's combination of
  impredicative irrelevant `Prop`, K-like `Eq` and `Acc` breaks it.
- Abel, Coquand and Pagano, TLCA 2009 / LMCS 2011. Irrelevance as a type former
  in predicative MLTT, with typed algorithmic equality whose completeness comes
  from a Kripke PER model, that is NbE. Needs normalization. The transferable idea
  is that proof positions are decided by types, never by syntax.
- Gilbert, Cockx, Sozeau and Tabareau, "Definitional proof-irrelevance without
  K", POPL 2019. `SProp` with a logical relation. They explicitly exclude the
  large-elimination and K cases that break normalization, and Lean has exactly
  those cases.
- Siles and Herbelin, JFP 2012, and Adams, JFP 2006. These handle the
  "subject reduction needs Pi injectivity, which needs typed CR" circularity for
  pure type systems by going through untyped beta-CR and typed parallel
  reduction. They rely on CR being untyped, which fails here because proof
  irrelevance, eta, K, singleton iota, struct eta and unit-like are all typed.
- Carneiro, "The Type Theory of Lean", 2019. A set model (consistency),
  undecidability, and non-transitivity of the algorithm. The syntactic
  metatheory (confluence, unique typing) of the ideal judgment is left
  conjectural. Lean4Lean is its continuation.
- Coquand and Huber, TOCS 2019. Adequacy from a domain semantics with finite
  approximations ("shapes"). It needs no normalization: non-terminating things
  get the bottom shape and are vacuously related. The repo's
  `Experimental/Thierry*.lean` and `ShapeLogRel*.lean` follow it.

### 2.3 Options considered

| Option | Verdict |
|---|---|
| A. Typed CR first, with stratified induction (BASE_SORRIES 3c) | Not well-founded (1.3). |
| B. Untyped CR first (erase, then retype) | Proof irrelevance cannot be an untyped rule. Erasure needs proof positions, which need uniq, the circle again. Untyped K is harmless, but erasure loses the data that singleton iota reads. |
| C. Annotated syntax, as in Siles and Herbelin | Breaks the circle for beta only. It would need an annotated twin of VExpr plus eta, irrelevance and typed iota. Larger than D, and no prototype exists. |
| D. Semantic shape logical relation (Coquand and Huber, Carneiro prototype) | Non-circular by construction: a fundamental lemma by induction on derivations, no CR, no uniq. Handles non-termination. Recommended. Risk at typed-check rules (2.4). |

### 2.4 The recommended layering, with import discipline

- L0: existing base: `Basic`, `Lemmas`, `Strong`, `EnvLemmas`,
  `ProjectionRigidity`, `Pattern`.
- L1: semantic layer. It proves `VEnv.WF.headInversion` (statement in section 4,
  step 1). It must not import `UniqueTyping`, `Injectivity`, `ChurchRosser`,
  `FullReduction` or `HeadReduction`. `HeadReduction` imports `ChurchRosser`, so
  L1 needs its own typed weak-head reduction. Also check the transitive import
  cone of the pattern registry builders (`NativeRegistryOfWF`,
  `CanonicalRegistryOfWF`).
- L2: uniqueness and inversions from L1 (Phase 0, below).
- L3: CR, using L2 freely. This is the cr branch's `NormalEqN`, spine exposure,
  `headParallel`, the `fullStep` gaps and `strip`.
- L4: STR, using L2 and L3 plus singleton eta.

Enforce the L1 boundary mechanically: add a test file that imports only L1 and
runs `#print axioms VEnv.WF.headInversion`.

L1 design notes:

- Work on `IsDefEq` extended to closure under heterogeneous type-level
  transitivity, as Mario does with `SExpr.IsDefEq.trans'`. Equivalently, state
  everything over chains of sort-typed links (`TypeChain`, step 1). Chains
  inherit `weakN`, `instN` and `defeqDFC` link by link, so no structural lemma
  is duplicated.
- Typed weak-head reduction `TWHRed Γ e e' A`. Its constructors copy the
  premises of `IsDefEq.beta`, `extra` (through the pattern registry), `elimIota`
  and `projIota`, plus head congruences and conversion. Then
  `TWHRed -> IsDefEq` is immediate and needs no uniq. Determinism is needed only
  for the untyped erasure: port `WHRed.determ` (HeadReduction.lean:316).
  Singleton reconstruction reads data fields from the recursor's own index
  arguments, which makes it syntactic and deterministic. Proof fields come from
  Eq-extraction terms (section 3), so L1 is proved under `env.HasCanonicalEq`.
- Why Eq (or a Kripke-glued semantics) is needed in L1. Take the countermodel
  context `p : I c v (leftMap v)` and `t := I.rec (fun .. => Type) (fun v h => Nat) p`.
  Proof irrelevance forces `t ≡ Nat` in `Γ, q : P v`. A semantics that is
  compositional in the valuation cannot see `q`, so it must give `t` the
  `Nat` shape in `Γ` too. Adequacy then demands a syntactic step `t ⇒ Nat` in
  `Γ`. That step needs a proof of `P v` built from `p`, which exists only with
  `Eq`. The alternative is a Kripke-glued semantics, where values carry syntax
  and the step fires once a constructor form exists in the current context.
  That is monotone under context extension but is new research. Recommendation:
  assume `HasCanonicalEq` in L1.
- Typed-check rules: K-like `Eq.rec`, nonlinear pattern checks `Pattern.Check`,
  and singleton index matching. Domain semantics cannot test equality of values
  continuously, so the semantics should be glued for these rules: a step fires
  iff the declarative check holds in the current context. The LR at the major's
  type (a Prop, which is a type) supplies the index relations. This is the
  largest unknown in L1. Mario's prototype has no inductives; its `const` case of
  `LR.adequacy` is still a sorry, and it relies on the axiom `extra_pat`.

## 3. Where `strengthening_of_canonicalEq` sits

Normalization does not exist (2.1). Confluence alone does not imply STR either. In
an Eq-free environment, CR in `Γ'` must use `q` through typed side conditions or a
context-dependent choice of proof fields, and the countermodel shows that this is
unavoidable. So the Eq-extraction trick has to be built into the metatheory, as
follows.

### 3a. Singleton eta (derived rule)

Statement: for every registered Prop family with singleton large elimination,
using the branch's declaration-derived `SingletonElimination` evidence and the
`SingletonReconstruction*` programs:

```lean
theorem singletonEta (henv : env.WF) (heq : env.HasCanonicalEq) (hΓ : OnCtx Γ (env.IsType U))
    (hfam : SingletonFamily env I info)            -- registered, Prop, singleton elimination
    (hm : env.HasType U Γ m (.mkApps (.const I ls) (ps ++ idx)))
    (hshape : env.IsDefEqU U Γ (.mkApps (.const I ls) (ps ++ idx))
        (.mkApps (.const I ls) (ps ++ info.ctorIndices ls ps (info.readData idx)))) :
    env.IsDefEq U Γ m (info.ctorForm ls ps idx m) (.mkApps (.const I ls) (ps ++ idx))
```

Here `readData idx` reads each data field from its literal index position. Lean's
singleton criterion makes every data field a literal index. `ctorForm` fills each
proof field with `extract_j m`: a `rec` into `Prop` whose motive takes the index
telescope plus a chain of dependent `Eq` hypotheses, transporting the field type
along them, as in STRENGTHENING.md's `extract`. The constructor branch closes
because `e : c = c` is `Eq.refl` by proof irrelevance, and the transport then
reduces by `Eq` iota. Recursive families such as `Acc` need no `Eq`: the motive is
the field type itself.

The risk is whether iterated dependent `Eq.rec` suffices for every index telescope
without `HEq`. I expect it does, but it must be checked on a three-index dependent
family before relying on it. Size: 2k-4k lines. Reuse the index-selector and
proof-field programs in `Theory/Inductive/SingletonReconstruction.lean` and
`Typing/SingletonReconstruction*.lean`.

### 3b. Context-free conversion certificates

Define an inductive `CertEq Γ e₁ e₂`: `FullReduction` steps followed by `NormalEq`
leaves, with two changes.

1. Large elimination on a proof major is the canonical step
   `rec .. m ⟶ rhs[readData idx, extract m]` (from 3a), instead of "proof
   irrelevance, then iota", and instead of the current context-dependent prefix
   replay.
2. Every typed side condition refers only to inferred types of subterms: the
   `funEta` domain, `structEta` parameters, the proof-irrelevance Prop, and the
   K and pattern checks. Each check carries its own sub-certificate.

Then reducts of lifts are lifts. Every sub-certificate's endpoints are lifts or
inferred types of subterms of lifts, which are again lifts. So strengthening for
`CertEq` is a plain structural induction on the certificate.

The route to STR:

1. Completeness: `IsDefEq -> CertEq`. This is the L3 CR theorem rephrased with
   canonical reconstruction and inferred types. It is the bulk of the work.
2. `CertEq` strengthening, by induction.
3. Soundness: `CertEq -> IsDefEq`, which is easy.

Size: 3a 2k-4k; `CertEq` and inferred types 2k-3k; completeness on top of the
L3 CR 3k-6k; strengthening 1k-2k. Total 8k-15k, after L3.

Before investing, run a falsification study: try to break STR with `Eq` present
(1k-3k lines of mostly paper work and small Lean checks). Candidates:

- families whose extraction seems to need `HEq`;
- a data binder of an empty type feeding a proof field through an axiom
  `g : D -> P v`;
- unit-like and struct-eta at q-dependent parameters;
- K-like `Eq.rec` whose index equality holds only through a singleton chain;
- `Quot.sound` combined with K.

If a counterexample appears, the final theorem's hypothesis must change. Learning
that early is worth more than any proof progress.

## 4. Ordered implementation plan

### Phase 0: one base theorem, everything else derived (1.5k-2.5k lines, low risk)

**Step 1** (new file `Theory/Typing/HeadInversion.lean`, imports L0 only):

```lean
namespace Lean4Lean.VEnv

/-- Nonempty chains of definitional equalities, each link typed at some sort. -/
def TypeChain (env : VEnv) (U : Nat) (Γ : List VExpr) : VExpr → VExpr → Prop :=
  Relation.TransGen fun A B => ∃ u, env.IsDefEq U Γ A B (.sort u)

/-- Arguments related pointwise at the domains of a Pi telescope, each domain
instantiated by the left arguments already consumed. -/
inductive SpineArgsEq (env : VEnv) (U : Nat) (Γ : List VExpr) :
    VExpr → List VExpr → List VExpr → Prop
  | nil : SpineArgsEq env U Γ T [] []
  | cons : env.IsDefEq U Γ a a' A → SpineArgsEq env U Γ (B.inst a) as as' →
      SpineArgsEq env U Γ (.forallE A B) (a :: as) (a' :: as')

/-- Head inversion for types: what the semantic layer delivers. -/
structure HeadInversion (env : VEnv) : Prop where
  sort_sort : OnCtx Γ (env.IsType U) →
    env.TypeChain U Γ (.sort u) (.sort v) → u ≈ v
  forallE_forallE : OnCtx Γ (env.IsType U) →
    env.TypeChain U Γ (.forallE A B) (.forallE A' B') →
    (∃ u, env.IsDefEq U Γ A A' (.sort u)) ∧ ∃ v, env.IsDefEq U (A :: Γ) B B' (.sort v)
  rigid_rigid : OnCtx Γ (env.IsType U) → env.Rigid c → env.Rigid c' →
    env.TypeChain U Γ (.mkApps (.const c ls) args) (.mkApps (.const c' ls') args') →
    c = c' ∧ List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) args args'
  former_args : OnCtx Γ (env.IsType U) → env.Rigid c →
    env.constants c = some ci → ci.type = .wrapForalls doms (.sort w) →
    env.TypeChain U Γ (.mkApps (.const c ls) args) (.mkApps (.const c ls') args') →
    SpineArgsEq env U Γ (ci.type.instL ls) args args'
  sort_forallE : OnCtx Γ (env.IsType U) → ¬env.TypeChain U Γ (.sort u) (.forallE A B)
  sort_rigid : OnCtx Γ (env.IsType U) → env.Rigid c →
    ¬env.TypeChain U Γ (.sort u) (.mkApps (.const c ls) args)
  forallE_rigid : OnCtx Γ (env.IsType U) → env.Rigid c →
    ¬env.TypeChain U Γ (.forallE A B) (.mkApps (.const c ls) args)

/-- The single base obligation of the inversion layer (Phase 1 proves it, under
`HasCanonicalEq` if the plumbing decision below goes that way). -/
theorem _root_.Lean4Lean.VEnv.WF.headInversion (henv : env.WF) : env.HeadInversion := sorry
```

As implemented (`Theory/Typing/HeadInversion.lean`), the structure has one more field,
`proj_fieldType`: two typings of one projection select `TypeChain`-related field types,
given both projections' typing data, sources related at the first major type, and the two
major types related by a chain. The proj case of `uniq_chain` cannot be derived from
`rigid_rigid`/`former_args` by substitution: the field type instantiates every earlier
field binder by a projection of the major, including binders the selected field does not
mention, and under the `projDF` guard the projection of a data field out of a structure
that may live in `Prop` is untypable. So neither `substDF` nor repeated `instDF` applies,
dropping the unused binder needs strengthening, and the occurrence-directed
`fieldTemplateCongruence` needs uniqueness at arbitrary subterms of the field type, which
is circular inside the uniqueness induction. `former_args` is not used by Phase 0.

Plumbing decision. If Phase 1 needs `HasCanonicalEq` (2.4), either add `heq` here
and thread it through about 100 Injectivity consumers, or bundle `env.WF ∧
env.HasCanonicalEq` into the environment predicate that `Verify` already carries.
Decide this before Phase 1. Every field is true given uniq and CR. `former_args` is
stated for literal telescopes because the uniq proj case needs arguments typed at
syntactic domains.

**Step 2** (`UniqueTyping.lean`, replacing the stratified proof):

```lean
theorem HasTypeStrong.uniq_chain (henv : env.WF) (hinv : env.HeadInversion)
    (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.HasTypeStrong U Γ e A b₁) (h2 : env.HasTypeStrong U Γ e B b₂) :
    env.TypeChain U Γ A B

theorem TypeChain.collapse (henv : env.WF) (hinv : env.HeadInversion)
    (hΓ : OnCtx Γ (env.IsType U)) (H : env.TypeChain U Γ A B)
    (hA : env.HasType U Γ A (.sort u)) : env.IsDefEq U Γ A B (.sort u)

theorem IsDefEq.uniq (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : Γ ⊢ e₁ ≡ e₂ : A) (h2 : Γ ⊢ e₂ ≡ e₃ : B) : ∃ u, Γ ⊢ A ≡ B : .sort u
    -- same statement as today; proof: `uniq_chain` + `collapse` with henv.headInversion
```

`uniq_chain` goes by plain induction on `h1`, inverting `h2` with
`HasTypeStrong.to_core`-style lemmas, as in `Experimental/UniqueTyping.lean`.

- app: the IH chain on `f`, then `forallE_forallE`, then
  `B ≡ B' : sort v` in `A::Γ`, then `instN` with `a : A`, giving one link.
- lam: link-wise `forallEDF`.
- forallE and sort-level mismatches: `sort_sort`, then `sortDF`.
- defeq: prepend the link.
- proj: `rigid_rigid` and `former_args` on the major's type chain, giving
  levels `≈` and params at domains. Then fieldType congruence through
  `IsDefEq.substDF` on the closed `ctorType`, plus `instL` level congruence
  (`EqUpToLevels`, LevelEquiv) and `projDF` on earlier fields.

`collapse` retypes one link at a time with `defeqDF`, using `uniq_chain` on each
intermediate endpoint. This needs a lemma "structure heads have a literal
telescope", from the formation shape; check ProjectionRigidity and
ProjectionShape.

**Step 3** (`Injectivity.lean` becomes theorems; `SAT` closes). Keep the current
signatures and add:

```lean
theorem IsDefEqU.rigidApp_forallE_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (hrigid : env.Rigid c)
    (h2 : env.HasType U Γ (VExpr.mkApps (.const c ls) args) (.sort u)) :
    ¬env.IsDefEqU U Γ (VExpr.mkApps (.const c ls) args) (.forallE A B)

theorem IsDefEqU.rigidApp_ne (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (hc : env.Rigid c) (hc' : env.Rigid c') (hne : c ≠ c')
    (h2 : env.HasType U Γ (VExpr.mkApps (.const c ls) args) (.sort u)) :
    ¬env.IsDefEqU U Γ (VExpr.mkApps (.const c ls) args) (VExpr.mkApps (.const c' ls') args')

theorem IsDefEqU.sort_rigidApp_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (hrigid : env.Rigid c) : ¬env.IsDefEqU U Γ (.sort u) (VExpr.mkApps (.const c ls) args)
```

Each inversion converts `IsDefEqU` between a known type and anything into a
`TypeChain` (via `uniq`), then reads off a `HeadInversion` field.
`forallE_inv_stratified` retypes `B'` with one `HasTypeStratified.defeq` step at
height `n'`. `fieldType_inv_stratified` follows from the proj-case lemma of step 2
plus `sort_sort`. Both stratified lemmas can be deleted once `uniq` no longer
uses them; their only other consumer, `IsDefEqU.forallE_inv`, can be reproved
directly. `saturated_of_hasType` is `mkApps_sort_arity` with
`rigidApp_forallE_inv` (60-100 lines). `rigidApp_forallE_inv` also closes the
FullReduction :693 `etaL` subcase, and `rigidApp_ne` closes :863.

After Phase 0 the cone contains exactly two named obligations:
`VEnv.WF.headInversion` and `strengthening_of_canonicalEq`.

### Phase 0.5: singleton eta (3a), 2k-4k lines, medium risk

Shared by Phase 1 and Phase 3.

### Phase 1: prove `VEnv.WF.headInversion` semantically (15k-25k lines, high risk)

First a spike, before committing: 2k-4k lines on the `SExpr` prototype. Add one
K-like `Eq` and one singleton family with large elimination, using glued
semantics for checked steps, and close the `const` adequacy case. Decide go or
no-go on the spike. Then:

| Part | Lines |
|---|---|
| 1a. `TWHRed`, soundness, erasure determinism | 1.5k-2.5k |
| 1b. Shape domain and interpretation: levels by evaluation, constants with `instL`, `elim` schemas, proj, quot, glued checks | 4k-7k |
| 1c. Soundness of the interpretation for all 17 `IsDefEq` rules | 3k-5k |
| 1d. LR by shape recursion: whr-expansion closure, irrelevance, symmetry and transitivity across sorts, weakening, substitution | 3k-5k |
| 1e. Fundamental lemma (adequacy) | 3k-5k |
| 1f. Corollaries = the `HeadInversion` fields | 0.5k |

Decide with Mario whether to port `SExpr` (with an `SLevel` quotient) or work on
`VExpr` directly. Directly on `VExpr` is recommended, to avoid a translation
layer. The `Experimental` files are his upstream work, so coordinate rather than
fork.

### Phase 2: complete CR (6k-10k lines, medium risk; in parallel with Phase 1 under `headInversion`)

- cr-branch `NormalEqN` with `etaBoth`, already in progress.
- Spine exposure (0.4k-0.7k).
- `headParallel` (0.2k).
- `fullStep` :640/:648 (0.2k-0.4k) and :693 (0.1k).
- `strip` :865 (3k-6k).
- Removing the remaining `weakN_iff` uses in ChurchRosser (1k-2k).

All of this may use `uniq` and `INJ` freely.

### Phase 3: STR (8k-15k lines after Phase 2; falsification study 1k-3k first)

As in section 3.

### Risks: statements that might be false as stated

- `rigidApp_inv` for rigid `c` whose declared type is not a literal telescope,
  for example `c : (T : Type 1) → T`. It is still true, but L1 must then handle
  heads whose result type is computed. Consumers only use structures and
  inductive families, so consider restricting to literal telescopes.
- `Rigid` (VEnv.lean:17) inspects only `env.defeqs` left-hand heads. It is
  correct because schema equations are headed by `.elim`, native patterns by
  recursor constants, and quotient rules by `Quot.lift`/`Quot.ind`. `structEta`
  and `unitLike` are headed by constructors, but only at non-sort types. That is
  why every type-level statement needs "typed at a sort", which `TypeChain`
  links provide.
- `sort_inv` gives `≈` (all assignments), the right notion. `extra` rules from
  polymorphic definitions only relate `instL` instances. No risk seen.
- `fieldType_inv_stratified`: true given uniq. The `projDF` guard
  (`resultLevel.IsNeverZero ∨ fieldLevel ≈ 0`) is what keeps data projections out
  of Prop structures. L1 needs it too.
- `mutualDef` and unsafe environments: non-termination is harmless for L1
  (bottom shapes) and for CR (parallel reduction). Unsafe environments also
  need STR (`Declaration.Strengthening` uses `ves.venv .unsafe`). The
  falsification study must include them.
- L1 typed-check rules (2.4): the main research risk. If glued semantics fails,
  the fallback is option C (annotated syntax), which is larger.
- STR with `Eq`: open. The `HEq`-free extraction risk is in 3a.

## 5. Estimate and fallbacks

Totals, in lines:

| Phase | Lines |
|---|---|
| 0 | 2k |
| 0.5 | 3k |
| 1 | 15k-25k |
| 2 | 6k-10k |
| 3 | 9k-18k |
| **All** | **about 35k-55k** |

That is several times `ChurchRosser` plus `FullReduction` today, and comparable to
the whole `Experimental` prototype times three. Phase 1 has perhaps a one-in-three
chance of needing a redesign at the checked-rule semantics. STR could still turn
out false with `Eq`.

Partial results that stand on their own, in order of value per line:

1. Phase 0. Six cone sorries (five Injectivity lemmas plus SAT), the two missing
   separation lemmas, and the stratified-uniq bookkeeping all collapse to one
   base theorem `VEnv.WF.headInversion` with a precise, believed-true statement.
   That statement is also the exact target of the semantic layer. CR and STR work
   can then proceed conditionally on it without circularity.
2. The STR falsification study. It either changes the final theorem's
   hypothesis now, or raises confidence.
3. Singleton eta. It is the formal content of "why `Eq` rescues strengthening",
   and both Phases 1 and 3 need it.
4. The Phase 1 spike on `SExpr` with `Eq`/K and one singleton family. It settles
   whether the semantic route survives typed-check rules, before 15k+ lines are
   committed.
5. Phase 2 under the hypothesis. It closes the confluence sorries outside the
   cone, so CR becomes a theorem modulo `headInversion` alone.
