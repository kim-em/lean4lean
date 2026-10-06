# Base sorries on agent/verify-inductives-base: scope and plan

Worktree /home/kim/worktrees/lean4lean/lean4lean-base, branch
agent/verify-inductives-base (base 061670d, now 9db09de). Full `lake build`
(675 jobs) passes at 9db09de.

## 0. Corrections to the task brief

* ChurchRosser.lean:2166 is NOT the eta/eta case of `NormalEq.trans`. It is
  `NormalEq.headParallel` (normal equality vs a native/schema head
  computation). The eta/eta case of `NormalEq.trans` (ChurchRosser.lean:670)
  has no sorry of its own; it calls `NormalEq.weakN_iff`, whose inverse
  direction `NormalEq.weakN_inv_DFC` (lines 492-611) calls
  `IsDefEqU.weakN_iff` / `HasType.weakN_iff` / `VExpr.WF.weakN_iff`, i.e. the
  sorry at UniqueTyping.lean:205.
* `IsDefEq.uniq` (UniqueTyping.lean:13) is derived (no sorry token), by
  stratified induction, but it calls `forallE_inv_stratified`, `sort_inv` and
  `fieldType_inv_stratified`. So `uniq`/`uniqU` are sorry-dependent.
* UniqueTyping.lean:205 is `IsDefEqU.weakN_iff` (inverse direction), the
  refuted strengthening principle (STRENGTHENING.md).

## 1. Per-sorry scoping

Cone = dependency cone of `Lean4Lean.addDecl.WF` (HANDOFF item 1 audit).

### Injectivity.lean (all in the cone)

1. `IsDefEqU.sort_inv` (:10): `Γ ⊢ sort u ≡ sort v → u ≈ v`.
   Consumers: UniqueTyping (`uniq`, 8 calls), ChurchRosser:1831 (parRed_beta),
   CaseSourceSort:405, ProjectionProofResult:72, CaseMotiveCoherence:94,
   QuotPatternTyping:45, Verify/Inductive/PrimitiveConstructorEvidence:49.
2. `IsDefEqU.forallE_inv_stratified` (:13): Pi injectivity with stratified
   typing bounds preserved. Consumers: `IsDefEqU.forallE_inv` (:22, used in
   ~45 places incl. 11 in ChurchRosser, ProjectionLemmas x9,
   Verify/Inductive/Basic x9, SignatureArity), and `IsDefEq.uniq` app case.
3. `IsDefEqU.sort_forallE_inv` (:32): `¬ sort u ≡ forallE A B`. Consumers:
   SignatureArity (`mkApps_sort_arity`), CaseMotiveCoherence:95/98,
   Nested/AuxiliaryFamilyCorrespondence:129/131/157, Nested/Lowering:1356.
4. `IsDefEqU.fieldType_inv_stratified` (:47): projection field types at
   defeq majors are defeq, levels equivalent. Sole consumer: `IsDefEq.uniq`
   proj case (so transitively everything using `uniq`).
5. `IsDefEqU.rigidApp_inv` (:76): rigid-head application injectivity
   (levels ≈, args pairwise defeq). Consumers: `structApp_inv` (->
   ProjectionLemmas:981), RecursorLemmas:646/912/978/994,
   Verify/Environment/Recursors:150, Verify/Typing/ProjectionUniqueness:47.

Are they consequences of confluence? Mathematically yes (the standard route:
CR + head preservation of reduction + head rigidity of NormalEq). But NOT of
the ChurchRosser development as it stands: that development itself uses
`uniqU`, `IsDefEqU.forallE_inv`, `IsDefEqU.sort_inv` and the weakN_iff family
(ChurchRosser.lean lines 501-611, 638, 1074, 1086, 1244, 1544, 1785-1918,
2197, 2277; FullReduction.lean:78 `FullStep.defeq` uses `uniq`). Deriving
Injectivity from it is circular. A non-circular derivation needs either
(a) a stratified simultaneous induction (CR/inversion at height n using
uniqueness/inversion only below n, the shape `forallE_inv_stratified` was
designed for), or (b) a CR proof whose side conditions are untyped/syntactic
(e.g. CR for an untyped parallel reduction without eta/proof-irrelevance,
then typing only at the end), which does not fit this calculus because
NormalEq has typed proof irrelevance and eta, and FullStep has typed
funEta/structEta. Even given CR, each inversion needs "head preservation":
the reducts of `sort u` are sorts (requires that `sort u` is not typed at a Pi
or a structure family, i.e. `sort_forallE_inv`/sort-vs-rigid at a higher
level), NormalEq at a sort/forallE head is a congruence (requires excluding
the etaL/etaR/proofIrrel leaves, again head separation). STRENGTHENING.md
names exactly this: "Head separation is another necessary case".
Difficulty: research-level; HANDOFF: open upstream too. Not attempted.

### UniqueTyping.lean:205 `IsDefEqU.weakN_iff` (cone)

Inverse direction refuted by the groupoid countermodel. Not provable; must
be removed from consumers (about 72 `Verify` uses per HANDOFF, plus the
ChurchRosser uses above). Out of scope here.

### RecursorLemmas.lean:437 `VConstructorShape.saturated_of_hasType` (cone)

Statement: `mkApps (const ctor cls) args : mkApps (const ind levels) familyArgs`
with `env.Rigid ind` implies `args.length = nparams + nfields`.
Consumers: Verify/Inductive/CompletedRecursorAlignment:59,
Verify/TypeChecker/Recursor:406.
Proof shape: copy `HasType.mkApps_sort_arity` (SignatureArity.lean:11,
~30 lines) with the result `mkApps (const ind (VLevel.params ..)) (...)`
instantiated by `instL cls` in place of `sort u`. Both the "too few" and
"too many" cases end in `forallE A B ≡ mkApps (const ind ls) xs`, which must be
refuted. No such rigid-head vs Pi separation lemma exists (grep: none; only
same-head `rigidApp_inv` and `sort_forallE_inv`). So this is not provable
without a new base lemma of the Injectivity class:

    theorem IsDefEqU.rigidApp_forallE_inv (henv : VEnv.WF env)
        (hΓ : OnCtx Γ (env.IsType U)) (hrigid : env.Rigid c) :
        ¬env.IsDefEqU U Γ (VExpr.mkApps (.const c ls) args) (.forallE A B)

With it: ~60 lines (mkApps_sort_arity analogue + `instL_wrapForalls`,
`wrapForalls_inst`). Not done here because it would only move the sorry
(no new sorry allowed). Recommendation: when the Injectivity layer is
attacked, state this separation there; it is also what the FullReduction
projIota etaL case and FullStep.strip's distinct-family case need.

### ChurchRosser.lean:2166 `NormalEq.headParallel` (outside the cone)

`Γ ⊢ e₁ ≡ₚ e₂ → HeadParallelReduction Γ e₂ e₂' → ∃ e₁', e₁ ≫* e₁' ∧ e₁' ≡ₚ e₂'`.
Used once (NormalEq.parRed appDF extra/schema). Genuine gap: e₂ is an
applied native pattern or case-schema spine; e₁ is related through appDF
spines whose inner nodes may be etaL (left lambdas that must be
beta-reduced, then related by an instantiated NormalEq), proofIrrel (inner
proofs, which force the whole spine into Prop; needs a "Pi into Prop
propagates" lemma using `sort_inv`), constDF (level congruence, partly done
by `const_native_parallel` and `Check.const_levels`). Same core lemma as
the FullReduction gaps below (spine exposure, see plan).

### FullReduction.lean (all outside the cone; part of `full_church_rosser`)

* :640 / :648 (`NormalEq.fullStep`, appDF case, delta / quotDelta step on
  the right, right side not a proof): genuine gap, same spine-exposure
  problem as headParallel, then `congr_normal`/`congr_levels` of the delta
  rule (exists: `fullStep_delta_args`, `fullStep_delta_levels`).
* :682 (projDF, projIota on the right): partly mechanical. Commit 9db09de
  proves the `refl`, `constDF` (args = [] contradicts `hget`) and the
  syntactically impossible `sortDF/lamDF/forallEDF/projDF/elimDF/etaR`
  majors. Remaining `appDF | etaL` (one sorry): appDF = spine exposure;
  etaL at the top needs rigid-head vs Pi separation for the structure type.
* :844 (`FullStep.strip`, proj of structEta with a different family):
  needs distinct rigid heads separation (`mkApps (const F ..) ≢ mkApps (const G ..)`
  for F ≠ G rigid), another Injectivity-class lemma.
* :845 / :846 (`FullStep.strip`, all remaining step kinds: core ParRed vs a
  full development, delta, quotDelta, projIota, app/lam/forallE/proj
  congruence): this is the whole confluence (strip) proof for the full
  calculus. Large.

None of the FullReduction sorries is a mechanical omission except the
subcases closed in 9db09de.

## 2. Dependencies

    weakN_iff (refuted) <- NormalEq.weakN_inv_DFC <- NormalEq.trans (eta/eta)
                         <- ParRed.weakN_inv, parRed_beta, hasType_app_bvar0
    sort_inv, forallE_inv_stratified, fieldType_inv_stratified <- IsDefEq.uniq
    uniq/forallE_inv/sort_inv <- ChurchRosser (NormalEq.trans appDF,
        parRed beta, ParRed.triangle, ...), FullStep.defeq
    headParallel, fullStep gaps, strip gaps <- full_church_rosser
    rigid-vs-Pi separation (missing) <- saturated_of_hasType, projIota etaL
    distinct-rigid separation (missing) <- strip :844
    (Injectivity <- CR) only via a stratified mutual induction.

## 3. Plan for the hard ones

### 3a. Replace the weakN_iff use in the NormalEq.trans eta/eta case

Can the Nat-indexed bound replace it? Yes for `trans`, but only with a
change of the relation, not a helper lemma. The eta/eta case needs
`e1 ≡ₚ e3` from `A::Γ ⊢ app e1.lift #0 ≡ₚ app e3.lift #0`; the appDF subcase
yields `e1.lift ≡ₚ e3.lift` whose typing premises mention types in `A::Γ`
that need not be lifts, so syntactic strengthening is exactly the refuted
principle. Proposal:

1. Add an extensionality constructor (or replace etaL/etaR by it plus
   one-sided forms):

       | etaBoth : Γ ⊢ e : .forallE A B → Γ ⊢ e' : .forallE A B →
           A::Γ ⊢ .app e.lift (.bvar 0) ≡ₚ .app e'.lift (.bvar 0) → Γ ⊢ e ≡ₚ e'

   and index the relation by a bound: `NormalEqN : Nat → List VExpr → VExpr → VExpr → Prop`
   with eta constructors charging 2, appDF charging 1 + max/sum of
   children, all others 1 + children. `NormalEq Γ a b := ∃ n, NormalEqN n Γ a b`.
2. Bound-preserving transport: `NormalEqN.weakN` (bound preserved, forward
   only), `NormalEqN.instN` (bound preserved), `NormalEqN.defeqDFC`.
   No inverse weakening anywhere.
3. `NormalEqN.trans` by strong induction on `n₁ + n₂`:
   etaR/etaL pair -> `etaBoth` directly (no strengthening);
   etaBoth/arbitrary H2: expand H2 to `app e2.lift #0 ≡ₚ app e3.lift #0`
   by `appDF (weakN H2) (refl #0)` (bound n₂+1) and compose with the body
   (bound n₁-2): sum decreases. Symmetric case likewise.
   The appDF/appDF case still needs the type alignment of the two function
   typings (`uniqU`, then `forallE_inv`); STRENGTHENING.md flags this; it is
   sound but keeps the Injectivity dependency.
4. Consumers must handle `etaBoth`: `NormalEq.defeq` (via `IsDefEq.eta`
   twice + lamDF), `symm`, `parRed` / `fullStep` (via `FullStep.funEta` on
   the left: `e →funEta lam A (app e.lift #0)` then reduce under the binder,
   output `lam A X`, related by etaL; this is why FullStep has funEta; in
   the ParRed-only presentation (ChurchRosser.lean) the case is not
   closable, so the ParRed CR (`ParRedS.church_rosser`, `CRDefEq`) would
   either be retired in favour of FullReduction or keep weakN_iff).
   The other weakN_iff uses in ChurchRosser (1244 `ParRed.weakN_inv` checks,
   1790 `hasType_app_bvar0`, 1850/1910 `parRed_beta` lift cases) need
   separate treatment: `hasType_app_bvar0` and `parRed_beta.lift` only need
   typing strengthening of terms already known typed in Γ (replace by
   carrying the Γ typing as a hypothesis from the caller, who has it);
   `ParRed.weakN_inv`'s pattern-check strengthening is a genuine
   defeq-strengthening of check premises and should become a hypothesis
   on the native pattern checks (checks closed / not depending on the lifted
   variables) or be dropped with ParRed.weakN_inv if unused after the
   switch to FullReduction.
   Size: NormalEqN definition and transport ~400 lines; trans ~150;
   consumer updates in ChurchRosser/FullReduction/NativePrefixNormalCongruence/
   QuotPrefixNormalCongruence/NormalSubstitution (~240 NormalEq mentions)
   ~800-1500 lines of edits. Removes the strengthening dependency from
   NormalEq.trans; it does not remove any Injectivity dependency.

### 3b. Spine exposure (shared by headParallel, fullStep :640/:648/:682)

Key lemma (stated over NormalEqN so recursion after beta+instN is on the
bound):

    theorem NormalEqN.spine_expose (hΓ) (hrigid : head c is not computed by the step)
        (H : NormalEqN n Γ x (mkApps (.const c ls) args))
        (bs bs' : List VExpr) (hbs : Forall₂ (NormalEq Γ) bs bs')
        (ht : Γ ⊢ mkApps x bs : T) :
        (∃ P, Γ ⊢ T : P ∧ Γ ⊢ P : sort 0)       -- proof case, close by proofIrrel
        ∨ ∃ ls' args', FullReduction Γ (mkApps x bs) (mkApps (.const c ls') args') ∧
            Forall₂ (· ≈ ·) ls' ls ∧ Forall₂ (NormalEq Γ) args' (args ++ bs')

Cases: refl/constDF trivial; appDF moves one argument into `bs`; etaL with
nonempty `bs` beta-reduces, instN gives `NormalEqN n' Γ (e[b]) (app f₂ b)`
with n' < n; etaL with empty `bs` is the top-level Pi case and needs the
separation lemmas below (or is excluded by T not being a Pi); etaR is
impossible (right side is a spine); proofIrrel at any prefix propagates to
the proof case via "a Pi in Prop has its codomain in Prop" (needs
`IsDefEqU.sort_inv` + `HasType.forallE_inv` + uniqueness).
Supporting: `NormalEqN.instN` with bound preservation, Prop propagation
lemma (~60 lines), mkApps/FullReduction plumbing (exists).
Size: ~400-700 lines. Then headParallel ~200 lines (combine with
`Check.const_levels`, `NormalEq.apply_pat`, `schema_of_spine`),
fullStep :640/:648 ~100 lines each (with `congr_normal` + `congr_levels`;
a combined levels+normal congruence of NativeDeltaRule may be needed,
~150 lines), :682 appDF ~80 lines.

### 3c. Injectivity layer (sort_inv, forallE_inv_stratified,
sort_forallE_inv, fieldType_inv_stratified, rigidApp_inv, plus the missing
rigidApp_forallE_inv and distinct-rigid separation)

Only route compatible with the existing code: a stratified mutual
induction on the height bound n of `HasTypeStratified`, proving at each n
simultaneously (i) uniqueness of types (the existing `IsDefEq.uniq`
proof), (ii) CR for defeq of terms whose types have height < n, (iii)
head preservation and NormalEq head rigidity at height n, (iv) the five
inversions + two separations as corollaries of (ii)+(iii). This requires
every typing side condition used in the CR proof (NormalEq premises,
FullStep.funEta/structEta typing, uniqU in appDF transitivity) to be
height-indexed. Estimate: 5k-10k lines, consistent with HANDOFF ("open
upstream"); the `Experimental/ShapeLogRel*`/`Stratified*` files are prior
attempts (still with sorries). The logical-relations alternative
(Abel-Ohman-Vezzosi style, cf. Experimental/LogRel*.lean) avoids CR
entirely but must model proof irrelevance, eta, structure eta, quotients
and the generated recursors; similar or larger size.

Once (i)-(iii) exist: sort_inv ~100 lines, sort_forallE_inv ~80,
forallE_inv_stratified ~200 (bounds), rigidApp_inv ~250 (spine exposure on
both sides + Forall₂ assembly), fieldType_inv_stratified ~300 (major
injectivity via rigidApp_inv on the structure type, then fieldType
congruence under instantiation), rigidApp_forallE_inv ~80,
saturated_of_hasType ~60 on top.

## 4. What was done

* 9db09de refactor: discharge the trivial major cases of projection iota
  under normal equality (FullReduction.lean projIota; sorry narrowed to
  `appDF | etaL`, sorry count unchanged).
* No sorry was removed: none of the listed sorries is provable with
  moderate effort; each needs either the spine-exposure lemma over an
  indexed NormalEq, the strip/confluence proof, or Injectivity-class
  separation lemmas that do not exist yet.
* `lake build` (675 jobs) passes at 9db09de.
