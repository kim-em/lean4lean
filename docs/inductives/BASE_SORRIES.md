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

## 5. Confluence step 1 (agent/verify-inductives-cr, 2026-10-06)

Normal equality is re-indexed: `NormalEqN : Nat → List VExpr → VExpr →
VExpr → Prop` with leaves at bound 0, congruences at one plus their
premises, and `etaL`/`etaR`/`etaBoth` at two; `NormalEq Γ a b := ∃ n,
NormalEqN n Γ a b`, with constructor-named theorems so consumers are
unchanged. `etaBoth` relates two functions whose applications to a fresh
variable are related. Weakening, substitution and context conversion
preserve the bound; `NormalEqN.trans` recurses on the sum of the bounds, and
the eta/eta case closes by `etaBoth`. `NormalEq.weakN_inv_DFC`,
`NormalEq.weakN_iff`, `ParRed.weakN_inv`, `hasType_app_bvar0` and the
`ParRedExt` beta machinery are deleted; ChurchRosser.lean has no
`weakN_iff` reference. The ParRed-only confluence (`CRDefEq`,
`ParRedS.church_rosser`) is retired: `etaBoth` needs `FullStep.funEta`.

In FullReduction.lean:

* `NormalEqN.spine_expose`: a term related to a rigid-headed spine (applied
  to related extra arguments) is a proof, reduces to a spine with an
  equivalent head and related arguments, or reduces to a lambda whose body
  is a smaller comparison with the eta expansion of such a spine.
* `NormalEq.parRed` is proved for every parallel step through
  `SpineTransport` (structural on the step, at every renaming and extra
  spine, strong induction on the bound). `SpineTransport.redex` handles
  native iota and generated case redexes. This removes
  `NormalEq.headParallel`.
* `NormalEqN.fullStep` uses strong induction on the bound; constant-headed
  rules (native prefix unfolding, quotient lifting) go through
  `NormalEqN.fullStep_rigidRule`, projection iota through
  `NormalEqN.fullStep_projIota`. The three `NormalEq.fullStep` sorries and
  the distinct-family case of `FullStep.strip` are closed.

After the Phase 0 merge these separation facts are theorems (commits
f14b82d8, efb7f95b, fb9b570b), and no class hypothesis remains:

* rigid head against Pi and distinct rigid heads: `IsDefEqU.rigidApp_forallE_inv`,
  `IsDefEqU.rigidApp_ne` (from `VEnv.WF.headInversion`).
* case majors: `MatchedCaseStep.major_not_pi`, from the declaration-history
  invariant extended with `VEnv.CtorResultRigid` (the constructor major of
  every installed native equation returns a rigid family) and
  `WF.case_family_head_rigid` (the family head of every registered case owner
  with a rule is rigid; containers are traced through their installed
  equations).
* native majors: `Params.major_not_pi` (major domain of the restored recursor
  type, `NativeRecursorRegistered.family_head_rigid`; quotient major `Quot`).
  `Params.pat_recursor` now also records that an iota pattern's owner has a
  constructor.
* proof majors: `Params.major_proof`; small eliminators by
  `NativeRecursorRegistered.result_sort`, large ones by the nonzero
  source-level check and `NativeRecursorRegistered.major_not_proof`.

Remaining at that point (now closed, see §6): `FullStep.strip` for the core, delta, quotient, projection iota
and congruence steps. Strip follows from a local property D' (for two steps
from one source, one side closes in at most one step, the other in a
reduction, modulo normal equality) together with `NormalEq.fullReduction`,
by induction on the development. D' fails for `FullStep` as defined because
its delta, quotient, projection iota and eta steps do not reduce their
subterms in parallel: substituting a stepped argument into a stepped body
need not be a single step. The route is a fully parallel full-step relation
between `FullStep` and `FullReduction`, its substitution lemma, and the
critical pairs, including native iota against native prefix unfolding at
the same recursor head.

`lake env lean scripts/InductiveAudit.lean`: `NormalEq.parRed` depends on
`sort_inv`, `forallE_inv_stratified`, `sort_forallE_inv` and
`fieldType_inv_stratified`; `IsDefEq.full_church_rosser` on these and
`FullStep.strip`; neither depends on `IsDefEqU.weakN_iff`.

## 6. FullStep.strip by levelled local diagrams

`FullStep.strip`, `FullReduction.church_rosser` and `IsDefEq.full_church_rosser`
are proved without `sorry` (`Theory/Typing/LevelledReduction.lean` and
`Theory/Typing/FullChurchRosser.lean`). Their only remaining `sorryAx`
dependencies are `WF.headInversion` and `IsDefEqU.weakN_iff`.

### The obstacle to a strongly closed parallel relation

A fully parallel relation P with FullStep ⊆ P ⊆ FullReduction whose peaks close
in at most one step each does not exist, because `FullStep.funEta` may expand
the function of an application. Counterexample: in an environment with `Nat`,
let `f := Nat.rec (motive := fun _ => Nat) z s` with `z : Nat` a variable, and
`t := app f Nat.zero`. Then `t → z` by native iota, and
`t → app (lam Nat (app f.lift #0)) Nat.zero` by
`FullStep.app (FullStep.funEta _) FullStep.rfl`. Every one-step reduct of the
latter (parallel beta reduces the body before substitution, so iota cannot
fire) is an application or a lambda, and `z` only reduces to itself; no such
pair is `NormalEq` (`Nat` is not a proposition). The peak closes in two steps
(beta, then iota).

Native iota and native prefix unfolding do not overlap: `NativeDeltaRule`
requires a large target with source level equivalent to zero, while the native
iota guard for large targets requires the source level to be nonzero.

### Why not restrict `funEta` to non-head positions (route (a))

The transports of computation through normal equality produce head
expansions. `NormalEqN.beta_aux` (`FullReduction.lean`) matches a beta step on
one side of a normal equality whose eta derivation ends in `etaBoth` by
expanding the other side with `FullStep.funEta`, and through the `appDF` case
that side is the function of an application. `NormalEq.parRed`,
`NormalEq.fullStep` and the final transport in `FullReduction.church_rosser`
all go through it. Restricting `funEta` would require redesigning these
transports; the levelled route leaves `FullStep` and the transports unchanged.

### Route taken: levelled local diagrams (route (c))

`Theory/LevelledConfluence.lean` proves an abstract criterion in the style of
decreasing diagrams: if the relations below level n are confluent, two level-n
steps close by lower steps around at most one level-n step on each side, and a
level-n step against a lower step closes by lower steps on its own side and by
at most one level-n step followed by lower steps on the other side, then the
relations up to level n are confluent. The proof counts level-n steps; no
multiset ordering is needed.

`FullStep` is split into four parallel relations (`LevelStep`):

0. `NormalEq₀`: normal equality without eta (structural, universe levels,
   proof irrelevance), obtained by indexing `NormalEqN` by an eta flag;
1. `ParRed`: beta, native and registered schema patterns;
2. `DeltaPar`: parallel native prefix unfolding, quotient prefix unfolding and
   projection of constructor applications;
3. `EtaPar`: parallel function and structure eta expansion.

Eta sits above beta, as the counterexample requires: the expansion side of the
peak may take any number of lower steps. Every `FullStep` is a single `UpStep`
below level 4 (`FullStep.upStep`), and `Below.full` turns a levelled reduction
back into a `FullReduction` followed by `NormalEq`, which yields
`FullStep.strip`.

The local diagrams are `ParRed.church_rosser` for `NormalEqF false` (level 1),
`DeltaPar.peak` and `DeltaPar.parRed_peak` (level 2), `EtaPar.peak`, `EtaPar.deltaPar_peak` and
`EtaPar.parRed_peak` (level 3), and the `normalEq₀_mirror` lemmas against
level 0. The eta lemmas use induction on the size of the source; root eta
expansions are peeled off by `Join3.fun_left` and `Join3.struct_left`, and a
root computation meeting an expanded head or major is undone by the
`collapse_*` lemmas with a lower beta or projection step.

### New `Params` assumptions

The prefix computation diagrams use seven new fields of `Params`
(`ChurchRosser.lean`); `Params` has no instance in the repository, so no
instance obligations change:

* `pat_const_native`: definition patterns never unfold a native recursor or
  `Quot.lift` (their prefixes compute by `DeltaPar`, so the two must not
  overlap);
* `recursorData_quot`: `Quot.lift` is not a registered native recursor;
* `pat_ctor_rigid`, `projection_ctor_rigid`: constructors of native iota
  patterns and structure constructors are rigid heads;
* `pat_struct_major`, `schema_struct_major`: a native iota or case major of
  structure type is a saturated application of the structure constructor;
* `pat_iota_params`: native iota at a structure constructor reads only the
  fields, not the parameters, so a structure eta expansion of the major
  collapses by projection.

## 7. The `Params` instance of a well-formed environment

`Theory/Typing/ConcretePatterns.lean` defines the concrete pattern table
`ConcretePattern registry env` (definition unfoldings, the primitive quotient
rule when the quotient declaration is present, and native iota rules), over the
canonical registry of `VEnv.WF.canonicalRegistry`, and proves its syntactic
non-overlap facts. `Theory/Typing/ConcreteParams.lean` assembles `Params` from
it. Two `Params` fields were restated truthfully:

* `pat_const_native` and `recursorData_quot` exclude `Quot.lift` only when
  `QuotRegistered env` holds: without the quotient declaration, `Quot.lift` is
  an ordinary name and may be a definition.
* `pat_struct_major` and `schema_struct_major` take the typing context's
  well-formedness, since they are proved by uniqueness of types.

### Confluence is false for some well-formed environments

`VEnv.WF` admits environments in which `VEnv.IsDefEq` is not confluent in the
full presentation, so `FullEquationCoverage` and the unconditional
`VEnv.WF.church_rosser` are false as stated:

1. Large elimination from a `Prop` family is excluded from native iota
   (`pat_recursor` forces the guard `.nonzero sourceLevel`), so its only
   computation is the singleton prefix unfolding `NativeDeltaRule`. Its replay
   requires typed captures, and a proof-field selector is a case-eliminator
   application at generic indices. The strengthening agent's countermodel
   `envCM` (branch `agent/verify-inductives-base`, `Theory/Typing/Countermodel/`)
   exhibits a family where that selector is ill-typed, so the singleton
   equation cannot be joined. Independently, the selector needs the case
   schema to be registered: `inductive And` installed without
   `inductEliminators` is well formed, and its `And.rec` equation (source
   level zero, large target) cannot be joined. The planned repair, following
   the coordinator, is `Eq`-cast extraction selectors under
   `env.HasCanonicalEq`.
2. `inductProjections` and `inductEliminators` may register metadata for the
   same constants from different declarations. Example (found by the
   structure-major fork): register `structure S : Type` with constructor `S.a`
   over axioms `S`, `S.a`; add the axiom `S.b : S`; register the case schema of
   `inductive S | b : S` over the empty base. Then `elim m x S.b` computes to
   `x` while `elim m x S.a` is stuck, although `S.a ≡ S.b` by the unit-like
   rule. This was a specification defect; see the resolution below.

### Resolution: Church-Rosser under canonical `Eq`

Canonical `Eq` is the only hypothesis of the final theorem besides
well-formedness:

```lean
theorem VEnv.WF.church_rosser {env : VEnv} (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U)) (H : env.IsDefEq U Γ e₁ e₂ A) :
    letI := henv.params U
    ∃ e₁' e₂', FullReduction Γ e₁ e₁' ∧ FullReduction Γ e₂ e₂' ∧ NormalEq Γ e₁' e₂'
```

Eliminator coherence (decision 2026-10-07, gap 2 above) is now part of
well-formedness: `VEnv.WF'.inductEliminators` requires
`VInductDecl.ProjectionsCoherent env source` (the projections already
registered for the certified declaration's families are that declaration's own
entries, `Theory/Typing/Env.lean`), and `VEnv.WF.eliminatorsCoherent`
(`Theory/Typing/EliminatorCoherenceOfWF.lean`) derives
`VEnv.EliminatorsCoherent` by induction on `WF'`: every later projection
registration is for fresh family names. `Certified.register_after_constructors`
proves the new premise from freshness of the declaration's types;
`CheckingEnv.Valid.registerCases` takes it as a premise (no producer in the
verified pipeline calls it).

(`Theory/Typing/WFParams.lean`). Its only `sorry` dependency is
`VEnv.WF.headInversion`; it does not use `VEnv.Strengthening`,
`strengthening_of_canonicalEq` or `IsDefEqU.weakN_iff`.

1. The singleton prefix program (`NativeRecursorData.singletonProgram`,
   `Theory/Typing/NativeSingletonProgram.lean`) reconstructs the constructor
   with `PropElim.occ`: data fields are read from the literal index slots, and
   proof fields are extracted from the major by the native recursor at motive
   universe `Prop`, with earlier data fields cast along `Eq`. It no longer uses
   case-eliminator selectors, so no eliminator registration is needed.
2. `NativeRecursorRegistered.zero_join`
   (`Theory/Typing/NativeSingletonCoverage.lean`) joins the installed equation
   of a large-eliminating native singleton at a universe specialization with
   source `Prop`. Under the equation's binders, the recursor applied to its
   prefix unfolds by `NativeDeltaRule` at the literal constructor instance,
   then a beta step with the constructor major gives the right side at the
   reconstructed fields. Data fields reconstruct to the field variables
   themselves; proof fields are related to them by proof irrelevance. The
   replay obligations are typed by `PropElim.occ_typed` and
   `PropElim.singleton_eta`, which need `env.HasCanonicalEq`.
3. `WF.singletonCoverage` discharges `WF.SingletonCoverage` from it, and
   `WF.church_rosser` follows from `WF.church_rosser_of_singletonCoverage`.

### Notes for the next session

* `Theory/Typing/NativeIotaSoundness.lean` imports two Verify modules
  (`Verify.Inductive.Nested.RecursorProvenance`,
  `Verify.Inductive.Nested.AssemblyNativeWhnf`); it is the only Theory file
  that does. There is no import cycle. Follow-up: move the lemmas it uses into
  Theory (`restoredFamilyHead_spec`, `restored_iota_shape`,
  `restoredConstructorShape`, `containerConstructors`,
  `Restoration.expr_wrapLams_eq`, `expr_wrapForalls`, `expr_liftN`,
  `expr_recursorMajor_source`, `expr_recursorMajor_auxiliary`,
  `find?_of_nodup`, `declaration_ctor_mem`, `vars_eq_bvarRange`,
  `vars_map_liftN`).
* `NativeIotaPattern.sound` uses `VIotaRuleShape.iota_of_args`, a
  strengthening-free variant of `VIotaRuleShape.iota` (which still takes
  `VEnv.Strengthening` for its Verify callers).
