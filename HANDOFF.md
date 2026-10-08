# Inductive verification: final state of `agent/verify-inductives`

Current account, 2026-10-08. This file describes only the final state of the branch and the
work still in progress. The chronological record that led here (decisions as they were taken,
superseded routes, intermediate statuses) is
[docs/inductives/history/HANDOFF-chronicle.md](docs/inductives/history/HANDOFF-chronicle.md).
The source and the checked theorem types take precedence over this account. The standing
instruction for the branch is [docs/inductives/GOAL.md](docs/inductives/GOAL.md).

## 1. The theorem

```lean
theorem addDecl.WF_of_canonicalEq {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (heq : ∀ safety, (ves.venv safety).HasCanonicalEq)
    (hch : ∀ safety, (ves.venv safety).HasCanonicalChoice)
    (decl : Declaration) (hdecl : decl.IsModelled env ves) :
    (addDecl env decl (check := true) (fuel := {})).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety
```

in [Lean4Lean/Verify/Environment.lean](Lean4Lean/Verify/Environment.lean). If the checked
`addDecl` succeeds, the result environment is modelled by abstract environments `ves'` that
are well formed and extend the input models at every safety level. The dependency cone has an
empty `sorry` inventory. `addDecl.WFHasCanonicalEq` is the iterable form: it also returns
`HasCanonicalEq` and `HasCanonicalChoice` for `ves'`, so the theorem applies again to the next
declaration of a replay.

The hypotheses, and what each one costs:

- `wf : ves.WF env`. The executable environment is modelled by well-formed abstract
  environments. This is the invariant being preserved; it is not an extra assumption.
- `heq : HasCanonicalEq` ([Theory/CanonicalEq.lean](Lean4Lean/Theory/CanonicalEq.lean)).
  A constant-presence predicate: `Eq`, `Eq.refl`, `Eq.rec` are present with the stored types
  of the prelude, and the iota rule of `Eq.rec` is a definitional equation. It is monotone
  (`VEnv.HasCanonicalEq.mono`) and realized by the replay of `Init.Prelude`
  ([Verify/CanonicalEqRealization.lean](Lean4Lean/Verify/CanonicalEqRealization.lean),
  `addDecl.eqBootstrapHasCanonicalEq`; executable side checked by
  [Tests/CanonicalEq.lean](Lean4Lean/Tests/CanonicalEq.lean)). It is used at exactly one
  place: the quotient declaration. `addQuot.WF`
  ([Verify/QuotInit.lean](Lean4Lean/Verify/QuotInit.lean)) needs `Eq` present at every safety
  level, because the executable's `checkEqType` checks the shape of `Eq` but not its safety,
  and the type of `Quot.lift` mentions `Eq`; the underlying theorem `addDecl.WF` takes that
  readiness (`VEnv.QuotReady` at each level) as its hypothesis and `WF_of_canonicalEq` derives
  it from `heq`. The confluence theorem `WF.church_rosser` also needs it, outside the cone.
- `hch : HasCanonicalChoice`
  ([Theory/CanonicalChoice.lean](Lean4Lean/Theory/CanonicalChoice.lean)). A constant-presence
  predicate: `Nonempty`, `Nonempty.intro` and the axiom `Classical.choice` are present with the
  prelude's types (one universe parameter each; `Nonempty.rec` is not required). Monotone, and
  realized by the prelude replay
  ([Verify/CanonicalChoiceRealization.lean](Lean4Lean/Verify/CanonicalChoiceRealization.lean),
  `VEnvs.WF.hasCanonicalChoice`; [Tests/CanonicalChoice.lean](Lean4Lean/Tests/CanonicalChoice.lean)).
  It is used at exactly one place, the projection-walk corner (section 3(b)). The honest
  reading of the theorem is therefore: soundness of `addDecl` in environments that contain
  the canonical prelude declarations, which every real Lean environment does.
- `hdecl : decl.IsModelled env ves`. Now `True` for every declaration form, including
  `quotDecl` (covered by `addQuot.WF` since 2026-10-08; see
  [QUOT_THEOREM.md](docs/inductives/QUOT_THEOREM.md) and
  [Tests/QuotInit.lean](Lean4Lean/Tests/QuotInit.lean)). It is kept only because GOAL.md fixes
  the statement; it can be dropped. Inductive declarations (ordinary, mutual, nested) carry no
  declaration-specific premise; their evidence is reconstructed from the execution.

No hypothesis names an input, hides a proof in a structure field, or supplies a semantic
answer: the obligations of section 3 are theorems for every well-formed environment.

## 2. Verification and acceptance commands

State of `agent/verify-inductives` at the time of writing:

| check | result |
|---|---|
| `lake build` | 881 jobs, no "declaration uses sorry" |
| `lake build Lean4Lean.Tests` | 556 jobs, green |
| `lake build Lean4Lean.Experimental` | 263 jobs, green (56 inherited prototype sorries, section 6) |
| `lake exe lean4lean --fresh Init.Prelude` | 1975 declarations checked |
| `lake exe lean4lean --fresh Init.Core` | 3953 declarations checked |
| `python3 scripts/check-inductive-audit.py --self-test` | passes |
| `python3 scripts/check-inductive-audit.py --require-complete` | "No sorry dependencies; all remaining axioms are listed." |
| `#print axioms addDecl.WF_of_canonicalEq` | 32 axioms: 3 standard + 29 implementation axioms, exactly the inventory |
| `grep -rn sorry Lean4Lean` outside `Experimental/` | only doc-comment mentions |

Acceptance for any change to the branch: run all of the above. The audit
(`scripts/InductiveAudit.lean`, driven by `scripts/check-inductive-audit.py`) walks the cone of
`addDecl.WF` and compares its axioms with `scripts/inductive-audit-inventory.json`
(`openProofs: []`). Preserve the toolchain `leanprover/lean4:v4.33.0-rc2`; add no axioms; add no
runtime rejections to ease proofs.

## 3. How the three obligations closed

GOAL.md listed three open obligations. Their final status:

**(a) Head inversion, `VEnv.WF.headInversion`**
([Theory/Typing/HeadInversion.lean](Lean4Lean/Theory/Typing/HeadInversion.lean)). Proved for
every well-formed environment, without canonical `Eq`, following Mario's plan of a model of the
full calculus. It is assembled from two halves (statements in `HeadInversionDefs.lean`):

- Separation (sort, Pi and distinct rigid heads are never convertible): `WF.headSeparation`.
  On the branch it is currently obtained from the shape model `Theory/Typing/ShapeModel/`
  (Phase 1a; decisions D1 to D17 in [PHASE1_NOTES.md](docs/inductives/PHASE1_NOTES.md)).
  The observation model already proves it independently
  (`WF.headSeparationModel`, `HeadInjectivity/Model/Separation.lean`), and the shape model is
  being removed in its favour (section 6).
- Injectivity (Pi domains and bodies, rigid arguments, former arguments, projection field
  types): `WF.headInjectivity`, from soundness of the glued observation model
  `Theory/Typing/HeadInjectivity/` (Phase 1b): history induction `WF.soundEnv`, rule soundness
  in `Model/RuleSound.lean` and `Model/Sound.lean`, projections through `Model/ProjSound.lean`,
  constructor fields `ctor_field_obs`, eta through `Model/EtaBind.lean`. Design and decisions:
  [PHASE1B_NOTES.md](docs/inductives/PHASE1B_NOTES.md).

Uniqueness of types (`IsDefEq.uniq`) and every inversion lemma of `Injectivity.lean` derive
from it.

**(b) Strengthening, `strengthening_of_canonicalEq`.** Not proved; removed from the
development. Declarative strengthening rests on a conversion-elimination theorem for which no
proof organisation is known ([STRENGTHENING_NOTES.md](docs/inductives/STRENGTHENING_NOTES.md);
without canonical `Eq` it is refuted by [STRENGTHENING.md](docs/inductives/STRENGTHENING.md)).
The goal allowed the E1 redesign instead:

- E1, scoped caches. Every binder of the checker saves and restores the inference and
  conversion caches (`State.leaveScope`, `checkLCtx`, [TypeChecker.lean](Lean4Lean/TypeChecker.lean)),
  so a cached fact never outlives the local context in which it was established and the
  verification never needs to move a typing to a smaller context. Rationale and the
  experiment showing the unscoped checker is not local:
  [CacheScopeExperiment.lean](docs/inductives/CacheScopeExperiment.lean). Inductive-side
  sites: [E1_INDUCTIVE_DESIGN.md](docs/inductives/E1_INDUCTIVE_DESIGN.md).
- The one remaining site is the projection-walk corner: the kernel's `infer_proj` walks the
  constructor telescope of a structure and must drop a field binder that the body does not
  mention. It is proved by substitution, not strengthening: eliminate the structure into
  `Prop` with motive `fun _ => Nonempty D`, then substitute `Classical.choice` of the result
  (`VEnv.WF.corner_inhabit_choice`,
  [Theory/Typing/ProjectionCornerChoice.lean](Lean4Lean/Theory/Typing/ProjectionCornerChoice.lean);
  `projectionWalkCorner_choice`, [Verify/Typing/ProjectionCorner.lean](Lean4Lean/Verify/Typing/ProjectionCorner.lean)).
  It needs an eliminator of the structure at every projection site, so every inductive block
  now registers a certified case eliminator before its projections (constructor boundary:
  [Verify/Inductive/ConstructorBoundary.lean](Lean4Lean/Verify/Inductive/ConstructorBoundary.lean);
  nested blocks: [Verify/Inductive/Nested/CaseEliminators.lean](Lean4Lean/Verify/Inductive/Nested/CaseEliminators.lean)).
  Indexed structures and blocks with several families are covered: the inhabitant comes from
  the registered case eliminator, whose families include every structure of the block
  (`ProjectionCornerIndexed*.lean`, `ProjectionCornerChoice.lean`).
- A choice-free corner was reviewed in
  [CORNER_ASTRA_REVIEW.md](docs/inductives/CORNER_ASTRA_REVIEW.md): no known proof avoids
  both choice and a substantial strengthening or conversion-locality argument.

`VEnv.Strengthening` survives only as a definition used by the parked countermodel
(`Theory/Typing/Countermodel/`).

**(c) Confluence, `FullStep.strip`.** Proved
([Theory/Typing/LevelledReduction.lean](Lean4Lean/Theory/Typing/LevelledReduction.lean),
by decreasing diagrams over a four-level split of `FullStep`). The concrete `Params` instance
of a well-formed environment is `WF.params`
([Theory/Typing/WFParams.lean](Lean4Lean/Theory/Typing/WFParams.lean)); the resulting
`WF.church_rosser (henv) (heq)` needs canonical `Eq` (without it, confluence of `IsDefEq`
fails; see STRENGTHENING.md) and is not in the cone of the top-level theorem.

## 4. Specification changes, divergence, trusted base

Changes to the branch's own earlier specification. Each restricts the specification to what
Lean actually produces, or reorders installation; none weakens a theorem:

- `Instance.FreeTarget`: a recursor's target universe is `≈ zero` or a universe parameter not
  occurring in the declaration's levels, exactly the shape `getElimLevel` produces.
- `StructCompat` (decision D10 of PHASE1_NOTES.md).
- `ProjectionsCoherent` and `ProjNamesRegistered` are premises of `inductEliminators`, so a
  structure's projections and its eliminator schema come from the same declaration
  (`WF.eliminatorsCoherent`, `EliminatorCoherenceOfWF.lean`).
- The case-only certificate with header agreement and index restoration; case eliminators
  installed between constructors and projections (`VInductBlock.WF`, `install`, `AddInduct`).
- `EliminatorsWF` admits a block with neither eliminators nor projections only when it has no
  families; window typings are stated in the window environment (`∃ es, OwnCaseEliminators`).
- The `RestoredEliminator` alternative of `RenamingReplacementOnCtx` (E1_INDUCTIVE_DESIGN.md
  section 5.4).

Executable divergence from the C++ kernel introduced by the branch: only the scoped caches of
E1 (section 3(b)): the checker discards cache entries made under a binder when it leaves that
binder, where the C++ kernel keeps them. Both fresh replays accept the same declarations as
before. Its `divergences.md` entry is maintained on a concurrent branch.
The other entries of `divergences.md` are upstream lean4lean divergences.

Trusted base: Lean's 3 standard axioms plus 29 implementation axioms, listed in
`scripts/inductive-audit-inventory.json`: 25 in [Verify/Axioms.lean](Lean4Lean/Verify/Axioms.lean)
(equations identifying the compiled implementations of `Expr` operations, `Level` operations,
`PersistentArray`, `PersistentHashMap`, `Std.TreeMap` and `Syntax.structEq` with their Lean
models, including `abstractN_eq`, the exact model that replaced the false
`Lean.Expr.abstract_eq`), the two pointer-equality
axioms of [PtrEq.lean](Lean4Lean/PtrEq.lean), and the two native `bv_decide` certificates of
[Verify/Expr.lean](Lean4Lean/Verify/Expr.lean). All existed on `master` in some form; the branch
added none.

## 5. Kim's decisions of 2026-10-08

Recorded in GOAL.md ("Amendments") and, with the reasoning at the time, in the chronicle under
"Literal reading of GOAL.md":

1. Item (1) of GOAL.md ("no `sorry`") covers the branch's own development. The `sorry`
   declarations inherited from Mario's prototypes under `Lean4Lean/Experimental/` stay as on
   `master`.
2. The canonical-choice hypothesis `hch` is accepted as part of the final theorem. The
   choice-free strengthening effort continues as a bonus and, if it succeeds, deletes `hch`.

With these, the branch meets the goal as amended, buildable with hypotheses `WF`,
`HasCanonicalEq` (used by the quotient case), `HasCanonicalChoice`, `IsModelled` (trivial),
and not with fewer.

## 6. Open and in-progress work

In progress on branches off `agent/verify-inductives` (none of this is merged yet):

- `agent/verify-inductives-quot`: MERGED (d7f53f0b). `addQuot.WF` covers `quotDecl`;
  `IsModelled` is true for every declaration form. The new test exposed a pre-existing
  executable quirk inherited from `master`: lean4lean's `addQuot` marks the `q` binder of
  `Quot.ind` implicit where the C++ kernel and Lean's declaration have it explicit (binder
  info does not affect typing; the test compares up to binder info). A one-line fix is
  prepared as a separate branch for upstream.
- `agent/verify-inductives-cleanup`: removal of the shape model `Theory/Typing/ShapeModel/`
  from the proof, using `WF.headSeparationModel` of the observation model for the separation
  half, and deletion of dead modules.
- `agent/verify-inductives-pipeline`: consolidation of the recursor pipeline, retiring
  `Verify/Inductive/Equation/`.
- `agent/verify-inductives-strengthening` (with helper branches `-strengthening-*`): research
  on a choice-free projection-walk corner via a frame-lemma route, following route (b) of
  STRENGTHENING_NOTES.md. Success would delete `hch`; there is no estimate of success.

Left as is:

- 56 `sorry` declarations in Mario's prototypes under `Lean4Lean/Experimental/` (Thierry,
  Thierry2, LogRel, DomainTheory, MoreStepIndexed, Stronger, and the remaining ones in
  SExpr, ParallelReduction, Stratified, StratifiedUntyped), present on `master` with at least
  as many. Of the ten in files this branch touched, two were proved, five are false as stated
  (set-model counterexamples in the chronicle) and three need strengthening for the prototype
  calculus. Closing them means rewriting the prototypes.
- Declarative strengthening with canonical `Eq` remains an open research problem; the
  countermodel `Theory/Typing/Countermodel/` without canonical `Eq` is parked.
- Executable hygiene noted in the chronicle: literal cost in `guardedIotaCheck` and the `Std`
  replay time.

## 7. Source map of the final proof

| Question | Entry points |
| --- | --- |
| Final theorem | [Verify/Environment.lean](Lean4Lean/Verify/Environment.lean) (`addDecl.WF`, `addDecl.WF_of_canonicalEq`) |
| Inductive pipeline contract | [Verify/Inductive/Run/](Lean4Lean/Verify/Inductive/Run/) (`FinalResult`, `SemanticSpecification`), [Verify/Inductive/FinalDispatch.lean](Lean4Lean/Verify/Inductive/FinalDispatch.lean) |
| Generative specification | [Theory/Inductive.lean](Lean4Lean/Theory/Inductive.lean) (`VInductDecl.WF`), [Theory/Inductive/](Lean4Lean/Theory/Inductive/) |
| Canonical hypotheses | [Theory/CanonicalEq.lean](Lean4Lean/Theory/CanonicalEq.lean), [Theory/CanonicalChoice.lean](Lean4Lean/Theory/CanonicalChoice.lean), the two `Verify/Canonical*Realization.lean` |
| Head inversion | [Theory/Typing/HeadInversion.lean](Lean4Lean/Theory/Typing/HeadInversion.lean), [Theory/Typing/HeadInjectivity/](Lean4Lean/Theory/Typing/HeadInjectivity/) (`Model/Staged.lean`, `Model/Separation.lean`, `Model/ProjSound.lean`) |
| Uniqueness and inversion | [Theory/Typing/UniqueTyping.lean](Lean4Lean/Theory/Typing/UniqueTyping.lean), [Theory/Typing/Injectivity.lean](Lean4Lean/Theory/Typing/Injectivity.lean) |
| Projection-walk corner | `Theory/Typing/ProjectionCorner*.lean` (`ProjectionCornerChoice.lean`), [Verify/Typing/ProjectionCorner.lean](Lean4Lean/Verify/Typing/ProjectionCorner.lean) |
| Case eliminators | [Verify/Inductive/ConstructorBoundary.lean](Lean4Lean/Verify/Inductive/ConstructorBoundary.lean), [Verify/Inductive/Nested/CaseEliminators.lean](Lean4Lean/Verify/Inductive/Nested/CaseEliminators.lean), `Theory/Inductive/Case*.lean` |
| Scoped caches | [TypeChecker.lean](Lean4Lean/TypeChecker.lean) (`State.leaveScope`) |
| Confluence (outside the cone) | [Theory/Typing/LevelledReduction.lean](Lean4Lean/Theory/Typing/LevelledReduction.lean), [Theory/Typing/WFParams.lean](Lean4Lean/Theory/Typing/WFParams.lean) |
| Executable inductive construction | [Inductive/Add.lean](Lean4Lean/Inductive/Add.lean) |
| Trusted base | [Verify/Axioms.lean](Lean4Lean/Verify/Axioms.lean), [PtrEq.lean](Lean4Lean/PtrEq.lean), [Verify/Expr.lean](Lean4Lean/Verify/Expr.lean), `scripts/inductive-audit-inventory.json` |

The shape model `Theory/Typing/ShapeModel/` is still in the cone at the time of writing and is
being removed (section 6); do not build on it.

## 8. Documentation index

[docs/inductives/README.md](docs/inductives/README.md) lists every file. Current rationale:

- [GOAL.md](docs/inductives/GOAL.md): the standing goal and its amendments.
- [PHASE1_NOTES.md](docs/inductives/PHASE1_NOTES.md): shape model design, decisions D1 to D17
  (the shape model is being removed, the decisions on the specification still stand).
- [PHASE1B_NOTES.md](docs/inductives/PHASE1B_NOTES.md): the observation model, current.
- [E1_INDUCTIVE_DESIGN.md](docs/inductives/E1_INDUCTIVE_DESIGN.md): scoped caches on the
  inductive side, corner discharge, spec corrections (section 5.4).
- [CacheScopeExperiment.lean](docs/inductives/CacheScopeExperiment.lean): why caches must be
  scoped.
- [CORNER_ASTRA_REVIEW.md](docs/inductives/CORNER_ASTRA_REVIEW.md): review of a choice-free
  corner.
- [STRENGTHENING.md](docs/inductives/STRENGTHENING.md): countermodel to strengthening without
  canonical `Eq`.
- [STRENGTHENING_NOTES.md](docs/inductives/STRENGTHENING_NOTES.md): strengthening with
  canonical `Eq`, still the reference for the active research branch.

History (superseded routes, reviews, obstruction certificates, the chronicle):
[docs/inductives/history/](docs/inductives/history/).
