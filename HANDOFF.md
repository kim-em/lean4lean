# Inductive verification: status, evidence, and remaining work

Current account, 2026-10-05, branch `agent/verify-inductives`.
This is the single maintained handoff. Update it in place. The source and the
checked theorem types take precedence over this account.

## Standing goal (2026-10-06)

`docs/inductives/GOAL.md` holds the `/goal` statement. Kim's instruction: do
not stop to ask questions; get the entire thing done; follow Mario's plan
(the shape logical relation of `Experimental/ShapeLogRel*`). Decisions taken
under that instruction on 2026-10-06: the canonical-`Eq` formulation (former
E3) is merged into this branch as the mainline (`addDecl.WF_of_canonicalEq`);
E1 (scoped caches) is parked at 14d38a5 and will not be resumed; the
countermodel is parked at its conditional theorem; the Experimental CI
failure is to be fixed properly as part of porting Mario's prototype. Open
proofs: `headInversion`, `strengthening_of_canonicalEq`, `FullStep.strip`.

Work in flight (2026-10-06, all unbudgeted, each in its own worktree under
`~/worktrees/lean4lean/`):
- `lean4lean-cr`, branch `agent/verify-inductives-cr`: **`FullStep.strip`,
  `FullReduction.church_rosser`, `IsDefEq.full_church_rosser` PROVED
  (88430392, pushed)** by decreasing diagrams over a four-level split of
  `FullStep` (0 normal equality without eta, 1 parallel reduction, 2 parallel
  prefix/projection computation, 3 parallel eta expansion;
  `Theory/Typing/LevelledReduction.lean`); `funEta` stays unrestricted
  because `NormalEqN.beta_aux` needs head eta. Caveat being fixed: the
  development is parametric in `class Params` (seven new fields) and
  `class FullEquationCoverage`, which have no instance; the agent is now
  constructing both. **Finding (strengthening agent): `FullEquationCoverage`
  is FALSE for arbitrary WF environments**, refuted by the formalised
  countermodel `envCM`: native iota of a large-eliminating Prop family is
  excluded from `ParRed` (source level 0), its only computation is the
  native delta rule, whose `NativePrefixReplay` needs `captures_typed`, and
  the `Eq`-free proof-field selectors are ill-typed at generic indices
  whenever a data slot's generic index type differs from the field type; so
  the singleton equation cannot be joined and confluence of `VEnv.IsDefEq`
  fails without canonical `Eq` (consistent with the countermodel). Decision:
  the unconditional theorem is `VEnv.WF.church_rosser (henv) (heq :
  env.HasCanonicalEq)`, with `NativePrefixProgram`'s proof-field selectors
  replaced by `Eq`-cast extraction terms (built by the strengthening agent's
  singleton-eta work; the two agents coordinate directly). **Merged into the mainline (71addb9b..277edf4d,
  pushed):** the one strengthening-dependent lemma underneath confluence
  (`VProjectionInfo.field_typing_of_ctorApp`, via the false
  `VExpr.WF.of_occurs`) was replaced by the E1 branch's strengthening-free
  proof (`of_occurs_lift`, `field_typing_aux`; port of ceb04ec); the
  confluence closure references neither `Strengthening` nor the conjecture.
  Mainline open proofs: exactly `headInversion` and
  `strengthening_of_canonicalEq`; full build, tests, both replays and the
  audit pass. Not ported from E1: `VIotaRuleShape.rec_doms`/`ctor_doms`
  (needs a new nested-restoration proof at `Restoration.restored_iota_shape`)
  and the projection-walk substitution (drags in the corner machinery); so
  `args_typing`/`iota`/`iota_body` still take `hs`. Patch saved at
  `/tmp/l4l-e1b-partial-port.patch` (volatile).
  **Spec correction decided (2026-10-06):** `Instance.Admissible`/`Compiles`
  constrained a recursor's target universe only by `target_wf`, so the
  specification admitted recursors Lean never produces (a large-eliminating
  singleton whose only recursor has motive universe `succ u`), under which
  proof fields cannot be extracted at all (no elimination into Prop, no
  cumulativity), `FullEquationCoverage` fails, and strengthening with
  canonical `Eq` is in doubt. The target universe is now required to be
  either `≈ zero` or a universe parameter not occurring in the declaration's
  levels, exactly the shape `getElimLevel` produces; realizability is
  preserved (CompletedElimination.lean / ConsumedAdmissible.lean instantiate
  the target from it). This corrects the specification to Lean's
  constructions; it weakens no theorem. The strengthening agent implements
  it; the confluence instance relies on it. **Confluence instance proved
  (cr branch 0d0c2531, `Theory/Typing/WFParams.lean`):** `WF.church_rosser
  (henv) (heq : HasCanonicalEq) (hcoh : EliminatorsCoherent) (hΓ) (H)`,
  joinability under `FullReduction` up to `NormalEq`, with the concrete
  `Params` instance `WF.params` built from the canonical registry
  (definition unfoldings, quotient rule when declared, native iota rules),
  every field proved; coverage from `WF.equationCoverage` +
  `WF.singletonCoverage` (`NativeSingletonProgram`/`NativeSingletonCoverage`,
  needing `heq`); only sorry dependency `headInversion`.
  `EliminatorsCoherent` was needed because `VEnv.WF` let a structure's
  projections and an eliminator schema come from different declarations
  (unit-like equality then breaks confluence); **decision (2026-10-07): make
  coherence part of `inductEliminators`** (spec correction; no pipeline
  producer registers schemas), so the theorem takes only `henv`, `heq`.
  Note: `NativeIotaSoundness.lean` makes Theory import Verify for the first
  time (no cycle; follow-up to relocate). **Landed on the mainline
  (fast-forward to 4ca9f41d, pushed):** `WF.church_rosser (henv) (heq)` with
  no coherence hypothesis: `VInductDecl.ProjectionsCoherent` is a fourth
  conjunct of `inductEliminators`'s premise (proved by
  `Certified.register_after_constructors` from freshness; a new premise of
  `CheckingEnv.Valid.registerCases`), and `WF.eliminatorsCoherent` by
  induction on `WF'` (Theory/Typing/EliminatorCoherenceOfWF.lean). Full
  build (733 jobs), tests, both replays and the audit pass; three commits
  inherited from the base branch still carry an Opus trailer (to normalise
  there). **Done (base branch to
  aac10d3c; mainline merged cc06211d as ec8b9270):** `Instance.FreeTarget`,
  the singleton branch of `Admissible.elimination`, realization
  `recursorDeclarationAbstractLevels_freeTarget`; abstract singleton eta
  (`SingletonExtraction.lean`: `value_typed`, `occ_typed`, `singleton_eta`,
  `occ_subst`); the native bridge `NativeRecursorData.propElim_wf` (a
  registered native recursor with a large target, at an occurrence whose
  source sort is Prop, gives `PropElim.WF`; the eliminator is the recursor
  with its free target set to 0, motive instantiated at
  `fun _ => ∀ p : Prop, p → p`), plus `occ_instL`, `occ_levels`,
  closedness lemmas without `HasCanonicalEq`, handed to the confluence
  integration. Only sorry dependency: `headInversion`. Next for (b): the
  certificate calculus (rule-level design first, Astra review of admissible
  transitivity); honest size estimate comparable to the confluence stack
  (about 29k lines).
  **Obstacle (base branch after aac10d3c; `STRENGTHENING_NOTES.md` "Part 3
  status", `STRENGTHENING_ASTRA_REVIEW2.md`, `REVIEW3.md`):** route (b)
  rests on a conversion-elimination theorem (admissible transitivity for a
  certified, transitivity-free calculus whose certificates mention only
  subterms, synthesized types and reducts of their endpoints) for which no
  proof organisation is known, already for the Π/λ/app/β/η/proof-irrelevance
  fragment: every organisation is circular (transitivity needs normal
  equality transported along β; that needs substitution through the typing
  evidence of proof-irrelevance and η leaves; substitution for synthesized
  typing needs conversion composition at variables on outputs of earlier
  calls, whose size grows) and no measure decreases; Siles–Herbelin does
  not transfer; the theory does not normalize; Astra knows no proof and no
  impossibility argument. **Decision (2026-10-06): pursue both remaining
  routes.** (1) The strengthening agent continues with a minimal Lean
  prototype of the certified core calculus hunting a termination
  organisation, documenting each failed measure for Mario. (2) E1 is
  UN-PARKED: its scoped-cache executable needs strengthening at exactly one
  restricted site (`ProjectionWalkCorner`); the E1 agent merges the mainline,
  finishes the last narrow-scope site, deletes `CheckerSubContextLocality`,
  and reports the residual conjecture set; the strengthening agent assesses
  whether `ProjectionWalkCorner` is provable with singleton eta. Whichever
  route reaches a complete proof first wins; GOAL.md's "E1 parked" clause is
  superseded by this entry.
  **`ProjectionWalkCorner` assessment (strengthening agent,
  `STRENGTHENING_NOTES.md` "Assessment: the restricted projection-walk
  corner"):** provable by SUBSTITUTION, no certificates, if the environment
  contains canonical `Nonempty` and `Classical.choice` (both in
  `Init.Prelude`): eliminate the structure `S` into Prop with motive
  `fun x => Nonempty D[x]` to get `hne : Nonempty D`, substitute
  `d := Classical.choice hne`; since the body does not mention `d` the
  substitution yields the smaller-context translation. Without choice the
  restriction gives no measure (same conversion-elimination problem).
  **Decision (2026-10-06): accept `VEnv.HasCanonicalChoice` as a further
  hypothesis of the final theorem** (same character as `HasCanonicalEq`,
  prelude-installed, monotone), on the E1 route; the strengthening agent
  implements `projectionWalkCorner_of_choice` (about 1k to 2k lines) and its
  realizability, then returns to the prototype. If E1 completes, the final
  theorem's hypotheses are `ves.WF env`, canonical `Eq`, canonical
  `Nonempty`/`choice`, `decl.IsModelled`, with `headInversion` the only
  remaining conjecture; GOAL.md item (3) is to be updated accordingly when
  that lands.
  Corner implementation status: `VEnv.HasCanonicalChoice`
  (Theory/CanonicalChoice.lean, without `Nonempty.rec`, with `mono`) and
  `TrExprS.weakBV_inv₁_inhabited` (Verify/Typing/InhabitedStrengthening.lean:
  strengthening across one binder whose type is inhabited by a typed term
  below, by substitution) are built on the base branch. The corner theorem
  needs, beyond `HasCanonicalChoice`: a registered native recursor of `S`
  (without it the statement is false: `inductProjections` registers
  projections with no eliminator), `info.nindices = 0` (true at the call site:
  projection inference accepts only structure-like families), and
  temporarily `families.size = 1` (to be generalized to mutual/nested
  structures via the restored recursor with constant motives). E1 discharges
  the recursor premise at every call site, including the transient
  types+constructors window (generated terms only; a block-family
  projection could arise there only via structure eta in `isDefEq`).
  **Theory-level corner proved (base branch c1e4b892):** `VEnv.corner_inhabit`
  (Theory/Typing/ProjectionCornerElim.lean): under WF, `HasCanonicalChoice`,
  the walk's data (projection info, levels, the instantiated constructor
  telescope reaching `forallE D body'`, `IsType D`, the failed guard,
  `nindices = 0`) and the bundle `StructurePropRecursor env U S info ls`
  (a registered native recursor of `S` with constructor `info.ctorName`,
  matching parameter count and arity, an instantiation `ls0` of its universes
  with target zero and levels corresponding to `ls`; temporarily
  `families.size = 1`), there is `d : D` in Δ (recursor applied with motive
  `fun _ => Nonempty X`, minor `Nonempty.intro field_j`, then
  `Classical.choice`). Sorry dependency only through unique typing
  (`headInversion`). Next: Verify-level `projectionWalkCorner_of_choice`,
  then the generalization to several families; E1 supplies the bundle at
  the call sites from a proved pipeline invariant.
  **E1 status (c54b258d, pushed):** mainline merged; the last narrow-scope
  site closed (`recursorTelescope_hypothesisUnlift` from the producer's
  checker contexts); the nested `ctor_doms` proof made strengthening-free
  (`CompilationData.restoredConstructorFieldDomains`); the unused
  strengthening-dependent Verify lemmas deleted; `CheckerSubContextLocality`
  gone. Top-level theorem on E1: `addDecl.WF_of_canonicalEq (wf) (hcorner :
  ProjectionWalkCorner) (heq) (decl) (hdecl)`; the cone (40182 constants)
  contains no `Strengthening` and no `weakN_iff`-family lemma; the only
  sorry in it is `headInversion`. Remaining on E1: discharge `hcorner`
  (proved registry invariant + the transient-window `ProjsOK` extension +
  the base branch's Verify-level corner under `HasCanonicalChoice`).
  **Decision (2026-10-07): E1 is the leading route and becomes the mainline
  once `hcorner` is discharged**; the declarative-strengthening route (b)
  is an open research problem and continues only as a documented prototype.
  The final theorem will then assume canonical `Eq` and canonical
  `Nonempty`/`Classical.choice`, with `headInversion` the sole conjecture;
  GOAL.md item (3) will be updated when E1 lands.
  **E1 at 94283b09:** `strengthening_of_canonicalEq` deleted (inventory
  lists only `headInversion`); `VEnv.Strengthening` kept as a definition
  used by the countermodel. Corner discharge design (`E1_INDUCTIVE_DESIGN.md`
  §5.1): the transient window is easy except `checkRecursorTypes`, whose
  full `checkType` could let `tryEtaStructCore` build `.proj S i t` for a
  block structure; **decision (2026-10-07): option (A), register the
  abstract case eliminator at the constructor boundary via
  `CheckingEnv.Valid.registerCases`** (executable unchanged; every
  registered structure has a registered eliminator by construction, inside
  and outside the window; the corner is inhabited through
  `.elim key owner (.zero :: levels)` with `schema.genericType`, which also
  covers mutual and nested blocks, so the native-bundle generalization is
  dropped). The strengthening agent is redirected to the head-inversion
  effort; route (b)'s prototype is parked after a write-up for Mario.
  **E1 at 89475ed3 (pushed):** mainline (78 commits) and base (corner files)
  merged; `corner_inhabit_sig` (corner for any closed term typed at an
  ordinary signature's recursor type). Option (A) as stated is circular:
  `registerCases` needs a full `CompilationData`, parts of which
  (`recursiveTypesWF`, recursors, equations, elimination level) exist only
  after the window run that needs the corner. **Decision (2026-10-07):
  option (C): weaken `WF'.inductEliminators` to a case-only certificate**
  (formation, model, correspondence, restoration scoping, names, projection
  names, coherence), since the eliminator rules depend only on the schema
  data; spec correction, weakens no theorem; consumers (`eliminator_origin`,
  EliminatorAvoidance, coherence, the confluence `Params` fields reaching
  constructor shapes) adapted on E1; then (A) proceeds with the case-only
  certificate plus an `elimDF` typability lemma for the case type.
  **Mainline fast-forwarded to base 9cc2be01 (pushed):** realizability of
  `HasCanonicalChoice` (Verify/Inductive/ChoiceCanonicalForms.lean,
  Verify/CanonicalChoiceRealization.lean `VEnvs.WF.hasCanonicalChoice`,
  Tests/CanonicalChoice.lean), and Theory no longer imports Verify (the 41
  declarations `NativeIotaSoundness` used moved into
  Theory/Inductive/NativeIotaRestoration.lean with proofs unchanged). Full
  build (745 jobs) and tests (346) green.
- `lean4lean-hi`, branch `agent/verify-inductives-headinv`: **Phase 1a
  COMPLETE (84bf90d3; being merged into the mainline):** `lake build
  Lean4Lean.Experimental` passes (NormalEq, ParallelReduction, Stratified,
  StratifiedUntyped ported; two false-once-iota-fires theorems take
  `VEnv.NoInductiveRules`); a new sound model `Theory/Typing/ShapeModel/`
  over the real `VExpr`, sound for every rule in every WF environment;
  `VEnv.WF.headSeparation` PROVED (fields `sort_sort`, `sort_forallE`,
  `sort_rigid`, `forallE_rigid`, `rigid_heads`); `headInversion` is now
  assembled from it and the single remaining conjecture
  `VEnv.WF.headInjectivity` (`forallE_forallE`, `rigid_args`, `former_args`,
  `proj_fieldType`; statements in HeadInversionDefs.lean). Spec correction
  D10: `inductEliminators` gains `schema.StructCompat env` (a registered
  schema has exactly the registered constructor of every registered
  structure among its families), since otherwise unit-like plus a foreign
  schema derived `Prop ≡ (Prop → Prop)` and head inversion was false.
  Prototype gaps isolated (`Params.PatternRegistry`, `LR.ConstAdequate`,
  `Params.TypedEnv`); decisions D1 to D14 in PHASE1_NOTES.md. Phase 1a: port
  Mario's Experimental prototype to this branch's `VExpr` (fixing the
  Experimental CI build), a sound shape model for the full calculus, the
  separation half of `HeadInversion`; split the conjecture so only
  `headInjectivity` remains.
- `lean4lean-e3` (re-pointed), branch `agent/verify-inductives-headinj`:
  **Milestone (2026-10-07, branch agent/verify-inductives-headinj-proj
  e8e8e90d, merging into headinj): all eight `HeadInversion` fields are
  proved in the projection-free scope** (`ProjFree`): the Phase 1b
  injectivity core plus `WF.headSeparation_of_sound`/`headSeparationModel`
  (HeadInjectivity/Model/Separation.lean) from the glued model; remaining is
  stage C (projections: `projOrigin`, `ctorTypeSound`, `ctorTypePiSD` done;
  the four projection soundness cases in progress), after which `ProjFree`
  drops and `headInversion` is proved. Phase 1b: the injectivity half (`forallE_forallE`, argument part of
  `rigid_rigid`, `former_args`, `proj_fieldType`); design candidates:
  cast-pushing inside the relation, neutral eliminators, type-level relation
  with singleton eta. Astra design review requested.
- `lean4lean-base`, branch `agent/verify-inductives-base`: obligation (b):
  falsification study of strengthening with canonical `Eq`, singleton eta,
  conversion certificates. **Study verdict (d4beac49): no refutation found;
  `strengthening_of_canonicalEq` kept unchanged.** Every attack reduces to
  (1) singleton eta (data fields read from literal index slots, proof fields
  extracted from the major by the family's recursor with casts along
  type-level `Eq`; no `HEq` needed), (2) quotient eta at Prop, or (3)
  conversion checks between binder-free terms handled recursively. Removed
  data binders never matter (the major of any redex is a binder-free subterm
  present in the smaller context). `Eq` is genuinely needed only when a data
  slot's generic index type differs from the field type (the countermodel).
  Kernel-checked evidence: `docs/inductives/StrengtheningFalsification.lean`;
  write-up `docs/inductives/STRENGTHENING_NOTES.md` (on that branch).
  Continuing with singleton eta and the certificate calculus.
  **Part 3 assessment (interim; `STRENGTHENING_NOTES.md` §3,
  `STRENGTHENING_ASTRA_REVIEW.md` on that branch):** confluence alone does
  not give strengthening: the canonical-step witness between binder-free
  terms has side conditions that are new larger-context judgements
  (K/singleton alignment checks, eta-domain agreement, binder-domain
  premises) with no well-founded measure below the original (no
  normalization; size not preserved by substitution). The irreducible core
  is a certificate calculus with transitivity-admissibility redone with
  certificate premises (Siles–Herbelin style), estimated 20k to 40k lines.
  Astra agrees, knows no published strengthening theorem for this
  combination, and suggests a checker locality theorem for the cache
  consumers instead; but the cache-scope experiment shows the unscoped
  executable is not local, so that route needs E1's executable change plus
  the inductive-side locality theorem (9k to 16k lines), which was parked by
  decision. Decision (2026-10-06): continue route (b) as planned (singleton
  eta, then the certificate calculus); revisit only if the pilot shows it is
  unworkable. **Pilot (paper, `STRENGTHENING_NOTES.md` §3.3):** strengthening
  a larger-context witness (`FullReduction` + `NormalEqN`) by induction on
  the index closes proof irrelevance, refl/sort/const/elim, forallE levels,
  common-mode lam/eta, head-forced spines, projections and eta at
  application heads. Failing pieces: own-mode lam/forallE domain premises
  (fixable by a "deep" `NormalEqN` with index-counted domain premises), and
  the irreducible core: reduction steps whose check is a conversion not
  forced by typing (`DeltaPar.delta`/`quotDelta` with K/singleton alignment
  checks; canonical choice of eta domains / struct-eta params). Design:
  delta/quotDelta steps carry an alignment WITNESS instead of an `IsDefEq`
  check; completeness reworks only the delta-level parts of
  `LevelledReduction` (about 63 lemmas) and the deep `NormalEqN`, not the
  whole confluence development. Far smaller than the 20k to 40k estimate.
  **Correction:** the K/singleton alignment check arises in the strip where a
  proof-irrelevance leaf `h ≡ₚ Eq.refl a` meets iota on the refl side, and
  the check `a ≡ b` comes from injectivity applied to the type agreement of
  the leaf (`Eq a b` vs `Eq a a`); witnessing it requires proof-irrelevance
  leaves to carry witnessed agreement of their independently synthesized
  types, hence witnessed synthesized-type agreements for typings: the full
  synthesizing certificate calculus, with transitivity admissibility (strip)
  restated as induction on certificate size. The deep `NormalEqN` and the
  §3.3 strengthening analysis stand. Next: singleton eta formally, then the
  certificate-calculus design doc with the plan for which mainline lemmas
  carry over.

## Intended result

Finish the executable Lean4Lean inductive checker's refinement of an
independent generative specification (Mario's intended treatment of ordinary,
primitive, mutual, higher-order, indexed, and nested inductives), including
dependent projections, structure eta, exact recursor metadata and equations,
with complete proofs. The specification determines artifacts from
declarations; validation must not assume correctness of its own artifact.

## What was established this session (decisive results)

1. **The final theorem and its exact dependencies.** The checker contract is
   `Lean4Lean.addDecl.WF` (`Verify/Environment.lean`): a successful
   `addDecl env (.inductDecl ..)` yields `VEnvs` that are `WF` for the output
   environment, extend the input models, and (through
   `InductiveFinalResult` / `InductiveSpecificationResult`) a `VInductDecl`
   with `TrInductDeclCore` and `VEnv.AddInduct`. An opaque-body dependency
   audit (`scripts/InductiveAudit.lean` mechanism, root `addDecl.WF`) finds
   exactly **10 `sorry` sources**:
   - base metatheory (6): `IsDefEqU.sort_inv`, `forallE_inv_stratified`,
     `sort_forallE_inv`, `rigidApp_inv`, `fieldType_inv_stratified`
     (`Theory/Typing/Injectivity.lean`) and `IsDefEqU.weakN_iff`
     (`Theory/Typing/UniqueTyping.lean`);
   - inductive-specific (4): `VConstructorShape.saturated_of_hasType`
     (`Theory/Typing/RecursorLemmas.lean`),
     `CompletedRecursorConstruction.canonicalConsumedGeneration`
     (`Verify/Inductive/Recursor/CanonicalConstruction.lean`),
     `CompletedRecursorPhasesResult.canonicalCompletedRuleTranslation`
     (`Verify/Inductive/CompletedEquationAssembly.lean`),
     `NestedValidatedRunResult.assemblyNative`
     (`Verify/Inductive/Nested/AssemblyProviderEvidence.lean`).
   `finalValidOfStaged` and the Church-Rosser items (`NormalEq.headParallel`,
   `fullStep`, `FullStep.strip`) are **not** on the path of `addDecl.WF`; they
   matter only to the audit roots `full_church_rosser` and `headParallel`.

2. **The Anchored foundation is disconnected.** None of the 1834
   `Theory/Typing/Anchored*.lean` files (295k lines, all untracked until the
   WIP snapshot) are in the import closure of `Verify.Environment`,
   `FinalDispatch`, `Injectivity`, or the tests. Its targets are the six base
   sorries above; five are open upstream too (`origin/master`, Aug 2026, still
   has `sort_inv`, `forallE_inv`, `weakN_iff`, `TrProj`, `VInductDecl.WF` as
   sorries and several `Experimental/*` attempts), and one is false (next
   item). **Deleted** (with Kim's approval): the 1834 Anchored files, their
   11 sole dependents (`Theory/Typing/{EquationHeaderDerivation,FieldAdequacy,
   NativeDeclaredFieldOrigin,NativeExtensionalTerminal,NativeInitialFieldOccurrences,
   NativeInitialSelection,NativeReplayEligibilitySoundness,NativeResultBridge,
   NativeTerminalSoundness,NativeZeroFieldProgram,TypedWorldProofPrefix}.lean`),
   and two stale unused modules that no longer compiled
   (`Theory/Typing/RigidHeadStrengthening.lean`, `Verify/Typing/ProjectionInverse.lean`).
   Some `docs/inductives/*.lean` witness files import deleted modules and are
   now historical text only. `lake build` (default targets) passes.

3. **`IsDefEqU.weakN_iff` has a mathematical countermodel.** The groupoid
   construction in [STRENGTHENING.md](docs/inductives/STRENGTHENING.md)
   (two singleton-eliminating indexed `Prop` families over a non-discrete
   index type) gives `Γ, q : P v ⊢ SI ≡ SJ` by proof irrelevance while
   separating `SI` and `SJ` in the smaller context. A second opinion (Codex,
   this session) found no defect in the construction but notes the
   certification boundary is open: the checked files establish the
   larger-context derivation and finite transport calculations, not a
   soundness proof for every `VEnv.IsDefEq` rule of a certified `VEnv.WF`
   environment, nor nonderivability of the existential `IsDefEqU`. Scope:
   this refutes unrestricted *equality* reflection; fixed-type typing
   reflection follows the same way; existential `VExpr.WF` strengthening is
   not refuted by it. Adding Lean's `Eq` lets the smaller context extract
   `P v` and so defeats this particular model; no general repair theorem is
   established either way. `weakN_iff` has 63 uses in 24 live files
   (including upstream's `OnCtx.weakN_inv`, `HasType.weakN_iff`,
   `IsType.weakN_iff`, `VLocalDecl.weakN_iff`, `LevelEquiv`,
   `ConditionallyTyped`); it is a base-theory issue shared with upstream.

4. **Two executable regressions were found and fixed** (upstream on the same
   toolchain `v4.33.0-rc2` replays `Init`, `Std`, `Lean.Data`,
   `Lean.Meta.Basic` with no problems except 25/6 "constant has already been
   declared" artifacts shared with this branch):
   - Higher-order recursive fields produced **wrong iota rules**: the
     recursive-call template in `Inductive/Add.lean` (`loopUBlueprints`,
     `mkRecRules.loopU`) placed the recursor placeholder as `.bvar 0` inside
     the field's own lambda binders, where `mkLambda` captured it. `Acc.rec`'s
     rule became `intro x h fun y a => a y (h y a)`; `WellFounded.fixF_eq`
     failed to check and `Lean.Order.iterates.rec` mismatched Lean's.
     Lean's `Expr.abstract` does not shift loose bound variables, so the
     placeholder must be `.bvar xs.size` (now in both sites). Verified by
     regenerating `Acc`, `Lean.Order.iterates`, and a dozen nested inductives
     through `Lean4Lean.addDecl` and comparing recursors (type, metadata,
     rules) against Lean's: identical. The template design is retained
     because first-pass field fvar ids can collide with later minor fvars, so
     a direct construction captures minors (checked: it produced
     `Acc.rec … a y (h y a)`).
   - The nested restoration guard check ran out of fuel: `guardedIotaCheck`
     expands literals (`Nat.succ` chains, string characters) but its fuel was
     `approxDepth + rawBVarBound + 1` with `approxDepth` capped at 255.
     `Lean.Parser.Tactic.MCasesPat` (a `TSyntax` field) was rejected.
     `validateRestoredRecursorRules.guardFuel` now bounds the traversal
     structurally including literal expansion. Note: the guard still walks
     `Nat.succ^n` for a literal `n` in a nested constructor type, which is a
     latent cost problem (a literal of 10^9 would hang); `.lit _ => true`
     plus a freshness premise in `guardedIotaCheck_sound` is the right fix.
   After the fixes, `lean4lean Init` and `lean4lean Std` match upstream's
   baseline exactly. `Std` replay takes ~1m20s here against ~28s upstream:
   a performance regression worth profiling.

5. **The trusted base contained a false implementation axiom.** Both upstream
   and this branch had `axiom Expr.abstract_eq : e.abstract ⟨xs.map .fvar⟩ =
   e.abstractList xs`, where the model `abstract1` **shifts** loose bound
   variables (`bvar i ↦ bvar (i+1)` at or above the cutoff). Lean's real
   `abstract` leaves them unchanged: `(Expr.bvar 0).abstract #[.fvar x]`
   evaluates to `bvar 0` while the model gives `bvar 1` (also false for
   duplicate lists). This is exactly why the recursive-call proofs "verified"
   the buggy executable: the model and the bug agreed. Now:
   - `Verify/Axioms.lean` defines `Expr.abstractN` (one-pass, last occurrence
     wins, loose bvars unshifted; exact mirror of C++ `abstract`), the axiom
     `Expr.abstractN_eq`, and the derived theorem `Expr.abstract_eq_of_closed
     (hnd : xs.Nodup) (h : e.looseBVarRange' = 0)`, plus
     `abstractN_eq_abstractList`, `abstractN_cons`, `abstractN_append_singleton`,
     `abstractN_nil`, `abstractN_hasLooseBVar_zero`, `abstractN_lower`,
     `abstractN_singleton`, `lastRevIdx?` lemmas.
   - The false statement is **gone**: `Expr.abstract_eq_legacy`,
     `abstractN_eq_abstractList_legacy`, and the sequential bridge
     `LocalContext.mkBinding_eq` were deleted (2026-10-05). Every former
     consumer now either runs on the exact model (`mkBinding_eqN`,
     `abstractN` telescopes, `reopenFVarsAt_eq_reopenParams` with a
     `looseBVarRange' = 0` premise, `NestedReplacementReopens.restoreNode`
     stated at arbitrary binder depth) or converts to the sequential model
     through `abstractN_eq_abstractList_of_closed` with an honest closedness
     fact. Closedness is supplied by translations (`TrExprS.closed` plus
     `MLCtx.noBV`), by the kernel's own nested-parameter check
     (`NestedParameterScan.closed`, recorded as
     `GeneratedFamilyWitness.argsClosed`), by `LctxClosed` of semantic
     contexts (`BoundFVarDeclarationAt.closed`), or by new fields/hypotheses:
     `ConstructorRestorationBodyInverse.sourceBVarClosed`,
     `GeneratedRecursorRestorationTelescopeAlignment.oldBVarClosed`,
     `hsourceBVar : Closed source.type` on the constructor restoration chain,
     and `hparamsSize : params.size = nparams` where the honest cancellation
     law needs the parameter count. `--require-complete` no longer reports it.
   - `Verify/LocalContext.lean` keeps two models: the sequential
     `mkBindingList` (now only a specification-side device; its bridge to
     `mkBinding` is `mkBinding_eq'`, which requires `Closed b`, nodup, and
     `DeclsClosed`) and the exact `mkBindingListN` with the true bridge
     `mkBinding_eqN` and the full `cons`/`fold` lemma family. The recursive-call verification
     (`BoundGeneratedRecursiveCall.body/abstractedRecursor/abstractedMajor`,
     `lambdaTelescope`, `appliedFieldLambdaTelescope`,
     `mkLambda_fvars_lambdaTelescopeN`, `mkLambda_fvars_avoidingLambdaTelescopeN`,
     `mkBindingListN_*Telescope`) runs on the exact model and the placeholder
     `.bvar args.size`; the model-internal fingerprints (`replayTrace`,
     `outerAbstracted*`, first-pass `Origins`, equation traces) stay on the
     sequential model and meet the exact model through
     `abstractN_eq_abstractList` with nodup/closedness (e.g.
     `outerAbstractedMotiveApp_eq`, `Equation/Canonical.lean`).
   - Closedness is now a hypothesis of `MLCtx.WF.mkForall_eq/mkLambda_eq`
     (`_he : Closed e`, unused by the sequential proof but required by the
     exact bridge); callers supply it from `TrExprS.closed` with
     `MLCtx.noBV` / `FVarNarrowSources.noBV` / `FVarNarrowCore.noBV`.
     `Closed.instantiate1`, `Closed.consumeTypeAnnotationsVerified`,
     `Closed.consumeForallTypes`, `AvoidsConsts.abstractN`,
     `SameLambdaPrefix.abstractN`, `ForallBinderAt.abstractN`,
     `FVarsIn.abstractN_of` were added.

6. **The source-facing specification needs a hypothesis the executable does
   not check.** Lowering (`ElimNestedInductive.lowerConstructor`, mirroring
   C++ `elim_nested_inductive`) opens the parameter telescope of every source
   constructor type and re-closes it with `mkForall`. Because `instantiate`
   lowers loose bound variables while `abstract` does not shift them, a
   constructor type with a loose bound variable under its parameter binders
   is silently *repaired* (`∀ α, (x : bvar 1) → T α` becomes
   `∀ α, (x : α) → T α`), and the kernel then checks and stores the repaired
   type. So `result.types = sourceTypes` (ordinary case) and "restored
   constructor ≡ source constructor" (nested case) are false for such
   inputs, and the former proofs of them rested on the false bridge. The
   honest statements carry `SourceBVarClosed types` (every inductive type and
   constructor type has no loose bound variables), threaded as
   `HsourcesB` into `ordinary_types_eq_source`,
   `ordinaryFinalSpecificationModelWF`, `inductiveFinalResultWF`, and
   `addInductiveDeclaration.finalResultWF`. The checker contract
   `addDecl.WF` and `finalPreservesWF` are **unconditional**: they go
   through the well-formedness halves (`ordinaryFinalModelWF`,
   `nestedInductiveFinalResultWF.modelExtension`, primitive) only. The
   executable matches the C++ kernel on such inputs (no new rejection); the
   nested path needed no new top-level hypothesis because every source-facing
   fact there comes with a translation of the source.

7. **Translations are syntactically unique, and the junction must invert the
   executable's type check.** `TrProj` has one constructor, so
   `TrExprS.uniqueS` (`Recursor/CanonicalMinorFields.lean`) gives
   `TrExprS Δ e e₁ → TrExprS Δ e e₂ → e₁ = e₂` with no `IsUnique` side
   condition; every "which translation was chosen" question in the junction
   disappears. The minor premises mention motives, and the first pass only
   translates them in free-variable contexts that interleave indices, majors
   and stale fields between the parameters and the motives; moving such a
   translation into the generator's abstract context `params ++ motives ++
   earlier minors` would need context strengthening, which is the `weakN_iff`
   problem. The only derivation of a closed recursor type available before
   installation is the executable's own `checkRecursorTypes`, so
   `CompletedRecursorConstruction` now retains it (`recursorTypes :
   RecursorTypeTranslations …`; `bindingSemanticWFOfTargets` lets the
   installed targets depend on it). `Recursor/CanonicalRecursorTelescope.lean`
   inverts it into the five binder groups (`recursorTelescope`) and identifies
   the parameter group with the cached parameter telescope and the motive group
   with `Instance.motives` by uniqueness (`recursorTelescope_params`,
   `recursorTelescope_motives`). Each flat minor slot translates the retained
   minor declaration type in its generator context
   (`recursorTelescope_minor`); its field domains are the `insertBinders`
   lift of `H.sourceFields` (`recursorTelescope_minorFields`, by uniqueness
   against `minorFieldsTemplate`); and its residual inverts to the owner's
   motive variable applied to translations of the closed terminal indices and
   to the canonical constructor spine `mkApps (const ctor levels) (vars …)`
   (`minorResidualSource`, `recursorTelescope_minorResidual`); its index
   translations are the lifted `sourceConstructorIndices`
   (`recursorTelescope_minorIndices`: lift the header replay with
   `liftOriginalType`, peel the field telescope, weaken with
   `insertBeforeInner` and `bvLift`, then `uniqueS`); and each hypothesis
   domain translates the retained hypothesis declaration in its generator
   context (`recursorTelescope_hypothesisSlot`) and inverts to a telescope of
   argument domains, the owner's motive variable applied to translations of
   the closed exposed indices, and the recursive field variable applied to
   the canonical argument spine (`hypothesisResidualSource`,
   `recursorTelescope_hypothesisShape`, from the blueprint hypothesis origins
   `RecInfoMinorHypothesisTypeOrigin`). The owner's index and major groups
   are the lifted motive telescope (`recursorTelescope_indicesMajor`), and
   `recursorTarget_eq_of_minors` assembles everything: the checked recursor
   type equals `Instance.recursorType` for any generator instance over the
   consumed families whose minor list equals `T.minors`. So the `types` field
   of the junction is reduced exactly to the minor group, and the minor group
   to item 8: the hypothesis argument domains and exposed indices must be the
   lifts of small-context `Recursive` shapes for `Instance.hypothesis` to
   match. Translation strengthening is available for this:
   `Recursor/ContextRestriction.lean` restricts a lambda-only typechecker
   context to any up-set of its free variables (`MLCtx.restrictUpSetCtx`:
   the result is a well-formed `MLCtx` whose declarations carry the
   strengthened translations, with the `FVLift'` witness; uses
   `TrExprS.weakFV'_inv`, which **does** depend on the false `weakN_iff`
   through `VExpr.WF.weak'_iff` and `HasType.weak'_iff` at
   `Verify/Typing/Lemmas.lean:1316-1354`; an earlier version of this note
   claimed otherwise) and closes such a context into abstract binders
   (`TrExprS.closeAllLams`). The
   remaining program for the minors, independent of item 8's resolution:
   for hypothesis `j` take the semantic call row
   (`RecInfoHypothesisCallSemanticOrigins` → `SemanticBoundGeneratedRecursiveCall`,
   with `current_scope_up : IsFVarUpSet (args ∨ fields ∨ params)`), sharpen
   the up-set to `params ∪ fields.take f ∪ args` (field dependencies lie in
   earlier fields by `VLCtx.WF` plus `fieldParameterUp`; argument scope by
   induction over `RecursorLoopUArgsPrefix` with `whnf.WF`'s `FVarsBelow`),
   restrict the row's context, read the `Recursive` binders off
   `MLCtxForallDomains` of the restricted context and the indices off the
   restricted `exposed_translation`, close with `closeAllLams`, weaken into
   the generator's hypothesis context with `insertBeforeInner`/`bvLift`, and
   identify with `recursorTelescope_hypothesisShape` by `uniqueS` (the two
   passes' telescopes are related through `replayTrace_eq_blueprint`). With
   item 8 resolved by (c), only `Instance.RecursiveTypesWF` for the actual
   instance then remains, by inversion of the retained type check.
   **Done (2026-10-06): per-field rows and the inversion tools.** The
   first-pass producer now retains, from the same executable run, a second
   semantic row per induction hypothesis whose root scope is
   `RecursorFieldPrefixScope`: the parameters and the constructor fields
   strictly before the recursive field (`RecInfoHypothesisCallSemanticOriginsAt`,
   stored as the last conjunct of `RecInfoRuleBlueprintSemanticOriginAt`,
   `SecondPass.lean`; the coarse row is unchanged for the equation layer).
   The field's own declared type is scoped by reading the stored metacontext
   declaration (`Recursor/FieldTypeScope.lean`: the executable's
   `inferType (.fvar fv)` is a local-context lookup, and an all-lambda
   `MLCtx` records the dependencies of a declared type on its own entry;
   `MLCtx.recentTypeScope`, `RecursorRecentBoundFVarArray.fieldTypeScope`),
   so `resultRecursiveDomainOfInferredScope`/`inductionHypothesisTypeOriginOfInferredScope`
   take the inferred type's scope as a hypothesis (the original forms are
   wrappers). The sharpened up-set is `IsFVarUpSet.sharpenPrefix`.
   `recursorTelescope_hypothesisDomains` extends the hypothesis-shape
   inversion with the translation of each binder domain `A[i]` (of the
   literal `i`-th domain of the blueprint telescope, `argDomains`).
   `Recursor/TelescopeUniqueness.lean` closes an all-lambda metacontext entry
   by entry (`MLCtx.lamTypes_telescope`, `lamTypes_find?`), identifies two
   abstract telescopes translating the same sources
   (`TrExprS.telescope_unique`), and pins the universe un-shift
   (`TrExprS.chooseOriginalUniverses_eq`, from `SourceUniverses.lean`'s
   `chooseOriginalUniverses`). `MLCtx.restrictUpSetCtx` now also preserves
   declaration types. Remaining for the minor group: restrict the per-field
   row (`SemanticBoundGeneratedRecursiveCall.restrictToFieldPrefix`,
   `Recursor/RecursiveShapeRow.lean`, in progress), identify its parameter
   and field domains with `parameterDecls` and `sourceFields` by
   `telescope_unique`, weaken the restricted translations into the generator
   context (`insertBeforeInner`) and identify with
   `recursorTelescope_hypothesisDomains`/`_hypothesisShape` by `uniqueS`
   (`replayTrace_eq_blueprint` relates the row to the blueprint origin), then
   un-shift universes and assemble the consumed signature.
   **Universe un-shift (open, 2026-10-06).** The shapes read off the row are
   translations in the recursor universe list `u :: c.lparams` (large
   elimination); the signature needs them in `c.lparams`, with
   `instL (recursorDeclarationAbstractLevels …)` reproducing the checked
   domains. `TrExprS.chooseOriginalUniverses_eq` does this given that the
   source Expr does not mention `u`. The arg domains and exposed indices are
   `whnf` outputs of the field types, which never mention `u`, but the
   checker proves no universe-parameter support for `whnf` (only
   `unfoldDefinition.WF_levelParams` existed; the index telescopes were then
   covered by a runtime check `checkIndexUniverses`, since removed, see
   below). A runtime guard for the argument telescopes is excluded by the
   no-new-rejections rule. Plan (study 2026-10-06, estimate 1.5k to 2.2k
   lines over 7 to 10 files of `Verify/TypeChecker`): add to `VState.WF` and
   `Methods.WF` a hereditary universe-support invariant (results of
   `whnfCore`/`whnf`/`inferType` mention only `Us` when the input and the
   declarations of an up-set containing its free variables do; `isDefEq` only
   threads the state invariant), prove it per method, and bridge to
   `loopUArgs` with the per-field up-set. This also allows removing
   `checkIndexUniverses`. **Done (2026-10-06, merged):** `VContext.UniverseScope`,
   `VContext.LevelsBelow`, `LevelsCache.WF` and the `VState.WF` fields
   `inferTypeI_levels`/`inferTypeC_levels`/`whnfCore_levels`/`whnf_levels`,
   with `Methods.WF` fields `whnfCore_levels`/`whnf_levels`/`inferType_levels`,
   proved for every method (`Verify/TypeChecker/{Basic,Reduce,Recursor,WHNF,
   Projection,InferType}.lean`, `Verify/ExprUniverses.lean`); no pending
   lemmas. The bridge to the recursor pass (`ArgumentUniverses`, the
   hypothesis of `consumedGeneration_of`) is in progress
   (`Recursor/ArgumentUniverses.lean`). **`checkIndexUniverses` removed
   (2026-10-06):** `loopInd1` no longer checks that the index telescope
   mentions only the declaration's universe parameters, matching C++. The
   fact is proved instead: `continueRecursorParameterSemantics` and
   `continueRecursorIndexSynthesisSemantics` (`Recursor/FirstPass.lean`)
   carry `type.levelParamsIn base.lparams` and a universe scope for the narrow
   scope through every `whnf`/`withLocalDecl` step (`whnfInRecursorContext.levelsWF`,
   `UniverseScope.cons`), seeded by the header translation and by
   `ParameterUniverseSupport` (now a hypothesis of
   `mkRecInfos.loopInd1.resultSemantics`), and
   `RecursorRecentBoundFVarArray.indexUniverses` closes the telescope; this
   discharges the `indexUniverses` field of the origin rows. The universe-scope
   lemmas the first pass needs moved from `Recursor/LoopUniverses.lean` to
   `Recursor/UniverseScope.lean`.
   **Assembly (2026-10-06).** `consumedGeneration_of H HU HF : Nonempty
   H.ConsumedGeneration` (`Recursor/ConsumedGenerationAssembly.lean`,
   `CanonicalConstruction.lean`) is proved from `recursorTelescope_hypothesisUnlift`
   (`Recursor/CanonicalRecursiveShape.lean`: each hypothesis binder group is the
   `underFields` lift of small-context translations of explicit blueprint
   sources), the universe un-shift (`TrExprS.unshiftFixed`), `ConsumedModels.lean`
   (`ConsumedSignatureData.models_of_familyTypes`), `ConsumedAdmissible.lean`
   (`consumedInstance_admissible`, with `sourceConstructorIndices_eq_header`),
   `recursorTarget_eq_of_minors`, and `recursiveTypesWF_of_recursorType`.
   `ConsumedGeneration` gained `recursiveTypesWF` and `familyTypesWF`.
   **Closed (2026-10-06):** `canonicalConsumedGeneration :=
   H.consumedGeneration_of H.argumentUniverses`, no remaining hypotheses. The
   per-field semantic rows retain universe support of each call's argument
   telescope and exposed indices (`RecInfoCallBlueprintSemanticOrigin.universes`,
   proved at the producer from the checker's invariant, `Recursor/LoopUniverses.lean`;
   the parameter and constructor-tail support is discharged at the two
   `loopInd2.resultSemantics` call sites, `Run/Formation.lean` and
   `CompletedConstructorReplay.lean`), and `ArgumentUniverses` is stated over
   the producer-retained blueprint calls (an earlier form quantified over
   arbitrary origins and was false). Reachable sorries after this step: the
   ten base obligations of item 1, `canonicalCompletedRuleTranslation`
   (`CompletedEquationAssembly.lean:278`), `assemblyNative`
   (`Nested/AssemblyProviderEvidence.lean:5049`) and
   `RestoredNestedDeclarationsResult.finalValidOfStaged`
   (`Nested/ValidationEnvironmentRegistry.lean:935`).
   Correction of an earlier plan: the junction
   signature cannot be `R.sourceSignature`. Its field types translate the raw
   constructor telescope, while the production minors bind their fields with
   `consumeTypeAnnotationsVerified` domains, and
   `ConsumedGeneration.sourceOrigins` requires `fieldTypes = H.sourceFields`
   (consumed, header universe). The junction signature is a consumed
   signature whose `Models` follows from `sourceSignature_models` through the
   definitional equalities already proved (`sourceConstructorDefEq`).

8. **The recursive-field clause of the specification was restated at the
   instance level (decision taken with Kim, 2026-10-05).** `Models` no longer
   carries `recursiveTypes`; instead `Instance.RecursiveTypesWF g envTypes`
   (`Theory/Inductive/Signature.lean`) demands, for every recursive field,
   the definitional equality of the field type with its `Recursive` shape in
   `Instance.hypothesisContext` (`SignatureData.lean`: parameters, motives,
   earlier minors, all fields, earlier hypotheses), lifted exactly as
   `Instance.hypothesis` lifts the shape. It is required next to
   `Admissible` in `Compiles`, `CompilationRealization`, and (for the nested
   path) `CompilationData.recursiveTypesWF`. Rationale: `InductiveSignature`
   and `Models` are this branch's formalization (upstream has `VInductDecl.WF :=
   sorry`), the generator needs the equality only in that context, and the
   former small-context form (parameters and earlier fields only) was an
   over-specification: production classifies recursive arguments in the
   recursor-construction context and definitional equality does not
   strengthen (next paragraph). The former form implies the new one by
   weakening and universe instantiation; this implication is not yet
   recorded as a lemma. Mario should review the clause with the rest of the
   signature specification. The paragraph below records the obstruction that
   motivated the change.

   **Correction (2026-10-06, decided with Kim after second opinions from an
   Opus agent and from the Astra model through Codex).** The claim that the
   instance-level definitional-equality clause "follows from the retained
   type check by inversion" was wrong: inversion of `IsType [] recursorType`
   yields typing facts only in the context extended by the hypothesis
   binders, and moving a definitional equality with lifted endpoints down to
   `hypothesisContext` is exactly the strengthening that
   `docs/inductives/STRENGTHENING.md` refutes; the first-pass facts need the
   same strengthening from the large stale context; reduction traces are not
   retained by `whnf.WF` and the theory's reduction relations are typed, so a
   trace route would be a new foundation. The clause is therefore restated as
   well-formedness of each generated induction hypothesis in its own context,
   `Instance.RecursiveTypesWF g env := ∀ index j hj, env.IsType g.uvars
   (g.hypothesisContext …) (g.hypothesis …)`, required in `Compiles` and
   `CompilationRealization` at the environment in which the recursors are
   declared (family headers, constructors, and the declaration's projection
   entries, which is `R.context.venv`), since binder peeling keeps the
   environment; it is derived from `IsType [] (g.recursorType owner)` by
   `Theory/Inductive/HypothesisTyping.lean` without new sorries. Planned
   follow-up (option (C)): a small-scope positivity clause in `Models`,
   existential over a source-free telescope and indices with the same target,
   from the header-phase evidence (the old small-context clause existentially);
   its evidence (`uniformNormalFormNarrow` via `restrictTrExpr`) also rests on
   the `weakN_iff` admission, so it is a specification improvement, not a
   repair of strengthening. Both opinions noted that the defeq form in
   `hypothesisContext` would not have pinned the shape well either, because
   later fields in that context may be proofs.

   **Second correction (2026-10-06, decided with Kim after a second Astra
   opinion).** `Models.externalFields` and `Models.recursiveDomains` required,
   for the consumed signature, agreement between the header phase's field
   classification (`checkPositivity`, which records nothing executably) and
   the recursor pass's (`isRecArg`): a field the generator calls external must
   be external for the header too, and the generator's binders must be
   syntactically source-free although the recursor pass never checks binder
   source-freedom. No lemma gives this agreement (it needs `whnf`
   alpha/context locality plus a syntactically retained header telescope, or
   new confluence-class admissions, and confluence alone cannot yield
   syntactic source-freedom). Both clauses are replaced by one
   classification-independent clause `Models.positiveFields`: every field
   type, in its own scope, is definitionally a
   `VInductDecl.UniformFieldNormalForm` at the source universes (source-free,
   or a telescope over source-free domains ending in a fully applied family),
   which is exactly the header evidence (`SignatureFieldModel` now carries
   it). The generator's classification and shapes are constrained only by
   `RecursiveTypesWF`; their fidelity to the C++ classification is validated
   by the recursor oracle tests, not by the specification. Astra's caveat for
   Mario: a future soundness proof for the permitted recursive presentations
   must justify the generated recursive calls (descent along the positive
   constructor structure), which the specification alone does not establish.

   **Third correction (2026-10-06, decided with Kim after an Astra opinion).**
   `Models.families` required each family's signature type `∀ params indices,
   Sort l` to be definitionally the declared type in the source environment.
   For the consumed families (whose indices must be the recursor pass's, since
   the generated motive types are built from them syntactically) this is the
   same obstruction once more: the recursor pass computes the index telescope
   by `whnf` in a context interleaving earlier families' indices, majors and
   motives, and the header phase records its telescope only existentially.
   Decision: drop the definitional conjunct from `Models.families` and add
   `InductiveSignature.FamilyTypesWF` beside `RecursiveTypesWF` in `Compiles`
   (recursor-declaration environment): the parameter-and-index telescope is a
   well-formed context and each family applied to it has type
   `Sort resultLevel`. Derivable for the consumed families from
   `sourceIndexDomains` and `sourceIndices_motive` without strengthening. Lost:
   exact agreement of each index domain with the declared one in its own
   prefix (domains that become equal only under a later binder). The nested
   restoration correspondence (`RestoresFamily.type`) and the K-like
   alignment (`kOfRealization`) consumed the definitional form and are
   rederived from source formation evidence; the restoration clause is
   weakened to "the source header is some telescope ending in the recorded
   sort". Pattern behind all three corrections: a clause tying a telescope
   computed by the recursor pass's `whnf` definitionally to header data in a
   clean context is not provable with the current foundations; provable are
   header-phase facts about the declared data in their own scope and
   well-formedness of the generated types in the recursor-declaration
   environment. Work on branch `agent/family-types` in a separate worktree.

   **Former statement of the risk.** `Compiles` (`Recursor/Realization.lean`,
   `CompilationRealization.generated`) requires `s.Models env decl` for the
   signature whose recursors and equations are installed, and
   `Models.recursiveTypes` asks, for every recursive field, a definitional
   equality `type ≡ s.recursiveType i r` in the *small* context
   `fieldTypes.take i ++ params`. The generator's hypothesis domains are
   `Instance.hypothesis`, built from `r.binders`/`r.indices`, so for the
   installed minor types to be syntactically the generator's output these
   shapes must be the translations of production's `loopUArgs` telescope
   (`RecInfoMinorHypothesisTypeOrigin.args`, `exposedType`). Production
   classifies recursive arguments in the big first-pass context
   (`RecursorRecursiveDomainAt.ctx := R'.mlctx.vlctx.toCtx`, Bindings.lean),
   which interleaves indices, majors, motives, earlier minors and stale fields;
   the raw signature's shapes (`signatureFieldOfUniform`, header phase) are
   only definitionally related normal forms, in the small context. Moving the
   production shapes to the small context is fine for translations
   (`TrExprS.weakFV'_inv` drops any unused free-variable declarations whose
   dependents are kept, and does not use `weakN_iff`), but the required
   *definitional equality* in the small context is exactly context
   strengthening, which `docs/inductives/STRENGTHENING.md` shows false in
   general. `Models.recursiveTypes` has no consumer in the theory besides
   `Models.mono` (grep 2026-10-05). Resolutions, to decide with Mario:
   (a) prove `TypeChecker.whnf` deterministic modulo free-variable renaming
   and context/environment extension, so the recursor-pass telescope equals
   the header-phase one and the raw `Models` transports; (b) have the type
   checker's `whnf` soundness also return an untyped head-reduction trace
   (`FullWHRedS`, whose `weak'_inv` strengthening exists in
   `Theory/Typing/FullHeadStrengthening.lean`) and strengthen the trace;
   (c) restate `Models.recursiveTypes` in the generator's own hypothesis
   context, where the checked recursor type supplies the typing by
   inversion (chosen; see above); (d) change the executable to reuse the
   header-phase classification (rejected: unnecessary divergence from the C++
   kernel). Cost check for (a) (2026-10-05): `Verify/TypeChecker/
   AlphaLocality.lean` already has the renaming framework
   (`ExprAlphaUnder`, `Context.OrderedBinderRenaming`) and locality of
   `whnf` only for the forall, immediate and free-variable-head cases
   (`whnf_forall_alpha`, `whnf_immediate_alpha`, `whnfFVarAt_alpha`);
   `RecursorFieldDecisions.alphaAlignment` (`ReplayCompat.lean`) is
   parametrised by an undischarged classifier-locality hypothesis and has no
   callers. The header phase's recursive normal form is definitional
   (`checkPositivity.loop.uniformNormalFormNarrow` yields `∃ normalized,
   IsDefEqU …`), not the translation of a retained telescope, so (a) also
   needs the header phase to retain its `whnf` telescope syntactically. Until
   one option is chosen, `canonicalConsumedGeneration` cannot be closed,
   independently of the uniqueness and inversion machinery of item 7. With
   (c) chosen, what remains for `canonicalConsumedGeneration` is the item 7
   program (define the shapes by translation strengthening, identify the
   minor group) plus `RecursiveTypesWF` for the actual instance, which
   follows from the retained type check by inversion.

## Assessment

The inductive verification is **not complete** and cannot be made sorry-free
inside this project's scope without solving open base metatheory:

- Five base sorries are the confluence-class conjectures also open upstream
  (`sort_inv`, `forallE_inv`, `sort_forallE_inv`, `rigidApp_inv`,
  `fieldType_inv_stratified`); `saturated_of_hasType` needs a rigid-head vs
  Pi separation lemma of the same class and is effectively base-layer.
- `weakN_iff` is false and must be replaced; about 72 textual uses of the
  `weakN_iff`/`weak'_iff`/`OnCtx.*_inv` family under `Verify` (2026-10-06
  count) depend on it, including `TrExprS.weakFV'_inv` (hence
  `MLCtx.restrictUpSetCtx` and the whole shape-definition program of item 7),
  `ConditionallyWHNF.weakN_inv` (the checker's cache invariant) and the
  header phase's `restrictTrExpr`. The repair needs a redesign (typing/defeq
  transport justified by actual inhabitants or a context-restricted invariant
  for the checker's cache), which is upstream work as well. What the
  consumers actually need is mostly existential well-formedness
  strengthening and strengthening at sort types, which the countermodel does
  not refute.
- The three core refinement junctions (`canonicalConsumedGeneration`,
  `canonicalCompletedRuleTranslation`, `assemblyNative`) are each a
  `Nonempty` of a large certificate structure assembling thousands of lines of
  component lemmas written against the formerly false model. Their
  components must be re-audited now that the template chain runs on the exact
  model; the executable they describe is now validated empirically against
  Lean's own recursors, which was not true before.
- **The junctions are the whole specification connection, not an
  assembly step.** Outside the three junction targets and their
  `Realization` definitions, the verification layer references the abstract
  generator only through `InductiveSignature.Instance.motive`
  (`CanonicalMotiveGroup.lean`). Nothing relates a production minor type to
  `Instance.minor`/`Instance.hypothesis`, a generated iota rule to
  `Instance.equation`, or `declareRecursors.recursorType` to
  `Instance.recursorType` (grep 2026-10-05). The equation layer
  (`Equation/*`, `Completed*`, about 56k lines) proves source-vs-production
  alignment of binders and residuals, not generator correspondence. So
  "recursor metadata/equations" and the minors part of recursor types are
  open in full, hidden behind `Nonempty` of certificate structures; the
  derived audit root `canonicalTypeTranslations` is not independent evidence.
  The first real junction theorem is: for `s := R.sourceSignature`, the
  production minor type of each constructor translates to `Instance.minor`
  (fields via `sourceSignature_fieldTypes`, hypotheses via
  `RecInfoMinorHypothesisTypeOrigin`, residual via the terminal spine).
- The honest reachable target is: executable validated against Lean on large
  corpora; inductive-specific obligations closed; final theorem conditional
  only on the named base conjectures; no false statement in the trusted base.
  Of these, the first and the last are done, and the middle two remain open.

## Remaining obstacles, in priority order

1. **Done: `Expr.abstract_eq_legacy` removed** (item 5/6 above). Residual
   risk: the new `SourceBVarClosed` hypothesis on the specification-facing
   theorems is not discharged by the executable; decide with Mario whether
   the kernel's silent repair of loose bound variables in source constructor
   types should be rejected instead (a one-line `hasLooseBVars` check in
   `checkInductiveSources`, which would be a divergence from C++ on
   malformed input and would let `SourceSyntaxChecks` carry the fact).
2. **Close the three refinement junctions. DONE (2026-10-06, 6f16a42):**
   `canonicalConsumedGeneration`, `canonicalCompletedRuleTranslation`,
   `finalValidOfStaged` and `assemblyNative` are all proved; no `sorry`
   remains under `Verify` or `Inductive`. History of the nested closure
   follows (kept for the record); the open proofs are now exactly the ten
   base obligations under `Theory` (item 3b) plus the `weakN_iff` route
   decision (item 3). Scoping (2026-10-06): the rule junction must produce
   `rules = g.equations` syntactically, so each generated rule is identified
   with `Instance.equation` component by component: outer domains from the
   checked type (`canonicalTargets`), field domains from `minorFieldsTemplate`,
   the right-hand side built constructively from the small-context shape
   translations exported by the first junction (weakened into the equation
   context, never derived from minor or recursor contexts, which would be
   strengthening), the left-hand side and type from
   `sourceConstructorIndices_replay` after universe rebase, typing of the
   equations transported from the equation layer's defeq-aligned residuals,
   recursor metadata from the generated entries (`getMajorInduct`,
   `KTargetCheck`), and the literal identity `info.rules = blueprints.map build`
   carried from the producer (dropped today before
   `CompletedRecursorPhasesResult`). Estimate 2k to 4k lines. The nested
   sorries: `finalValidOfStaged` needs executable-vs-abstract restoration
   commutation (`restoreNested` against `Restoration.expr`,
   `ContainerSpecialization` built from the lowering, name/order agreement),
   a rule-free restored recursor realization and `RecursorEnvCoherent.extend`
   for the stripped map; `assemblyNative` additionally needs the rule junction's
   content restored (`CompilationData.equations`, `RestoredRuleRealization`,
   provenance), `CertifiedSpecializations` from the installed containers, and
   a substitution lemma (restoration preserves `IsDefEq`) for the constructor
   correspondence; the auxiliary families' `resultLevel`/`indices` comparison
   rests on the Injectivity base sorries. Estimate 4k to 6k lines beyond the
   rule junction.
   **Progress (2026-10-06, later):** rule junction components committed:
   `GeneratedRecursorEntry.rules_eq`/`rulesLiteral` (literal blueprint builds),
   `consumedGeneration_shapeTranslations` (`Recursor/ConsumedShapeTranslations.lean`;
   `consumedGeneration` is now the explicit construction), `RecursorMetadataRealization`
   (`RecursorMetadataRealization.lean`, every `RecursorRealization` field but `rules`),
   `EquationWF.lean` (`equationsWF` modulo `GeneratorBodyTranslations`),
   `RuleLhsTranslation.lean` (lhs/type bodies, closedness),
   `RuleTranslation.lean` (`TrExprSyn`: untyped translation with unique targets;
   `ruleRhsSyn` hypothesis-free; `ruleRhsTranslation` needs any typed closed
   translation of the rule rhs, being discharged from the equation frame),
   `RuleTranslationAssembly.lean` (`completedRuleTranslation_of (Hrhs :
   H.RuleRhsTranslations) : Nonempty (CompletedRuleTranslationResult H)`).
   **Closed (2026-10-06):** `canonicalCompletedRuleTranslation` (moved to
   `CompletedRuleTranslation.lean`) `:= H.completedRuleTranslation_of
   H.ruleRhsTranslations`, no hypotheses; full build, tests, audit self-test
   and fresh `Init.Prelude`/`Init.Core` replays pass. Reachable sorries: the
   ten base obligations plus `assemblyNative` and `finalValidOfStaged`. Nested
   components committed: `Nested/ContainerSpecializations.lean`
   (specializations, certified, scoped, direct families, well-formed for the
   consumed parameters, constructor renaming), `Nested/RestorationCommutation.lean`
   (`restoreNested` vs `Restoration.expr` under `RestorationMapAgreement` and
   `RestoreReady`), `Nested/StrippedValidity.lean`
   (`finalValidOfStaged_of_shapes`), `Nested/RestoredRecursorShape.lean`
   (restored `VRecursorShape`), `Nested/CompilationDataAssembly.lean`
   (`CompilationData` of the run modulo `NestedCompilationPending`:
   constructor `RestoresType`, auxiliary family headers, restored recursors
   and equations), `Nested/RestorationAgreement.lean` (2026-10-06:
   `RestorationMapAgreement` for the run from `RestorationTableData` via
   `TrExprS.instantiateRevList_inv`; `RestoreReady` of lowered recursor types
   from the closed-form `LoweredRestoreReady`; per-owner
   `restoredRecursorTypes` modulo `ForallTelescope`/`LoweredRestoreReady`/
   `ForallDomainsReady` of the generated type and the restored type's
   translation). Found and repaired there: the `head` clause of
   `RestorationMapAgreement` was false for open arguments (sequential
   `instantiateRev`), now requires free-variable arguments of parameter arity;
   `RestoreReady` rejected literals (`lit`/`mdata` cases added). In progress:
   discharging those syntactic hypotheses, `Theory/Inductive/RestorationDefEq.lean`
   (restoration preserves `IsDefEq`; constructor `RestoresType`), and the
   auxiliary family header conjuncts.
   **Later (2026-10-06):** the readiness predicates were false for inputs with
   `let`/`proj`; replaced by `Expr.HitShape` (Nested/HitShape.lean: every
   auxiliary head applied to the parameter variables at the declaration's
   universe parameters) with commutation from hit shape plus the translation
   of the restored output in an auxiliary-free environment
   (`RestorationCommutationHit.lean`). Committed since: beta subject
   reduction, eliminator schema avoidance, source and auxiliary constructor
   restoration (restoring expansion leaves, lowering levels recorded in the
   traces), auxiliary family headers, `CompilationData` assembly
   (`CompilationDataConstructors.lean`), restored recursors field
   (`RestoredBlockAssembly.lean`), hit-shape provenance of generated
   recursor types and rule rhs (`RecursorHitShape.lean`, modulo
   `HitShapeInputs` and `WhnfHitShapeFacts`), run-level inputs and totality
   (`HitShapeInputs.lean`). In flight: retained `loopArgs1`/call-root traces
   (`indexDomains`, `callRoots`; branch `agent/verify-inductives-origins`),
   whnf/inferType hit-shape preservation (`agent/verify-inductives-hitshape`:
   `whnf.hitShape`, `inferType.hitShape` proved via new `VState.WF`/`Methods.WF`
   cache invariants; `EnvHitShape` instance for the lowered environment and
   the `WhnfHitShapeFacts` discharge pending), restored equations identity,
   and `Hshapes`/`finalValidOfStaged`.
   **Later still (2026-10-06):** `HitShapeInputs` fully discharged on
   `agent/verify-inductives-origins` (retained `loopArgs1` traces
   `RecursorIndexTrace`/`RecInfoIndexTraces` inside `RecInfoMinorSourceAlignment`,
   rooted call origins `RecInfoCallBlueprintOrigins.rooted`; family headers
   avoid the auxiliary names because `buildAuxiliary` never lowers headers:
   `LoweredInductiveMapping.type`), so `recursorHitShape` needs only `W`.
   Restored equations (`RestoredEquations.lean`): rule right-hand sides are
   identified with the restoration of the generator's equations through the
   lambda-telescope commutation; lhs and type cannot be read off the
   executable (`RecursorRule` has only `ctor`, `nfields`, `rhs`) and are
   supplied by the certificate's own rule choice (`RestoredRulesRealization`),
   which `assemblyNative` must realize with the restored generated lhs/type.
   **`finalValidOfStaged` closed (4a1e2e6):** `finalValidOfStaged_of_hitShape`
   (Nested/FinalShapes.lean) reads the restored recursor shapes off the
   staged block and the restoration traces (more than one family from
   `aux2nested.size ≠ 0`, available at the dispatch site), modulo
   `HitShapeInputs` (discharged on the origins branch) and
   `WhnfHitShapeFacts`. The checker-level whnf fact is proved on the
   hitshape branch only at the larger head set `E.hitHeads` (auxiliary names
   plus main constructors) with the projection condition `ProjsOK`
   (`WhnfHitOKFacts`, modulo `hprims`: no main constructor named like a
   checker-built constant); the `RecursorHitShape` chain is being reworked to
   run at that head set and shrink back. In flight: that rework,
   `assemblyNative_of_whnf` (origins worktree).
   **Milestone (2026-10-06, main at 9cc9c8e):** full `lake build` (676 jobs),
   `lake build Lean4Lean.Tests`, fresh `Init.Prelude` (1975) and `Init.Core`
   (3953) replays pass; audit self-test passes. Reachable sorries: the ten
   base obligations and `assemblyNative` only.
   **Hit-shape chain complete on `agent/verify-inductives-hitshape` (cb54cf6,
   pushed; being merged into main):** `recursorHitShape' E wf Hsources hprims`
   gives `HitShapeTele E.auxHeads …` of every owner's generated recursor type
   and rule rhs with no `W`/`I`; the chain runs at `E.hitHeads` (auxiliary
   names plus main constructors) under `HitOK` (hit shape plus `ProjsOK`),
   and shrinks back. The single remaining hypothesis is
   `hprims : ∀ n ∈ hitPrimNames, n ∉ E.mainCtorNames` (no main constructor is
   named like a constant the checker builds itself: `String.mk`, `List.nil`,
   `List.cons`, `Char.ofNat`, `Nat.zero`, `Nat.succ`, `_inhabitedExprDummy`,
   …); `hprims_of_present` reduces it to "those names are already constants
   of the source environment (true after `Init.Prelude`) and no constructor is
   named `_inhabitedExprDummy`". Removing it needs a rework of the checker's
   `EnvHitShape.prims` field (showing literal expansion and the out-of-range
   dummy never reach a successful recursor-pass output). **Decision for Kim:**
   carry `hprims` as an explicit hypothesis of the nested theorem (hence of
   `addDecl.WF` for nested inductives) or fund the rework. **Resolution
   (2026-10-06, after Kim asked what Mario would do): rework.** No
   input-naming hypotheses on soundness theorems; the literal-expansion
   sites only need the hard-coded constants that exist in the environment
   not to be heads (discharged by freshness), and the out-of-range dummy must
   be shown unreachable on successful runs. **Done (d12593f, merged as
   ebc0e0e):** `EnvHitShape` now has `prims` (the seven kernel primitive
   names are never heads: every installed name passed `checkName` without
   primitive permission) and `strs` (when string literals are supported,
   `String`/`Char`/`List.nil`/`List.cons` are old constants, hence not
   heads); every out-of-range read is shown in range. `hprims` is gone from
   the whole nested chain; `assemblyNative_of_run (E) (wf) (Hsources)
   (Hrules) (Hprovenance)`.
   **`assemblyNative_of_hprims` (Nested/AssemblyNativeWhnf.lean, merged
   89776a7):** the nested final assembly certificate from `wf`, `Hsources`,
   `hprims` and two named hypotheses: `Hrules` (a shape `C` whose rules
   realize `RestoredRulesRealization`: the validator's rule lhs is its own
   build and the rule type is the checker's inferred type, neither
   syntactically `r.expr` of the generated equation; plus freshness of the
   restorable names in `C.finalBaseVEnv`) and `Hprovenance`
   (`InductiveRecursorProvenance` of the restored recursors with their rules;
   open core: `VConstructorShape` of every restored rule's constructor,
   container constructors included). Agents on both. `CompilationData`
   including `recursiveTypesWF`, `CertifiedSpecializations` and
   `RestoredCompilationRealization` are proved from the run.
   **Rule junction status (1f8f1dd):** `hrules_of (E) (wf) (Hsources)
   (HauxRecNames) (HruleShape)` (Nested/RuleJunction.lean): freshness of the
   restorable names in any shape's final base environment is proved except
   for a pathological coincidence between a renamed auxiliary recursor name
   `Main.rec_k` and an auxiliary head name (`HauxRecNames`; arises only
   because the commutation takes freshness in the TARGET environment, which
   for rule rhs contains the restored recursors; being replaced by
   source-environment absence plus trailing-argument provenance).
   `HruleShape` (a shape whose rules realize `RestoredRulesRealization`)
   is the main remaining nested obligation: the validator's rule lhs/type are
   its own build and the checker's inferred type; route: rebuild the shape
   with the restored generated lhs/type and prove their well-formedness from
   the restored recursor type plus unique typing (agent running).
   **`Hprovenance` proved (104639f):** `hprovenance_of (E) (wf) (Hsources)
   (hnested : result.aux2nested.size ≠ 0)` (Nested/RecursorProvenance.lean);
   `hnested` is in scope at the only call site of `assemblyNative`
   (`Nested/FinalModelDispatch.lean`) and must be threaded into
   `assemblyNative`'s signature at wiring time. Remaining for the nested
   junction: `HruleShape` and the `HauxRecNames` residue.
   **Collision finding (bb40f64, Nested/AuxRecNames.lean):** in the
   pathological case of a source family named `_nested.i.x` with a container
   constructor `J.x.rec_k`, the auxiliary constructor name EQUALS the renamed
   recursor name `Main.rec_k`, so freshness of all restorable names in the
   final base environment is false; the restoration itself still agrees with
   the executable (the aux constructor is restored before the renamed
   recursor is interpreted). The commutation is generalized to freshness
   outside an avoided set `X` plus input-side `HitTrailAvoids`/
   `LamPrefixAvoids`; the assembly interface is being switched to these
   modulo forms, with the residue `LoweredRulesAvoid E heads X` (lowered
   rules' hit trailing arguments and parameter domains avoid the renamed
   names) to be discharged from the checker's hit-shape invariant (aux
   constructor names never occur in index expressions or parameter domains).
   **Done (next commit after 24cf282):** `assemblyNative_of_run` (now in
   Nested/RuleJunction.lean) takes `Hrules`/`Hprovenance` in the modulo
   forms; `hprovenance_of (E) (wf) (Hsources) (hnested)` and
   `hrules_of (E) (wf) (Hsources) (HruleShape)` discharge them;
   `loweredRulesAvoid_renamed` closes the residue. **`HruleShape` is the only
   remaining premise of the nested assembly** (agent running on
   Nested/RuleShape.lean).
   **`HruleShape` proved modulo `HrestoredWF` (53437e2, Nested/RuleShape.lean):**
   the shape is rebuilt with the restored generated equations as its rules
   (`NestedFinalAssemblyShape.withRules`); primary iota shapes and auxiliary
   guardedness come from the validator by translation uniqueness. The last
   nested premise is `HrestoredWF`: every restored generated equation is
   `VDefEq.WF` in the shape's final base environment (route: transport the
   generated equation's well-formedness from the lowered recursor environment
   through a restoration substitution extended with the recursor renaming).
   Agents: `hrestoredWF_of` and the `assemblyNative` wiring with `hnested`.
   **Wiring done (a24fc27):** `assemblyNative` lives in
   Nested/AssemblyNative.lean, takes `hnested`, and
   `assemblyNative_of_restoredWF (E) (wf) (Hsources) (hnested) (HrestoredWF)`
   is proved by composition; the final body will be
   `assemblyNative_of_restoredWF E wf Hsources hnested (E.hrestoredWF_of wf Hsources)`
   once `hrestoredWF_of` lands (agent running).
   **`hrestoredWF_of` proved modulo `NestedRestoredEquationGaps` (cf712fb):**
   Theory/Inductive/RestorationRenaming.lean extends restoration-preserves-
   typing with the recursor and projection renaming (`VExpr.replaceRen`,
   `RenamingReplacement`, `ProjectionTransport`); the nested instantiation
   transports the lowered generated equations' well-formedness (in the
   rule-free lowered recursor environment) to the final base environment.
   Six gap fields remain, all believed true: projection names avoid the
   restorable names in eliminator schemas, lowered constructor types,
   generated recursor types and equations (agent: `ProjsOK` from the hit-shape
   chain plus a projection-name analogue of `IsDefEq.noConsts`); typing of each
   auxiliary constructor's restoration lambda from the container's formation;
   and `ProjectionTransport` for the lowered projection entries (agent).
   **Container fields (977b14f):** field 5 proved with no hypothesis (the
   container's installed formation types `J.c levels args`); field 6 proved
   for source structures whose lowered constructor type mentions no
   restorable name, and reduced otherwise to `NestedProjectionTransportGap`:
   `primaryFields` (field-type transport of nested source structures: the two
   field types differ by beta of the restoration lambdas under substitution,
   but `projDF` carries no context well-formedness) and `auxiliary`
   (projection entries of auxiliary structure-like families versus their
   containers' registered projections). Agent running on both.
   **Projection-name fields (35998dc):** fields 2 to 4 proved (translated
   terms project only out of registered structures; `ProjsOK` of the
   generated recursor types at the full head set; every piece of a generated
   equation occurs in a recursor type). Field 1 (eliminator schemas of
   EARLIER blocks) is not derivable from `VEnv.WF`: a schema may contain
   `.proj _nested.k …` from that block's own auxiliary structure families and
   the current block may reuse the name. **Decision (2026-10-06): strengthen
   the certificate** `CaseSchema.Certified` with "schemas project only out of
   structures registered at registration time" (a new producer obligation,
   provable from translation; no theorem is weakened), derive field 1 from it
   and freshness. **Done (next commit after 7e5cdaa):** the fact lives in the
   data `VEnv.WF'.inductEliminators` carries (`CaseSchema.ProjNamesRegistered
   env key`, Theory/Inductive/CaseFormation.lean), since `Certified` knows only
   the base environment; `WF.eliminatorsProjNamesRegistered` by induction on
   `WF'`; `eliminatorProjNames_of` and `restoredEquationGaps_of'` (no `Helim`).
   Note: no producer in the verified pipeline registers eliminator schemas
   (`inductEliminators` has no caller), so the strengthening creates no new
   proof obligation today; the two registration lemmas take it as a premise.
   **Projection transport (28b72e3, Nested/ProjectionTransportGap.lean):**
   `primaryFields` proved syntactically modulo beta conversion in arbitrary
   contexts; the context-free `auxiliary` transport is unprovable in
   arbitrary contexts (counterexample in the module docstring: `projDF`
   carries no context well-formedness); the fix is the context-carrying
   `RenamingReplacementOnCtx`/`ProjectionTransportOnCtx` provided there. Final
   agent: switch `RestoredEquationWF` to the OnCtx transport, prove both
   projection fields (auxiliary via the syntactic specialization of restored
   auxiliary constructor types from the lowering trace), compose
   `hrestoredWF_of` with no gaps, and replace the `assemblyNative` sorry.
   **NESTED JUNCTION CLOSED (6f16a42).** `assemblyNative :=
   assemblyNative_of_restoredWF E wf Hsources hnested (E.hrestoredWF_of wf
   Hsources)`; the transport is the context-carrying
   `RestorationRenamingOnCtx`; auxiliary projection transport via the
   constructor shape up to level equivalence now recorded in the lowering
   traces (`BuiltConstructorTranslation.directAuxiliary`,
   `FinalLoweredGeneratedFamilyNativeSource.constructorShapes`,
   `AuxiliarySpecializationEvidence.constructorShapes`). Full build (695
   jobs), tests, fresh `Init.Prelude`/`Init.Core` replays and the audit
   self-test pass; `grep sorry` under Verify and Inductive is empty; the
   audit reports "10 distinct proof obligations remain" (the base ones).
   `scripts/inductive-audit-inventory.json` no longer lists `assemblyNative`.
   **E3 re-merged with the closed main (94cfc7a, pushed):** one conflict in
   `AssemblyProviderEvidence.lean`; `RuleShape.lean` needed
   `finalBaseVEnv_strengthening` (from `E.sourceStrengthening.recursors`);
   full build, tests, `Init.Core` replay and audit pass; `addDecl.WF`
   unchanged; the nine base declarations (13 sorry sites) are the only open
   proofs there. E1 per-phase work (steps 3 to 6) continues on its branch.
   **Standard restated by Kim (2026-10-06): nothing counts as done until
   `addDecl.WF` is proved with complete proofs** (no sorry, no hypotheses
   beyond the specification). Kim also does not accept the prose
   countermodel as establishing that `weakN_iff` is false, and regards the
   equality-free environments where it would fail as irrelevant to the goal.
   Consequences: (i) a machine-checked refutation attempt is running (branch
   `agent/verify-inductives-base`): a finite groupoid model of
   `VEnv.IsDefEq` for the small environment, with feasibility report first;
   if it fails at a rule, strengthening may be true and a proof attempt
   follows; (ii) E1 PAUSED at a clean commit (14d38a5, pushed): one site
   (`weakBV_inv_lift`) remains below `addDecl.WF`, dead lemmas not yet
   deleted; the executable change is only warranted if strengthening fails
   in real environments; (iii) on E3 the abstract hypothesis is being
   replaced by the concrete, monotone `VEnv.HasCanonicalEq` plus the base
   conjecture `strengthening_of_canonicalEq` (wrapper
   `addDecl.WF_of_canonicalEq`), so the top-level hypothesis is "the
   environment contains canonical `Eq`"; (iv) the base obligations
   (confluence, injectivity, strengthening with `Eq`) are on the critical
   path, not optional.
   **Base-obligations design (2026-10-06, `docs/inductives/BASE_OBLIGATIONS_DESIGN.md`):**
   Injectivity cannot be derived from the current confluence development
   (circular: confluence uses `uniq` about 130 times, `uniq` uses
   Injectivity); height-stratified induction is not well-founded (the `defeq`
   constructor takes unstratified `IsDefEq`); normalization is FALSE for this
   calculus (Abel–Coquand 2020; `def T := T` loops), so normalization-based
   literature does not apply. Non-circular route: a semantic layer
   (Coquand–Huber adequacy over finite shapes, prototyped by Mario in
   `Experimental/ShapeLogRel*`) proving ONE theorem `VEnv.WF.headInversion`
   (sort/sort, forallE/forallE, rigid/rigid with argument equality, three
   separations), from which uniqueness and all inversions follow. Phases:
   0 (1.5k to 2.5k lines, low risk): `HeadInversion` structure,
   `uniq_chain`/`TypeChain.collapse`, the five Injectivity lemmas,
   `saturated_of_hasType` and two separations, all from `headInversion` (six
   cone sorries collapse to one believed-true base theorem); 1 (15k to 25k,
   high risk, coordinate with Mario): the semantic layer, which likely needs
   canonical `Eq`; 2 (6k to 10k): confluence completion assuming
   `headInversion`; 3 (8k to 15k, open): strengthening with `Eq` via a
   conversion-certificate calculus, after a 1k to 3k falsification study.
   Total 35k to 55k lines. **Phase 0 done (222373b9, on main):**
   `Theory/Typing/HeadInversion.lean` defines `TypeChain`, `SpineArgsEq`,
   `HeadInversion` (eight fields: the seven designed plus `proj_fieldType`,
   because the projection case of uniqueness substitutes untypable data
   projections for unused earlier binders and cannot be derived from the
   others without strengthening) and the single conjecture
   `VEnv.WF.headInversion`; `IsDefEq.uniq` is reproved without
   stratification (`uniq_chain`, `TypeChain.collapse`); `sort_inv`,
   `forallE_inv`, `sort_forallE_inv`, `rigidApp_inv`, `structApp_inv`,
   `saturated_of_hasType` are theorems; new `rigidApp_forallE_inv`,
   `rigidApp_ne`, `sort_rigidApp_inv`; `forallE_inv_stratified` and
   `fieldType_inv_stratified` deleted. Remaining Theory sorries on main:
   `headInversion`, `weakN_iff` (false; replaced on E3 by
   `strengthening_of_canonicalEq`), `headParallel`, `fullStep`, `strip`.
   Phase 1 spike (semantic layer on the `Experimental` prototype) started.
   **Phase 1 spike result (branch `agent/verify-inductives-headinv`,
   d77f4fc6, pushed; `docs/inductives/PHASE1_SPIKE.md`): the semantic route
   as designed is a NO-GO for the injectivity half**, and `HasCanonicalEq`
   does not rescue it. Proved in Lean from explicit interface assumptions:
   (1) `HeadModel.readThrough`: in any sound model where proofs carry no
   information, an eliminator on a proof major takes its iota value whenever
   the model cannot distinguish the index from the aligned one (proof
   irrelevance hides the major; shape models cannot always separate
   indices); (2) `check_of_piAdequacy`: with the K-like/singleton step gated
   by a declarative index check, any Carneiro-style adequacy proof of
   `forallE_forallE` derives equality REFLECTION (`a = b ⊢ a ≡ b`), believed
   false; firing without the check yields ill-typed reducts; the index check
   is also circular in the derivation induction. The separation half
   (`sort_sort`, `sort_forallE`, `sort_rigid`, `forallE_rigid`, head and
   level parts of `rigid_rigid`) follows from any sound model
   (`HeadModel.separation`), but downstream lemmas also need uniqueness. The
   only repair found: an Observational-Type-Theory-style cast-pushing
   reduction inside the logical relation (untried, no precedent with
   proof-irrelevant K), 11k to 19k lines; Phase 1 total 19k to 31k. Also:
   `Eq` is not needed to extract a singleton's proof field (the family's own
   recursor does it), and Mario's `Experimental/SExpr.lean` no longer builds
   on this branch (non-exhaustive matches after `VExpr` gained `elim`/`proj`).
   **`headInversion` is therefore an open metatheoretic problem**
   (consistent with the Lean4Lean paper retracting the uniqueness proofs).
   **CI note:** the step "Build Lean4Lean.Experimental" has failed on this
   branch since 368a34ca (`VExpr.elim`/`proj`, `Pattern.elim`,
   `Check.nonzero`, six strong-typing rules). c1e990a7 adds the missing
   match arms to `Experimental/SExpr.lean` (and partly `NormalEq.lean`), so
   SExpr and its seven dependents build; still failing: `NormalEq.lean`'s
   `proj` case of `instN_r` (the file's abstract `Typing` has no `proj_inv`;
   header says "TODO: remove, now part of ChurchRosser"),
   `ParallelReduction.lean` (imports it), `Stratified.lean:85` and
   `StratifiedUntyped.lean:67` (inductions over strong typing lacking the six
   new rules: real obligations). Options: exclude those files from the
   `Lean4Lean.Experimental` glob, port the ChurchRosser fixes, or allow
   sorries there. Decision for Kim; none affects `addDecl.WF`.
   **Church-Rosser step 1 (branch `agent/verify-inductives-cr`, b70dd16b,
   pushed):** `NormalEq` re-indexed by a Nat bound (`NormalEqN`, `etaBoth`;
   eta/eta transitivity closes without inverse weakening); every
   `weakN_iff` reference removed from ChurchRosser (`weakN_inv_DFC`,
   `ParRed.weakN_inv`, the `ParRedExt` beta machinery deleted; beta by
   `NormalEqN.beta_aux`); ParRed-only confluence retired for
   `FullCRDefEq`; spine exposure (`NormalEqN.spine_expose`) and
   `SpineTransport` close `headParallel` (now `NormalEq.parRed`) and the
   `fullStep` delta/quotDelta/projection-iota cases, and the distinct-family
   case of `strip`. Named hypotheses collected in class `HeadSeparation`
   (`not_pi`, `proof_major`, `case_not_pi`, `rigid_not_pi`, `rigid_ne`); the
   last two are Phase 0's `rigidApp_forallE_inv`/`rigidApp_ne` (to be
   discharged on merge); `proof_major` needs a typing analysis of native
   recursors. Still open: `FullStep.strip` (general confluence): the local
   confluence property fails for `FullStep` because delta/quot/projection/eta
   steps do not reduce subterms; needs a fully parallel full-step relation
   with its own substitution lemma and the critical-pair analysis (native
   iota against native prefix unfolding at the same head). Next task.
   **Church-Rosser step 2 (d0470e04, pushed): `HeadSeparation` is gone;
   every field is a theorem** (`rigid_not_pi`/`rigid_ne` from Phase 0;
   `MatchedCaseStep.major_not_pi` via a new declaration-history invariant
   `VEnv.CtorResultRigid` and `WF.case_family_head_rigid`;
   `Params.major_not_pi` and `Params.major_proof` via
   `NativeRecursorRegistered.family_head_rigid`/`result_sort`/
   `major_not_proof` (new `Theory/Typing/NativeMajorFamily.lean`);
   `Params.pat_recursor` now records that an iota pattern's owner has a
   constructor). The native-iota-vs-prefix-unfolding critical pair does not
   exist (incompatible universe guards). `strip` obstacle: `FullStep.funEta`
   at head position breaks the one-step local property (counterexample
   `app (Nat.rec z s) Nat.zero`; the peak closes in two steps, so `strip` is
   not refuted). Decision (2026-10-06): restrict `funEta` to non-head
   positions (internal proof device; fall back to decreasing diagrams if the
   completeness direction needs head eta). After step 2, `addDecl.WF` depends
   only on `weakN_iff` (hypothesis on E3) and `headInversion`.
   **Milestone (main at 27510ecd):** full build, tests (150 jobs), fresh
   `Init.Core` replay (3953) and audit self-test pass after the Phase 0 and
   spike merges; five sorry warnings (`headInversion`, `weakN_iff`,
   `headParallel`, `fullStep`, `strip`), the last three closed on the cr
   branch pending merge. **Merged (0525770b):** main's open proofs are now
   exactly `headInversion`, `weakN_iff` (hypothesis on E3), `strip`
   (in progress on the cr branch). **E3 at c6293804 (pushed) carries all
   of this:** its open proofs are exactly `headInversion`,
   `strengthening_of_canonicalEq`, `strip` (audit: "2 distinct proof
   obligations remain" from the roots, since `strip` is outside the
   `addDecl.WF` cone). So on E3, `addDecl.WF_of_canonicalEq` rests on two
   conjectures: head inversion and strengthening with canonical `Eq`.
   **E3 canonical-`Eq` wrapper done (c4ebdf45, pushed):**
   `Theory/CanonicalEq.lean` defines `VEnv.HasCanonicalEq` (constants `Eq`,
   `Eq.refl`, `Eq.rec` with explicit `VExpr` types and the `Eq.rec` rule in
   `env.defeqs`; `HasCanonicalEq.mono`), the single conjecture
   `strengthening_of_canonicalEq (henv : env.WF) (heq : env.HasCanonicalEq) :
   env.Strengthening` (registered in the audit inventory), and
   `addDecl.WF_of_canonicalEq (wf) (heq : ∀ safety, (ves.venv safety).HasCanonicalEq)
   (decl) (hdecl)` plus `addDecl.WFHasCanonicalEq` returning the hypothesis
   for the output (iterable over a replay). Two clauses of
   `Declaration.Strengthening` gained WF premises their callers already had
   (unsafe definition's constant WF; projection environment WF). Caveats being
   checked: that the replay of `Init.Prelude` installs exactly the stored
   forms (universe order of `Eq.rec`, rule shape), and an `EqBootstrapShape`
   `nparams = 1` vs real `Eq` (2 params, 1 index) mismatch.
   **Realizability (a1ea806a on E3, pushed):** the stored forms match the
   real `Init.Prelude` declaration exactly (universe order `[u, u_1]`;
   `Verify/Inductive/EqCanonicalForms.lean` proves any translation of the
   production expressions equals the stored terms; `Compiles.eqRecRules`
   derives the stored rule from the recursor type;
   `addDecl.eqBootstrapHasCanonicalEq` shows the bootstrap run of `Eq`
   yields `HasCanonicalEq` provided the installed `Eq.rec` has the
   production type (`IsProductionEqRec`, an executable fact checked by the
   new test `Lean4Lean/Tests/CanonicalEq.lean`, not provable from the theory
   since the recursor construction uses extern `Expr` operations). The
   `EqBootstrapShape` `nparams = 1` was a real bug making the bootstrap
   theorems vacuous for the real `Eq`; fixed to 2 with the two-parameter
   lowering proof redone; no executable change.
   **E3 at 41ff3b52 (pushed) carries Phase 0:** remaining Theory sorries on
   E3 are exactly `headInversion`, `strengthening_of_canonicalEq`,
   `headParallel`, `fullStep`, `strip` (the last three being closed on the
   cr branch, to be merged). The inventory still lists
   `canonicalConsumedGeneration` and `canonicalCompletedRuleTranslation`
   although they contain no sorry (stale entries; harmless, to be pruned).
   **Decision (Kim, 2026-10-06): the final theorem may assume the environment
   contains canonical `Eq`.** So the strengthening obligation is stated as
   the base conjecture `strengthening_of_canonicalEq : env.WF →
   env.HasCanonicalEq → env.Strengthening`, and `addDecl.WF_of_canonicalEq`
   takes `(heq : ∀ safety, (ves.venv safety).HasCanonicalEq)` (monotone under
   extension, preserved by the conclusion). The equality-free refutation is
   no longer on the critical path (feasibility report only). Critical path:
   the base obligations (confluence programme started on branch
   `agent/verify-inductives-cr`).
   Refutation feasibility (`docs/inductives/COUNTERMODEL_FEASIBILITY.md`): a
   machine-checked groupoid countermodel would be 10k to 18k lines (the model
   must cover every rule of `VEnv.IsDefEq`; no proof-irrelevant model can
   separate the endpoints); the reviewer judges the unrestricted statement
   false and strengthening with canonical `Eq` plausibly true but unproved
   (a proof would need normalization or confluence for typed proof
   irrelevance with iota and K). **Reversed (Kim, 2026-10-06): a formal
   refutation of strengthening without canonical `Eq` is worth having.**
   Restarted without budget on `agent/verify-inductives-base`
   (Lean4Lean/Theory/Typing/Countermodel/): WF environment via a direct
   certificate, larger-context derivation, groupoid model with soundness for
   every `IsDefEq` rule, separation at `v = 2`; target
   `strengthening_fails : ∃ env, VEnv.WF env ∧ ¬ env.Strengthening`,
   axiom-clean. **Status (435f2d8b on that branch, pushed;
   `docs/inductives/COUNTERMODEL_STATUS.md`):** the environment's `VEnv.WF`
   is PROVED by a direct certificate (`envCM_wf`; `.elim` registration cannot
   give large elimination for a Prop family, so native recursors are used),
   the larger-context derivation `larger_defeq : envCM.IsDefEq 0 ctxL SI↑
   SJ↑ (sort 1)` is PROVED, and `strengthening_fails_of_separated (hsep :
   ¬ envCM.IsDefEqU 0 ctxS SI SJ) : ∃ env, VEnv.WF env ∧ ¬ env.Strengthening`
   is proved, all axiom-clean (1322 lines). The separating model is BLOCKED
   for a set-theoretic reason: soundness must cover every closed universe
   level (`sortDF` types `Sort n` for all `n`), so all universe
   interpretations must sit in one Lean universe, each an element of the
   next, and with Π as all sections each universe is inaccessible-sized; Lean
   cannot prove such an unbounded chain exists (a plain set model has the
   same problem; groupoids are additionally required: a transport-free model
   fails on an explicit motive). Ways forward are research-scale designs
   (realizability-style groupoid model over syntax with big-step evaluation;
   or a restricted Hofmann–Streicher model with hereditarily bounded
   sections). Decision for Kim: pursue one, or accept the conditional
   theorem.
   Literature (Astra, `docs/inductives/STRENGTHENING_LITERATURE.md`):
   Carneiro's thesis (§3.2, Weakening (4)) states strengthening with a proof
   by mutual induction that does not address the transitivity case; the
   Lean4Lean paper (§2.4, Conjecture 2.10) labels strengthening a conjecture
   and retracts the thesis's uniqueness/inversion proofs; Coquand–Spiwack
   (LICS 2006, §4.4) report failure of strengthening in a related
   proof-irrelevant calculus; no published treatment of the singleton-family
   example. The riskiest model rule is `elimIota`. Judgement: unrestricted
   statement probably false; with canonical `Eq` plausibly true, unproved.
   **Process rule (Kim, 2026-10-06): no size or time budgets in agent briefs
   for anything on the critical path.** Agents run to completion or to a
   genuine mathematical obstacle (a statement believed false, or a precisely
   stated missing metatheorem); "isolate as a named hypothesis" is only for
   the latter, never for size. Earlier budgets caused premature hand-backs.
   **Merged into main (2026-10-06):** `finalValidOfStaged_of_hitShape`,
   `restoredMajorHead`, `restoredRecursorEntries_of_steps`,
   `strippedRecursorOfStep` (Nested/FinalShapes.lean) and
   `assemblyOfFormationNative`/`assemblyShapeNative`
   (Nested/AssemblyProviderEvidence.lean) now take `(wf) (Hsources) (hprims)`
   in place of `(I) (W)` and use `recursorHitShape'`.
   Record of what the first junction used: the `params` and `motives`
   groups (`recursorTelescope_params`, `recursorTelescope_motives`), the
   field-domain template `minorFieldsTemplate`, the per-minor translation
   `recursorTelescope_minor`, the field-domain identification
   `recursorTelescope_minorFields`, and the residual inversion
   `recursorTelescope_minorResidual` (motive variable, constructor spine),
   the index identification `recursorTelescope_minorIndices`, the
   hypothesis-domain shape `recursorTelescope_hypothesisShape`, the index and
   major groups `recursorTelescope_indicesMajor`, and the assembly
   `recursorTarget_eq_of_minors` (recursor type modulo the minor group).
   Previously planned and now done: `idx` equals the lifted
   `sourceConstructorIndices`
   (forward: `liftOriginalType`, `insertBeforeInner`, `bvLift`, then
   uniqueness); each hypothesis domain inverts to `wrapForalls A (app (mkApps
   (bvar m) I) (mkApps (bvar f) bvars))`, and the consumed signature's
   `Recursive` shapes must be defined so that `Instance.hypothesis` reproduces
   `A` and `I`: either as unlifts (`VExpr.unliftN`) of the inverted domains,
   justified by first-pass scope facts (`O.args` domains and `exposedType`
   indices mention only parameters, earlier fields and earlier arguments), or
   by forward derivations closed with `mkLambda` over fields and arguments,
   dropped to the parameter suffix (`dropFVarPrefix`), abstracted
   (`abstractParameters`) and weakened. Then `Models` of the consumed
   signature by definitional transport from `sourceSignature_models`,
   `sourceOrigins` by construction, `types` from `T.target_eq`, and
   `minorTranslation` from the `params ++ motives ++ minors` prefix of `T`.
   The `Recursive` shapes and `Models.recursiveTypes` are blocked by item 8.
   The other junctions (`canonicalCompletedRuleTranslation`, `assemblyNative`)
   need `RecursorEntryRealization` per owner (`Recursor/Realization.lean`) and
   the restored analogue plus `InductiveRecursorProvenance`; the equation
   build (`existsCanonicalGeneratedEquationBuild`) supplies the rule list.
   Staging: the junction is proved at the `CompletedRecursorConstruction`
   stage, whose fields (now including `recursorTypes`) are the only premises;
   post-installation results (`GeneratedRecursorTelescopeTranslation`,
   `finalSelectedMinorTypedSplit`) are reusable as technique only. Use the
   recursor-comparison scratch (regenerating `Acc`, `iterates`, nested types
   through `Lean4Lean.addDecl`) as the executable oracle.
3. **Replace `weakN_iff` and repair consumers**; coordinate with upstream.
   **Scoping (2026-10-06, `/tmp`-free summary):** a dependency walk of the
   built oleans found 3445 constants depending on `IsDefEqU.weakN_iff`, 1523
   of them in the cone of `addDecl.WF`, through every declaration kind: the
   checker-cache invariants `ConditionallyHasType.weakN_inv` /
   `ConditionallyWHNF.weakN_inv` (`Verify/Typing/ConditionallyTyped.lean`)
   used when `withLocalDecl`/`withLetDecl` leave a scope, and the
   `EquivManager` invariant `VState.WF.ectx` used by `quickIsDefEq.WF`. The
   weaker fallbacks (existential `VExpr.WF` strengthening, `IsType`
   strengthening, strengthening at sorts, `TrExprS.weakFV'_inv`) are refuted
   as well: `(fun x : SJ => x) z` with `z : SI` is typed under `q` and, by
   `app_inv`, uniqueness and `forallE_inv`, typing it without `q` would give
   `SI ≡ SJ`. Only two use sites are pure weakening. **Executable evidence
   (`docs/inductives/CacheScopeExperiment.lean`):** both the C++ kernel and
   the Lean4Lean checker accept a closed definition whose typing needs
   `SI ≡ SJ` in the empty context, provided an earlier `let` binding forces
   the comparison chain under a binder `q : P v` first; without that binding
   both reject it. So the implemented conversion is not local to the context
   and no invariant of the form "cache entries are derivable in the current
   context" holds for the current executable; `addDecl.WF` as stated is
   false for it (assuming the countermodel). Options for Kim: E1 change the
   executable (save and restore caches and the `EquivManager` around binder
   scopes, always open a binder in `isDefEqLambda`/`isDefEqForall`, re-check
   a few Primitive gadget pieces in the empty context; statement of
   `addDecl.WF` unchanged; departs from C++ exactly on declarations whose
   acceptance needs a conversion established under a binder and reused
   outside it; performance to measure); E3 add an environment-level
   strengthening hypothesis to `addDecl.WF` (restricts the theorem; false
   for some Lean-valid environments). E2 (prove executable locality) is
   impossible given the experiment. Inductive-side consumers (header phase,
   consumed translation, `restrictUpSetCtx`, `weakBV_inv_lift`) need either
   producer changes keeping a narrow-context run or a locality theorem for
   fresh checker runs. Estimated total 3k to 12k lines depending on route.
   **Decision (Kim, 2026-10-06): try both routes in parallel and keep the one
   that reaches the end.** E1 is developed on branch
   `agent/verify-inductives-e1` (worktree `../lean4lean-e1`): scoped caches
   and `EquivManager`, binder always opened in `isDefEqLambda`/`isDefEqForall`,
   Primitive gadget pieces re-checked in the empty context; success criteria
   are a full build with no `weakN_iff`-family use under the checker, Primitive
   and `ConditionallyTyped`, the cache-scope experiment now rejected by the
   Lean4Lean checker, and fresh `Init.Prelude`/`Init.Core` replays with
   timings against the unmodified branch. E3 is developed on
   `agent/verify-inductives-e3` (worktree `../lean4lean-e3`): `VEnv.Strengthening`
   replaces the sorry as an explicit hypothesis threaded to `addDecl.WF`,
   quantified over exactly the intermediate environments each declaration kind
   uses (the output environment's strengthening is never claimed). The nested
   junction work continues on `agent/verify-inductives` and is merged into
   the surviving route afterwards.
   **E1 status (2026-10-06):** checker cluster done on `agent/verify-inductives-e1`
   (commits be54d43, 000dbcc, 758bb60): `State.leaveScope` restores the infer,
   whnf, failure caches and the `EquivManager` at every `withFreshId` scope
   (keeps `ngen`, `unfold`); `isDefEqLambda`/`isDefEqForall` always open a
   binder; `Condition.check` re-checks the gadget pieces at `[]`;
   `unfoldNatWellFounded` re-checks `F` in the outer context. No
   `weakN_iff`-family use remains under `Verify/TypeChecker`,
   `ConditionallyTyped`, `Primitive`; the checker still reaches `weakN_iff`
   only through `VExpr.WF.of_occurs`, `VIotaRuleShape.args_typing`,
   `TrExprS.weakBV_inv₁` (class (b), being repaired) and the inductive side.
   The cache-scope experiment is now rejected by the Lean4Lean checker.
   Replays check the same declaration counts; cost: `Init.Core` unchanged,
   `Init.Data.List.Lemmas` +21%, `Std.Data.HashMap.Lemmas` 26.6 s to 49.0 s
   (+84%), inherent to discarding in-scope cache entries.
   **E1 Theory routes (2026-10-06):** `VExpr.WF.of_occurs` replaced by
   `of_occurs_lift` (keeps the enclosing binders), `VIotaRuleShape` gained
   `rec_doms`/`ctor_doms` proved at every producer, the projection walk
   substitutes the projection for non-dependent fields. One corner remains:
   a Prop structure with an earlier non-dependent DATA field (the C++
   `infer_proj` skips the binder without a sort check): the proof must
   translate the later field's type without the data binder. The general
   statement `ProjectionFieldCorner` is FALSE (Astra: add `D : Type`,
   `out : D → P v`, `z : SI`, `f : SJ → Prop` to the countermodel context;
   under `d : D`, `out d : P v` makes `f z` typable). The restricted
   obligation (registered telescope, typed major) is plausible, since
   eliminating the Prop structure into Prop recovers `P v`, but no syntactic
   inhabitant of the data field exists, so it is being threaded as an
   explicit hypothesis to the top-level theorems on the E1 branch. E1 is
   therefore not hypothesis-free either. Done as `ProjectionWalkCorner`
   (`Verify/Typing/ProjectionCorner.lean`, commit 02ea245 on the E1 branch),
   quantified over every well-formed environment; being converted from a
   `VEnvs.WF` field (which would hide it) into an explicit argument of the
   top-level theorems. With it, no constant under the checker, Primitive,
   ConditionallyTyped or EquivManager depends on `weakN_iff`; `addAxiom`,
   `addDefinition`, `addTheorem`, `addOpaque`, `addMutual` are clean; the
   inductive side (25 sites) remains.
   **E1 inductive side, steps 0 to 2 done (45d7f7e, pushed):** Step 0 local
   fixes and deletions of unused false lemmas; Step 1 executable: a second
   local context `Context.checkLCtx` seen only by the lifted checker calls
   (18 binders marked "checker context narrowed"; parameters, indices,
   fields, positivity/`isRecArg`/`loopUArgs` binders in both contexts;
   majors, motives, minors, hypotheses only in the main one; closed header
   `whnf` and `isLargeEliminator` under `{}`); replays match baseline counts
   (`Init.Prelude` 1975, `Init.Core` 3953, `List.Basic` 5521, `Array.Basic`
   7894, `Format.Basic` 7084), 2 to 17% slower. Step 2 plumbing: `ContextWF`
   /`RecursorContextWF`/`StagedContextWF` gain `checkMapWF`, `checkSub` and a
   TRANSITIONAL hypothesis `CheckerSubContextLocality` (a successful lifted
   checker run in the narrow context succeeds with the same value in the
   full context), because the main-context lift lemmas cannot be weakened
   corollaries of narrow ones until Steps 3 to 6 make every lifted run
   narrow. It had been hidden in `Declaration.IsModelled`; being made an
   explicit argument of the top-level theorems together with
   `ProjectionWalkCorner`. **Done (4ba46b2, pushed):** `addDecl.WF` on E1 now
   reads `(wf) (hcorner : ProjectionWalkCorner) (hloc :
   CheckerSubContextLocality) (decl) (hdecl)`; `IsModelled` is `False` for
   `quotDecl` and `True` otherwise; the checker cone is free of `weakN_iff`;
   25 inductive-side sites remain (LoopType 7, Verify/Typing/Lemmas 4,
   Basic 2, twelve files with one each). Steps 3 to 6 (per-phase
   narrow-scope proofs, deleting `hloc`) in progress after merging main.
   **E3 status (2026-10-06): complete on `agent/verify-inductives-e3`**
   (commits 7c544ac..717fc23, pushed): `VEnv.Strengthening` replaces the
   `weakN_iff` sorry; threaded through the Theory consumers, a new
   `VContext.strengthening` field, `ContextWF`/`RecursorContextWF`, and
   result structures. `addDecl.WF` gains `(hs : decl.Strengthening ves env)`
   with `Declaration.Strengthening` per kind: axiom/theorem/opaque: the
   checking environment; definition: the safe environment, or the unsafe one
   plus the definition as an axiom; mutual: headers environment and its
   extension by the translated headers; quot: nothing; inductive:
   `InductiveStrengthening` of the source declaration and of the executable's
   nested lowering result, each covering the base, plus type headers, plus
   constructors, plus projection entries, plus the recursor constants added
   as axioms. Full build, tests and fresh `Init.Prelude`/`Init.Core` replays
   pass; executable unchanged. Four legacy theorems outside the `addDecl.WF`
   cone take a coarser hypothesis quantified over every `ContextWF` with the
   same Lean environment. The output environment's strengthening is never
   claimed. Comparison so far: E3 reached a buildable state with a true
   statement, which is NOT the same as being the right route: its
   hypothesis `Declaration.Strengthening` is of unknown truth for real
   (prelude-derived) environments, and if false there the theorem is vacuous
   for real replays (Astra consulted, 2026-10-06). E1 has the checker
   cluster and Theory routes done, carries a restricted projection-corner
   hypothesis (plausibly true), an executable divergence, a replay slowdown,
   and the inductive-side narrow-context change (4.5k to 9k lines) still
   ahead. E3 has absorbed the nested work (merge d923f9f, clean). **Astra
   (2026-10-06): the countermodel collapses once canonical `Eq` is present**
   (`extract p : P v` by `I.rec` with an `Eq.rec` motive, checked; see
   STRENGTHENING.md's last section), so E3's hypothesis is not known false
   for prelude-derived environments; strengthening in environments with
   canonical equality is an open conjecture. E1 additionally covers the
   `Eq`-free bootstrap prefix.
   **E1 inductive side (design, 2026-10-06, `docs/inductives/E1_INDUCTIVE_DESIGN.md`):**
   79 strengthening uses under `Verify/Inductive` strengthen fresh checker
   runs from the nested context of `Inductive/Add.lean` (later families run
   inside earlier families' indices; constructor and recursor phases inside
   stale header indices; later constructors under earlier minors). Chosen
   repair (P): a second local context `checkLCtx` seen only by the lifted
   checker calls (parameters, indices, fields, argument binders in both
   contexts; majors, motives, minors, hypotheses only in the main one), with
   snapshots per parameter and per field; estimated 4.5k to 9k lines of churn
   (much deletion), versus 9k to 16k for a fresh-run locality theorem (L).
   (P) is a second executable departure, invisible if (L) holds (argued, not
   proved). Scoping reports copied to `docs/inductives/WEAKN_SCOPE.md` and
   `docs/inductives/RESTORE_READINESS.md`.
3b. **Base sorries (scoped 2026-10-06, `docs/inductives/BASE_SORRIES.md`).**
   None is provable with moderate effort. Injectivity (5) follows from
   confluence in principle but not from the current ChurchRosser development
   (circular: it uses `uniqU`, `forallE_inv`, `sort_inv`, `weakN_iff`); a
   non-circular route is a stratified induction on typing height with new
   head-separation lemmas, roughly 5k to 10k lines. `RecursorLemmas:437`
   needs a rigid-head-versus-Pi separation lemma (then about 60 lines).
   `ChurchRosser:2166` is `NormalEq.headParallel` (not the eta/eta case);
   the eta/eta case of `NormalEq.trans` uses the false `weakN_iff` through
   `NormalEq.weakN_inv_DFC` and can be replaced only by re-indexing
   `NormalEq` with a Nat bound and an `etaBoth` constructor (about 550 new
   lines plus 800 to 1500 of consumer edits). FullReduction's six sorries
   need spine exposure, two separation lemmas and the full strip proof.
   Branch `agent/verify-inductives-base` (commit 9db09de) narrows the
   projection-iota sorry to the `appDF | etaL` cases. Decision for Kim:
   keep these as documented base conjectures (the branch's standing stance)
   or fund the confluence programme.
4. **Executable hygiene**: literal cost in `guardedIotaCheck`, the `Std`
   replay slowdown, and a review of every runtime rejection added in
   `Inductive/Add.lean` (grep `throw <| .other` in the diff against
   `origin/master`) against Lean-accepted declarations beyond `Init`/`Std`.
   `checkIndexUniverses` is gone (its fact is now proved, see the universe
   un-shift entry under item 7 above).
5. **Audit discipline.** `scripts/check-inductive-audit.py` roots
   `full_church_rosser`, `headParallel`, and `NormalEq.fullStep` are outside
   the `addDecl.WF` cone; decide whether they remain goals.
6. **Tests.** `Tests/InductiveTheory.lean` was repaired (the enum `Models`
   instance gained the ninth field `constructorArity`).
   `Tests/RecursorOracle.lean` regenerates `Acc`, `Lean.Order.iterates`,
   `Nat`, `List`, `Prod`, several nested inductives, a `TSyntax`-field nested
   type and a multi-binder higher-order predicate through `Lean4Lean.addDecl`
   and compares every recursor (type, metadata, rule RHSs) with Lean's, and
   pins `Expr.abstract`'s behaviour on loose bvars. Still missing: a test
   exercising the first-pass/minor fvar-id collision directly, and a
   large-literal guard test.

## Source map

| Question | Entry points |
| --- | --- |
| Final contract | [Verify/Environment.lean](Lean4Lean/Verify/Environment.lean) (`addDecl.WF`), [Run/FinalResult](Lean4Lean/Verify/Inductive/Run/FinalResult.lean), [Run/SemanticSpecification](Lean4Lean/Verify/Inductive/Run/SemanticSpecification.lean) |
| Generative specification | [Theory/Inductive.lean](Lean4Lean/Theory/Inductive.lean) (`VInductDecl.WF`), [Theory/Inductive/](Lean4Lean/Theory/Inductive/) |
| Base open lemmas | [Injectivity](Lean4Lean/Theory/Typing/Injectivity.lean), [UniqueTyping](Lean4Lean/Theory/Typing/UniqueTyping.lean), [RecursorLemmas](Lean4Lean/Theory/Typing/RecursorLemmas.lean) |
| Abstraction models and axioms | [Verify/Axioms.lean](Lean4Lean/Verify/Axioms.lean), [Verify/LocalContext.lean](Lean4Lean/Verify/LocalContext.lean) |
| Recursive-call verification (exact model) | [Recursor/RecursiveCalls.lean](Lean4Lean/Verify/Inductive/Recursor/RecursiveCalls.lean), [Recursor/Rules.lean](Lean4Lean/Verify/Inductive/Recursor/Rules.lean), [Recursor/SecondPass.lean](Lean4Lean/Verify/Inductive/Recursor/SecondPass.lean) |
| Executable recursor construction | [Inductive/Add.lean](Lean4Lean/Inductive/Add.lean) (`loopUBlueprints`, `RecCallBlueprint.build`, `validateRestoredRecursorRules`) |
| Strengthening countermodel | [STRENGTHENING.md](docs/inductives/STRENGTHENING.md) |

## Evidence and commands

- Dependency audit of `addDecl.WF`: now a permanent root of
  `scripts/InductiveAudit.lean`; result listed above (exactly the 10 sorries
  of item 1; `abstract_eq_legacy` is gone; axioms are the inventory's
  implementation axioms including `abstractN_eq`).
- Executable oracle: regenerate an inductive through `Lean4Lean.addDecl` on a
  renamed copy and compare `RecursorVal`s with Lean's; `lake env
  .lake/build/bin/lean4lean Init` (25 "already declared" artifacts, same as
  upstream), `… Std` (6, same as upstream), `--fresh Init.Prelude`,
  `--fresh Init.Core`.
- After adding `recursorTypes` (2026-10-05): `lake build` (629 jobs) and
  `python3 scripts/check-inductive-audit.py --self-test` pass.
- `lake build` (default targets), `lake build Lean4Lean.Tests`, the fresh
  `Init.Prelude` (1975 declarations) and `Init.Core` (3953 declarations)
  replays, and `python3 scripts/check-inductive-audit.py --self-test` all
  pass at this state (2026-10-05, after removing the false bridge);
  `--require-complete` fails only on the 10 reachable open obligations of
  item 1 (plus the Church-Rosser roots outside the `addDecl.WF` cone).

Final acceptance still requires: `lake build`, `lake build Lean4Lean.Tests`,
fresh `Init.Prelude` and `Init.Core` replay,
`python3 scripts/check-inductive-audit.py --self-test` and `--require-complete`,
and a review of the final theorem hypotheses. Preserve the toolchain
`leanprover/lean4:v4.33.0-rc2`; add no axioms; do not hide proofs behind
supplied semantic answers; do not add runtime rejections to ease proofs.
