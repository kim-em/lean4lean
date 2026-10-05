# Inductive verification: purpose, evidence, and remaining work

Current account, 2026-10-05, branch `agent/verify-inductives`.
This is the single maintained handoff and plan. Update it in place; do not
append checkpoint diaries or turn temporary agent coordination into policy.
The source and checked theorem types take precedence over this account.

## Intended result

Finish the executable Lean4Lean inductive checker's refinement of an
**independent generative specification**, following Mario's intended treatment
of ordinary, primitive, mutual, higher-order, indexed, and nested inductives.
The final result must include dependent projections and structure eta, exact
recursor metadata and equations, and complete proofs without sorries.

The specification must determine artifacts from declarations, not certify
whatever the executable happened to produce:

- Normalized family/constructor signatures generate motives, minors, recursor
  types, recursive calls, and typed equation telescopes and sides. Source
  models use typed equality and retain actual recursive field domains,
  positivity, universe admissibility, and singleton-elimination conditions.
- Ordinary and nested cases share a finite `CompiledInductive` judgment.
  Nested specialization uses earlier certified, installed containers; scoped
  restoration and ordered constructor correspondence determine its outputs.
  Check original source constructors before lowering. Current headers or
  recursors cannot provide their own container justification.
- Final abstract syntax removes primitive `.proj`. Typed `TrProj` desugars
  dependent projections through admissible abstract eliminators, including
  earlier-field substitutions, without relying on `casesOn`. Abstract symbols
  are disjoint from concrete names. Declaration-derived structure eta remains
  a separate equality principle: iota alone does not imply it. Derive unit-like
  equality from eta and proof irrelevance.
- Concrete generation/restoration traces establish exact names, counts,
  parameters, universe arities, ownership, safety, K eligibility, and equations.
  `TrConstVal` alone erases needed metadata. Constructor and recursor parameter
  counts can differ, notably for nested auxiliary recursors.
- Staged refinement relates the source environment, independently justified
  abstract block, and concrete visible prefix, with ownership, freshness, and
  final accounting. Validation cannot assume correctness of its own artifact.
  Preserve primitive formation and Eq/Bool/Nat/quot bootstrapping.

No normalization theorem or set-theoretic consistency model is an additional
project goal. False intermediate statements may need replacement, with their
consumers repaired; the intended final checker guarantees must be preserved.

## Assessment and next decision

**The Anchored foundation is a candidate, not an established solution.** There
is substantial checked conditional infrastructure, but no unconditional global
construction and no basis for a reliable completion percentage. Neither final
specification migration nor complete correctness has been achieved.

Start from the actual final theorem contracts and dependency roots. Assess
whether the present semantics, recursive interfaces, and measures can close
without assuming the conclusions they are meant to prove. Compare continuing
this approach with simplifying or replacing it. Do not preserve it because of
its size, sunk effort, or successful local builds.

Choose the largest unresolved feasibility risk and the smallest decisive
end-to-end theorem or counterexample that tests it. State the hypotheses,
missing producer, and recursive decrease explicitly, then implement that test.
A useful milestone removes a final obligation or settles whether a route can
work. Another conditional wrapper, interface, or clean dependency audit alone
does not establish global progress. Reassess after each such experiment; do
not let architecture discussion become a replacement for proving anything.

Fable's second opinion identified scaffolding without final closure, possibly
circular dependencies, supplied semantic answers, and neglected checker work.
The specific criticism that target adequacy bridges were missing has since
been addressed conditionally. The global-closure criticism remains. Neither
an import of an admitted theorem nor a suggested above-cutoff counterexample
by itself proves failure: inspect actual dependencies and resource conditions.
Audit the intended calculus as well as the proof machinery built around it.

## Checked evidence and its limits

The actual all-budget `WorldBoundedUnaryAt` and `WorldBoundedReplayAt`
interfaces imply the exact sort/Pi inversion targets, including original
stratified bounds, sort/Pi separation, rigid application inversion, field
compatibility, and uniqueness. Initial queries, frames, canonical registry,
and equation strata are constructed. **The interfaces themselves still need
an unconditional producer.** These bridges do not discharge the final holes.

The latest focused checkpoint built 993 jobs successfully. Opaque dependency
audits of these five roots found no sorries and only `Classical.choice`,
`propext`, and `Quot.sound`:

| Root (namespace prefixes omitted) | What the checked component supplies |
| --- | --- |
| `ProjectionHead.priorRawBridgeWorld` | Two genuinely smaller empty assigned-type comparisons and the actual guarded source projection produce the raw projected pair. |
| `RichComputationalValue.projectedSortable` | Paired semantic interpretation and its actual right query from the same major and field answers. |
| `projectionSortableWorldValue` | Actual smaller interpretation calls, restored assigned prefix, certificate control, and right-query fuel; right-query site provenance remains open. |
| `RichFunctionDemandFactor.priorSortableAdmissions` | Sortable code plus the raw pair and field path give admission at the original application's key, retaining its anchor. |
| `ControlledStoredQuery.projectionVariableSortableWorld` | Total physical/charged demand compilation and actual caller-query metadata; a field certificate and typed support are still inputs. |

Local logs: `.lake/inductive-proof-checks/projection-sortable-stopping-final-build.log`
and `.lake/inductive-proof-checks/projection-sortable-stopping-final-audit.log`.
These are focused checks, not a successful full-branch acceptance run.

## Remaining obstacles

1. **An unconditional foundation, or a better replacement.** The current
   approach needs simultaneous closure of F (fundamental interpretation),
   equality, R (expression reindexing), and C (assigned-type comparison).
   Right-substitution frames and hereditary histories must belong to the
   *same returned query and assigned certificate*. Individual binder/capture
   clauses and a reconstruction transcript are not a total producer. Ordinary
   R/C calls require compatible cutoff/fuel; changing frames does not itself
   prove a decrease. Do not identify source and caller controls, substitute a
   new domain/anchor for a frozen request key, or infer syntax from semantic
   `Related`. Every recursive call needs genuine original-derivation bounds.

   The latest candidate experiment is independent dependent-field comparison
   for `S (A) (P)` with fields `a : A` and `b : P a`, hence field type
   `P (proj S 0 m)`. Major comparison, two captures, formal/caller replay, and
   exact family demand have checked components. What remains is composing
   these with the actual caller query, field-support producer, raw pair, and
   original-key admission at the independent-C entry. Arbitrary profiles need
   physical nonsortable requests, sortable charged requests, and grade adapters.
   `RichObs.projectionSortable` preserves the whole retained request separately
   from its final field input. This experiment is an option to evaluate, not a
   mandatory route if the architecture review points elsewhere.

2. **Correct core statements and noncircular dependencies.** The two-singleton
   example in [STRENGTHENING.md](docs/inductives/STRENGTHENING.md) challenges
   unrestricted `IsDefEqU.weakN_iff`, including strengthening at a fixed type.
   Source inference and finite model calculations are checked; full environment
   formation and model soundness are not formalized. Treat the evidence at that
   scope, and repair invalid strengthening uses in eta/cache/translation proofs.
   `ChurchRosser.Params` already depends on uniqueness and inversion, so cannot
   prove them circularly. The measure's current import path through
   `ProjectionLemmas`, `UniqueTyping`, and `Injectivity` needs separation for
   final integration; clean local opaque audits do not solve that organization.

3. **Semantic equation coverage and full reduction.** `FullEquationCoverage`
   remains an unconstructed hypothesis of `full_church_rosser`. Registry
   classification does not establish its reduction joins and `NormalEq`
   conclusions. Construct it from actual installation/typing evidence. Finish
   `NormalEq.headParallel`, `NormalEq.fullStep`, and `FullStep.strip`, with a
   whole finite development for strip, not just local joinability.

4. **Final executable refinement.** Finish canonical recursor consumption and
   equation translation, constructor saturation, nested staged validation and
   assembly, and the dependent-projection/eta consumers. Complete the trace-
   derived metadata and final ordinary/primitive/nested dispatch. Review the
   existing index-universe runtime check: successful Prelude/Core replay did
   not establish compatibility with every Lean-accepted declaration. Do not
   add runtime rejections merely to bypass difficult proofs. Remove superseded
   pipelines once replacements support their consumers. Reassess priorities
   across these independent obligations, not only inside foundation machinery.

The [audit inventory](scripts/inductive-audit-inventory.json) currently names
14 open proofs. This is a dependency inventory, not a certificate that their
statements are true or that no missing hypothesis remains. Inspect theorem
contracts as well as `sorryAx` reachability; an assumed callback or class can
hide the entire intended result while passing an axioms audit.

## Source map

| Question | Entry points |
| --- | --- |
| Independent generation and finite compilation | [Signature](Lean4Lean/Theory/Inductive/Signature.lean), [Compilation](Lean4Lean/Theory/Inductive/Compilation.lean), [CaseSchema](Lean4Lean/Theory/Inductive/CaseSchema.lean), [Restoration](Lean4Lean/Theory/Inductive/Restoration.lean) |
| Actual final contracts | [FinalDispatch](Lean4Lean/Verify/Inductive/FinalDispatch.lean), [Injectivity](Lean4Lean/Theory/Typing/Injectivity.lean), [UniqueTyping](Lean4Lean/Theory/Typing/UniqueTyping.lean) |
| Current recursive interfaces | [Unary bank](Lean4Lean/Theory/Typing/AnchoredOriginalWorldBoundedUnaryCallBank.lean), [replay bank](Lean4Lean/Theory/Typing/AnchoredOriginalWorldBoundedCallBank.lean) |
| Conditional target bridges | `AnchoredOriginalWorld{SortInversion,PiInversion,RigidAdequacy,FieldAdequacy,UniqueTyping}.lean` in `Theory/Typing` |
| Latest candidate composition | `AnchoredOriginalWorld{PriorRawBridge,PriorKeyAdmission,ProjectionSortableComputational,ProjectionVariableSortable,FunctionPriorFieldSupport,TwoParameterMajorDemand,FormalPriorProjectionReplay}.lean` in `Theory/Typing` |
| Full reduction and coverage | [FullReduction](Lean4Lean/Theory/Typing/FullReduction.lean), [FullChurchRosser](Lean4Lean/Theory/Typing/FullChurchRosser.lean) |
| Focused obstruction evidence | [STRENGTHENING.md](docs/inductives/STRENGTHENING.md) and the accompanying `.lean` witnesses in `docs/inductives` |

Other research notes under `docs/inductives` are historical or focused evidence,
not competing plans. Read them when a specific claim needs checking, not as a
required sequence of attempted designs.

## Completion and working discipline

Preserve inherited dirty/untracked work and unrelated edits. Keep the existing
toolchain (`leanprover/lean4:v4.33.0-rc2`). Do not
introduce new axioms, hide unfinished proofs behind supplied semantic answers,
or weaken intended final guarantees. Correct false helper statements and their
consumers instead. Add tests only to settle the active proof/design question
or directly validate a necessary implementation change.

Final acceptance requires the complete proofs and specification review, then:

```sh
lake build
lake build Lean4Lean.Tests
lake env .lake/build/bin/lean4lean --fresh Init.Prelude
lake env .lake/build/bin/lean4lean --fresh Init.Core
python3 scripts/check-inductive-audit.py --self-test
python3 scripts/check-inductive-audit.py --require-complete
```

Existing targeted checks cover auxiliary recursor reduction, higher-order,
mutual and nested indexed declarations, dependent projections/eta, universe
specialization, K/singleton and forbidden eliminations, primitive preservation,
and malformed metadata/equations. Use these to validate the final implementation.
The auditor follows types and opaque bodies; retain its strict definition-root
checks and existing explicit implementation-axiom boundary. A passing audit
must accompany, not replace, review of final theorem hypotheses.
