# docs/inductives: index

Documents of the inductive-verification work on `agent/verify-inductives`. The current account
is [HANDOFF.md](../../HANDOFF.md). "Current" files are rationale for the proof as it stands or
for active work; files under [history/](history/) describe superseded routes and are kept only
as a record. No file here is part of a lake target; the `.lean` files are run individually with
`lake env lean <path>`.

## Current

- [GOAL.md](GOAL.md): the standing goal of the branch and Kim's amendments of 2026-10-08.
- [PHASE1_NOTES.md](PHASE1_NOTES.md): Phase 1a, the shape model and decisions D1 to D17 (the shape model is being removed from the proof; the specification decisions stand).
- [PHASE1B_NOTES.md](PHASE1B_NOTES.md): Phase 1b, the observation model proving head injectivity (and separation).
- [E1_INDUCTIVE_DESIGN.md](E1_INDUCTIVE_DESIGN.md): scoped caches on the inductive side, the corner discharge, and the specification corrections of section 5.4.
- [CacheScopeExperiment.lean](CacheScopeExperiment.lean): why the checker's caches must be scoped to binders.
- [CORNER_ASTRA_REVIEW.md](CORNER_ASTRA_REVIEW.md): review of a choice-free proof of the projection-walk corner.
- [STRENGTHENING.md](STRENGTHENING.md): the countermodel to strengthening without canonical `Eq`.
- [STRENGTHENING_NOTES.md](STRENGTHENING_NOTES.md): strengthening with canonical `Eq`; reference for the active research branch `agent/verify-inductives-strengthening`.

## History

- [history/HANDOFF-chronicle.md](history/HANDOFF-chronicle.md): the chronological record formerly in HANDOFF.md.
- [history/BASE_OBLIGATIONS_DESIGN.md](history/BASE_OBLIGATIONS_DESIGN.md): design for the base obligations (head inversion, strengthening, confluence) before they closed.
- [history/BASE_SORRIES.md](history/BASE_SORRIES.md): scope and plan for the base sorries of the former base branch.
- [history/WEAKN_SCOPE.md](history/WEAKN_SCOPE.md): scoping report for replacing `IsDefEqU.weakN_iff`.
- [history/RESTORE_READINESS.md](history/RESTORE_READINESS.md): the Expr-level obligation of nested restoration.
- [history/PHASE1_SPIKE.md](history/PHASE1_SPIKE.md): the Phase 1 spike; obstruction for the shape logical relation.
- [history/PHASE1_SPIKE_README.md](history/PHASE1_SPIKE_README.md): the spike's README from `Lean4Lean/Experimental/Spike/` (the spike text plus a Phase 1a update note).
- [history/PHASE1B_ASTRA_REVIEW.md](history/PHASE1B_ASTRA_REVIEW.md): review of the candidate routes for Phase 1b.
- [history/STRENGTHENING_ASTRA_REVIEW.md](history/STRENGTHENING_ASTRA_REVIEW.md): first review of the strengthening proof design.
- [history/STRENGTHENING_ASTRA_REVIEW2.md](history/STRENGTHENING_ASTRA_REVIEW2.md): review of the certificate architecture.
- [history/STRENGTHENING_ASTRA_REVIEW3.md](history/STRENGTHENING_ASTRA_REVIEW3.md): review of termination of certified transitivity.
- [history/STRENGTHENING_LITERATURE.md](history/STRENGTHENING_LITERATURE.md): literature survey on strengthening.
- [history/StrengtheningFalsification.lean](history/StrengtheningFalsification.lean): plain-Lean evidence for the strengthening falsification study.
- [history/SingletonStrengthening.lean](history/SingletonStrengthening.lean): source admissibility of the strengthening countermodel.
- [history/SingletonStrengtheningModel.lean](history/SingletonStrengtheningModel.lean): semantic calculations for the countermodel.
- [history/COUNTERMODEL_FEASIBILITY.md](history/COUNTERMODEL_FEASIBILITY.md): feasibility of a machine-checked refutation of `weakN_iff`.
- [history/COUNTERMODEL_STATUS.md](history/COUNTERMODEL_STATUS.md): status of the parked countermodel `Theory/Typing/Countermodel/`.
- [history/FOUNDATION-COMPARISON.md](history/FOUNDATION-COMPARISON.md): research diary of earlier foundation investigations.
- [history/RECORD-ETA-COVERAGE.md](history/RECORD-ETA-COVERAGE.md): record eta and source coverage in an abandoned source grammar.
- [history/FIELD_ADEQUACY.txt](history/FIELD_ADEQUACY.txt): audit of the former field-type adequacy lemma.
- [history/RIGID_ADEQUACY.txt](history/RIGID_ADEQUACY.txt): audit of the former rigid-application adequacy lemma.
- [history/LegacyMetadataCounterexample.lean.txt](history/LegacyMetadataCounterexample.lean.txt): counterexample to an earlier recursor-metadata specification (does not elaborate on the current tree).
- [history/LegacyNestedCounterexample.lean.txt](history/LegacyNestedCounterexample.lean.txt): counterexample to an earlier nested-inductive specification (does not elaborate on the current tree).
- [history/BudgetStratificationObstruction.lean](history/BudgetStratificationObstruction.lean): termination obstruction for a budget-indexed foundation.
- [history/OneSidedBudgetObstruction.lean](history/OneSidedBudgetObstruction.lean): non-transitivity of a one-sided budgeted simulation.
- [history/DependentSingletonObstruction.lean](history/DependentSingletonObstruction.lean): the singleton reconstruction obstruction.
- [history/TypedObservationChildMismatch.lean](history/TypedObservationChildMismatch.lean): observer types do not determine application children.
- [history/TypeIndexCaptureObligation.lean](history/TypeIndexCaptureObligation.lean): a singleton family with a repeated type index.
- [history/EtaResidualObligation.lean](history/EtaResidualObligation.lean): the eta/beta/native overlap repair.
- [history/StratifiedUniverseObligation.lean](history/StratifiedUniverseObligation.lean): obstruction to the former stratified field retyping bound.
- [history/ProofRetypingObligation.lean](history/ProofRetypingObligation.lean): missing typing obligation of a proposed proof-opacity construction.

The history `.lean` files import modules as they were when written; some may no longer
elaborate against the current tree.
