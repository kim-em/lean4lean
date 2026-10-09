# Direction C log: the counterexample hunt under canonical `Eq`

Branch `agent/verify-inductives-strengthening3-C`. Plan: section 3.C of
`STRENGTHENING_ATTEMPT_2026-10-09b.md`. Library files: `Lean4Lean/Theory/Typing/Strengthening/
Candidates.lean` (the checked ledger, namespace `VEnv.StrengtheningCandidates`), then
`Hunt.lean` (the typing gap and the rigid-binder analysis).

## 1. Mechanism ledger (round 7, integrated)

| mechanism | theorem | verdict |
|---|---|---|
| K on an unaligned cast | `cast_identity_iff`, `unaligned_cast_not_identity`, `unaligned_spine_check_impossible` | the cast computes iff the endpoints are already aligned in the same context; a hypothesis `q : X = Y` aligns nothing |
| aligned cast | `aligned_cast_below`, `aligned_cast_above` | computes below with an `Eq.refl` proof whenever it computes above |
| Prop-source quotient | `quotient_source_cannot_be_missing`, `quotient_source_cancel` | the major supplies an inhabitant of `Q` below (`Quot.ind`), so the instance is inhabited |
| quotient prefix | `quotient_prefix_below`, `quotient_prefix_above` | holds below when the prefix is typed below |
| singleton proof field | `proof_major_join`, `singleton_cast_extractor_exists` | the field is extracted below from a major typed below (cast telescope, `PropElim.value_typed`) |
| unit-like, structure eta | `unit_below/above`, `structure_eta_below/above`, `common_retyping_requires_alignment`, `shared_middle_forces_type_agreement` | hold below when the subjects are typed below; retyping above forces type agreement above |
| blocked definitions | `definition_equation_below/above`, `detour_eq` | stored equations have no local guard; the beta detour is reflexive below |
| universe identities | `universe_gate_impossible`, `sort_front` | no context aligns distinct levels; sort equations descend |
| support invariant | `no_support_invariant`, `wellformed_support_obstruction` | not preserved (beta detour) |
| occurrence parity | `no_occurrence_parity_invariant` | not preserved (beta detour) |
| remaining obligation | `UninhabitedCancel`, `uninhabitedCancel_iff_cancel` | `Cancel` for uninhabited binders, equivalent to `Cancel` |

All theorems check with axioms among `propext`, `Classical.choice`, `Quot.sound`
(`scratch/CandidatesAxioms.lean`).

## 2. Log

* 2026-10-09: worktree read; `Candidates.lean` created from the round 7 ledger, built, axioms
  checked.
