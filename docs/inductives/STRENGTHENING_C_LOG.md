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

## 2. The typing gap and the rigid binder (`Hunt.lean`, namespace `VEnv.StrengtheningHunt`)

Organising statement (Astra, round 8, `not_cancel_iff_typing_gap`): `Cancel` fails iff some
`q`-free term is typable in `Q :: Γ` and at no type in `Γ`, with `Q` uninhabited in `Γ`.

| mechanism | theorem | verdict |
|---|---|---|
| `q`-free `t` typed above at a lifted type `A↑`, typed below at `T` | `retyping_gap`, `typing_gap_is_type_cancel`, `typing_gap_cases` | `T↑ ≡ A↑` above; if `t` is not typed below at `A`, `(T, A)` is a type-level `Cancel` failure between types typed below; so a gap at `Q↑` is an inhabitant of `Q`, a term typable at no type below, or a type-level failure |
| cast into `Q` along `e : M = Q` | `cast_into_binder_inhabits`, `cast_source_cancel` | inhabits `Q` below; the instance is the inhabited one |
| `q` as a proof | `binder_proof_iff_level` | iff the sort level of `Q` is `≈ 0`; `¬ u ≈ 0` is not `IsNeverZero` (`param_nonzero_not_neverzero`), but `≈ 0` is what `proofIrrel` needs at the given parameters |
| rigid binder, bare `q` | `rigid_binder_not_proof`, `rigid_binder_not_function`, `rigid_binder_not_struct` | never a proof, a function, or a structure inhabitant |
| rigid binder, derived proof `f q` | `derived_proof_irrel` (Astra), `derived_proof_typed`, `prop_binder_transfer` | every Prop-binder instance `P :: Γ ⊢ a↑ ≡ b↑` is a `Q`-binder instance over `(Q → P) :: Γ`, for any `Q` |
| `RigidCancel` as a partial result | `RigidCancel.prop_to_pi`, `Cancel.rigidCancel` | `RigidCancel` turns every Prop-binder instance into a `Π`-binder instance in the same context; the rigid case contains the derived-proof mechanism of the Prop case; harmless exactly when `P` is inhabited below (`transfer_inhabited`) |
| gap at an application node | `app_gap` | with function and argument typed below and the function type a `Π` below, the exposed domain and the argument type agree above; agreement below types the application below; the open piece is `Π`-exposure below (Astra's `UninhabitedPiExposure`) |
| gap at a rigid type (`structEta`, `unitLike` subjects typed only above) | `rigid_type_gap_args` | descends to pairwise argument conversions above |
| derived proof `f' q` as a singleton field (the extra-index variant of the 5.1 countermodel) | `derived_field_join` | the join above through `mk (f' q)` has the twin below through `mk h₀` for any `h₀ : P` typed below, which `singleton_cast_extractor_exists` supplies from a major typed below for any index values; the inhabitant that matters is of the field type `P`, not of `Q` |
| derived proof as a middle between `q`-free terms typed below | `derived_proof_middle` | forces type alignment with `P` above; proof irrelevance below when aligned below |
| fresh axiom types | `axiomEnv_exists`, `AxiomEnv.wf`, `AxiomEnv.canonicalEq`, `AxiomEnv.rigid`, `AxiomEnv.no_projections` | rigid non-proposition binders exist in every extension |

## 3. Log

* 2026-10-09: worktree read; `Candidates.lean` created from the round 7 ledger, built, axioms
  checked.
* 2026-10-09: `app_gap`, `rigid_type_gap_args`, `derived_field_join`, `derived_proof_middle`
  added (sections 5 and 6 of `Hunt.lean`).
* 2026-10-09: designer's course correction (Astra review 6, round 8): the search target is the
  typing gap at any type, not at `Q↑`; derived proofs `f q` are a third base of `q`-dependence;
  `¬ u ≈ 0` versus `IsNeverZero`. `Hunt.lean` written: typing-gap reduction, binder sort,
  rigid-binder facts, the transfer theorem and `RigidCancel.prop_to_pi`, fresh axiom types.
