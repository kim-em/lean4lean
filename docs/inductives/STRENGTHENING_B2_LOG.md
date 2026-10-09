# Direction B2 log: `TypedFront → Cancel` through local replay

Branch `agent/verify-inductives-strengthening3-B2` (worktree `lean4lean-strength3-B2`), off
`agent/verify-inductives-strengthening3` at c8fa311e. Plan: `STRENGTHENING_ATTEMPT_2026-10-09b.md`
section 5 (Astra round 9) and the designer's brief: prove or reduce exactly
`TypedFront env → Cancel env` under `WF` and `HasCanonicalEq`, by replaying the steps of an
exposure path above as steps below, discharging guards with `TypedFront`. Every entry records an
attempt and its outcome; files under `Lean4Lean/Theory/Typing/Strengthening/` are at zero `sorry`
in every commit.

## Step 1: `Strengthening/Replay.lean` (Astra round 9, adapted)

* Namespace `Lean4Lean.VEnv.StrengtheningReplay`, imports `TypingFront`, `Hunt`,
  `HeadReduction`. Names kept: `typeFrontN_of_typeFront`, `typeFrontN_iff_typeFront`,
  `typeFrontN_iff_typedFront`, `piExposureRed_iff_piExposure`, `retyping_of_typeFrontN`,
  `typedFront_independent_endpoints`, `cancel_iff_typedFront_and_closures` (the exact formulation
  `Cancel ↔ TypedFront ∧ AppFrontN ∧ ProjFrontN ∧ ElimFrontN`), `cancel_of_typedFront_and_exposure`,
  `core_exposure_standard`, `whnf_proj`, `projection_has_no_core_head_exposure`,
  `projection_full_exposure`, `type_not_function`, `type_not_structure`,
  `saturated_projection_replay`, `HeadStep`, `HeadStep.full`, `LocalReplay` (Astra's `HeadReplay`,
  stated as a `def`), `HeadStandard`, `head_path_replay`, `piExposureRed_of_head_interfaces`.
* Build: `lake build Lean4Lean.Theory.Typing.Strengthening.Replay` succeeds. Axiom audit
  (`scratch/ReplayAxioms.lean`, `lake env lean`): only `propext`, `Classical.choice`,
  `Quot.sound`; no `sorryAx`.
