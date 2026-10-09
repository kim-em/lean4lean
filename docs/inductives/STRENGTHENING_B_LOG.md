# Direction B log: term model integration and typing strengthening under uninhabitedness

Branch `agent/verify-inductives-strengthening3-B` (worktree `lean4lean-strength3-B`), off
`agent/verify-inductives-strengthening3` at ebdab07c. Plan: `STRENGTHENING_ATTEMPT_2026-10-09b.md`
section 3.B. Every entry records an attempt and its outcome; files under
`Lean4Lean/Theory/Typing/Strengthening/` are at zero `sorry` in every commit.

## Step 1: `Strengthening/TermModel.lean` (Astra round 7, adapted)

* Namespace `Lean4Lean.VEnv.StrengtheningTermModel` (was `Round7TermModel`); every name kept.
  Imports `Strengthening/Kripke.lean`.
* Added `UninhabitedCancel` and `uninhabitedCancel_iff_cancel` (from `round7/counterexample/
  Round7.lean`) at the end of the file, same namespace.
* Module docstring: `TermEq` is the least typed equivalence congruence; its transitivity is a
  constructor; `termEq_iff_join` is `WF.church_rosser` (packaging, not a solution);
  `Reflection ↔ Cancel`; stuck heads separated by name (`opaque_separated`, `loops_separated`);
  `bad_join_not_descending` and `bad_join_repaired`.
* Build: `lake build Lean4Lean.Theory.Typing.Strengthening.TermModel` succeeds. Axiom audit of
  all 39 declarations (`scratch/TermModelAxioms.lean`, run by `lake env lean`): only `propext`,
  `Classical.choice`, `Quot.sound`; no `sorryAx`.

## Step 2: `UninhabitedTypingFront`

(entries follow)

### 2.1 Course correction (Astra review 6, round 8) and step 2(a)

Before any Lean was written for 2(a), my own analysis reached: `Cancel → UninhabitedTypingFront`
trivially; `UninhabitedTypingFront → TypedFront` (Kripke's fixed-type front) by encoding an
equation as the typing `Eq.refl a : Eq A a b` and reading it back below with unique typing and
rigid-head injectivity of `Eq`; the only thing I could not supply was `env.Rigid ``Eq` from
`HasCanonicalEq` alone (a definitional `Eq` is not excluded by the constants clause). Astra's
round 8 (`strengthening-context/round8/design_check/Round8.lean`, checked) has exactly this
argument with `ascribe e A := (λ x : A. x) e` for fixed-type descent and derives `Rigid ``Eq`
from `WF.installed_constructor_result_rigid` on the installed `Eq.rec` rule. Adapted into
`Strengthening/TypingFront.lean` (namespace `VEnv.StrengtheningTypingFront`, names kept):
`TypingFront`, `UninhabitedTypingFront`, `typingFront_of_uninhabited`, `ascribe`,
`ascribe_typed`, `ascribe_inv`, `fixed_typingFront`, `canonicalEq_rigid`, `eqApp_injective`,
`cancel_of_typingFront`, `uninhabitedTypingFront_iff_cancel`, `not_cancel_iff_typing_gap`;
the head-exposure counterexample (`badDomain`, `badEta`, `arbitrary_Q_eta`, `headType`,
`headTypeBad`, `headType_typed`, `headType_bad_reduct`, `headSource`, `headSource_typed`,
`headSource_bad_path`, `arbitrary_Q_eta_repaired`, `fixed_type_eta_peak`); `derived_proof_irrel`,
`derived_proof_mentions_q`, `rigid_q_not_proof`; the open `UninhabitedPiExposure`. The pilot
section of Round8 (direction A material) is not adapted. Axiom audit of all 22 declarations
(`scratch/TypingFrontAxioms.lean`): no `sorryAx`.

Consequence for the plan: the designer's expected gap `G` ("join repair as well") is empty under
canonical `Eq`; `UninhabitedTypingFront` IS `Cancel`. Step 2(b), proving it, is the whole problem.
