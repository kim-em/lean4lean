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

### 2.2 The structural induction and its exact residue (part 2 of `TypingFront.lean`)

Decision: do the induction in the `Ctx.LiftN 1 k Γ Γ'` form (`TypingFrontN`), not the front form:
the `λ`/`Π` body cases move the inserted binder to depth `k+1`, and no context-exchange lemma
exists in the library. `TypingFrontN ↔ TypingFront ↔ Cancel` under canonical `Eq`
(`typingFrontN_iff_cancel`; the converse direction is `Strengthening.of_cancel`).

Checked (`typingFrontN_iff_closures`): `TypingFrontN ↔ AppFrontN ∧ TypeFrontN ∧ ProjFrontN ∧
ElimFrontN`. The right-to-left direction is the structural induction on the term
(`typingFrontN_of_closures`); each closure is necessary, the three application-shaped ones
trivially and `TypeFrontN` through the ascription `(λ x : Π B. B↑. x) (λ x : A. x)`
(`TypeFrontN.of_typingFrontN`). Per case:

* `bvar`, `sort`, `const`: close unconditionally (`Lookup.of_liftN`, `sort_inv`, `const_inv`).
* `lam A b`, `forallE A B`: the induction hypothesis types `A` below at some `T`; one needs
  `A : sort u` below, i.e. `T ≡ sort u` below from `T↑ ≡ sort u` above. This is `TypeFrontN`
  (a `Front` instance between two lifts, `T↑` and `(sort u)↑`), packaged as `TypeFrontN.sort`.
  So even the application-free fragment is blocked, by the *type of the domain*, not by the body.
* `app f a`: the induction hypotheses give `f : F`, `a : A₀` below; `F↑ ≡ Π A B` above. Needed:
  (i) `F ≡ Π A₁ B₁` below for some `A₁ B₁` (`PiExposureN`) and (ii) `A₀ ≡ A₁` below from
  `A₀↑ ≡ A₁↑` above (`TypeFrontN`). `AppFrontN.of_piExposure` checks (i) ∧ (ii) → `AppFrontN`.
  (i) is not reducible to `TypingFrontN` by any encoding I can see: a lifted term whose
  typability forces `F ≡ Π _ _` must apply something of type `F` to an argument typable below at
  a type whose lift is convertible to the domain `A` above, which presupposes (i)
  (`AppFrontN.piExposure` is exactly the restricted converse).
* `proj`, `elim`: `ProjFrontN` (spine exposure of the major's type plus typing of the field type
  below) and `ElimFrontN` (the closed generic type `type.instL ls` is typed above; it is a closed
  term, not a subterm, so the induction gives nothing; the library has no lemma typing generic
  types in `[]`, only `WF.eliminator_genericType_closed`).

Reduction form: `exposure_reduces` (a type convertible to a `Π` reduces to a `Π`; needs the new
`Π`-stability lemmas `parRed_forallE_inv`, `fullStep_forallE_inv`, `fullReduction_forallE_inv`
and `normalEqN_forallE_inv_r`, the latter three using the sort typing of the `Π` to exclude
`structEta`, `funEta`, `etaL`/`etaBoth` and `proofIrrel`), `PiExposureRedN` and
`PiExposureN.of_red`, `cancel_of_piExposureRed`. `piExposure_of_descending`: a `DescendingStep`
path exposes below; `headSource_path_not_descending`: Astra's path is not descending.

Stuck heads (step 2(d)): `stationary_type_not_pi` (a stationary non-`Π` type is never
convertible to a `Π`), `rigid_type_not_pi` (opaque types, `rigidApp_forallE_inv` with no
arguments), `loop_not_pi` (the self-looping `L₁` of `LoopEnv`, through `toAxioms` and
`rigid_of_fresh`, with `loopEnv_onCtx_toAxioms` transporting the context). So exposure never
passes through an opaque constant or a self-loop; they enter the problem only through
`TypeFrontN`/`TermEq` separation, not through exposure.

Build clean; axiom audit of all 57 declarations: no `sorryAx`.

### 2.3 Fragments that close (step 2(c)) and the eliminator closure (part 3)

* `SortSkeleton` (sorts, `Π` over skeletons): closed and context-free. `SortSkeleton.hasType_of`
  (sort typing transfers between any two well-formed contexts), `typeFrontN_skeleton` (type
  front between skeletons, by induction with `sort_inv`, `sort_forallE_inv`, `forallE_inv`).
* `typingFrontN_skeletonFragment`: typing front, no hypothesis on `env`, for `bvar`, `sort`,
  `const`, skeletons, and `λ` over fragment bodies with skeleton domains. Attempted extensions and
  the blocking rule: `λ`/`Π` with a non-skeleton domain `A` (the induction hypothesis types `A`
  at some `T` below; `T↑ ≡ sort u` above must descend: `TypeFrontN.sort`); `Π` with a
  non-skeleton body (same, for the body's type); `app` (`AppFrontN`); `proj` (`ProjFrontN`);
  `elim` (`ElimFrontN`). "Environments with no definitional unfolding" was not pursued: the
  blocking rule in every case is a conversion between lifts or an exposure, not an unfolding.
* `GenericTypesTyped env` (generic eliminator types typed at a sort in `[]`) discharges
  `ElimFrontN` (`ElimFrontN.of_genericTyped`, through `elim_inv`, `elimDF` and `weak0`). The
  library lacks this environment lemma (it has `WF.eliminator_genericType_closed` only); it is
  plausibly provable from `RegistrationCertificate` and is recorded as a side obligation.

Build clean; axiom audit of all 63 declarations: no `sorryAx`.
