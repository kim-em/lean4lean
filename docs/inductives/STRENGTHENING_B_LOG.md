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

### 2.4 Statement (ii) pinned (part 4)

`TypeFront` (front form of `TypeFrontN`) ↔ Kripke's `TypedFront` under canonical `Eq`
(`typeFront_iff_typedFront`): types-to-terms by encoding `a ≡ b : T` as the pair of types
`Eq T a a`, `Eq T a b` (both typable below, lifts convertible above through `IsDefEq.eqApp_r`,
read back by `eqApp_injective`); terms-to-types by aligning the two sorts with `sort_inv`. So the
domain-agreement obligation (ii) is exactly `TypedFront`, i.e. `KeyFaithful`
(`keyFaithful_iff_typedFront`), the statement the observation models could not deliver.

### 2.5 Attacks on (i) and (ii), and where each fails

(i) `PiExposureRedN`: `f : F` and `F : sort u` below, `F↑ →* Π A B` above; wanted `F →* Π _ _`
below.

* Induction on the path with the invariant "the current term is a lift": the base case closes
  (`piExposure_of_descending`), the step fails at the first non-descending step. Checked
  instance: `headSource_path_not_descending` (Astra's `headSource`, a type typable below, whose
  lift reaches `headTypeBad Q` by one eta step inside an argument and one beta step; the eta
  annotation `badDomain Q = (λ z : Q↑. Prop) q` mentions the inserted variable). This holds for
  every `Q`, so uninhabitedness does not repair the invariant.
* Weakened invariant "the current term is convertible above to the lift of a type typable
  below": the step case would need, for a step `X → X'` with `X ≡ G↑`, a `G'` with `G →* G'`
  below and `X' ≡ G'↑`; the guards of that step are conversions and typings of subterms of `X`,
  which are arbitrary terms (not lifts, not subterms of `F`), so nothing is known about them
  below. And even granting such a one-step repair, the continuation `X' →* Π` cannot be replayed
  from `G'↑`: `exposure_reduces` produces a new path from `G'↑` whose length is unrelated to the
  remaining length, so no induction measure decreases. (A strip lemma with length control is
  not available for `FullStep`: `join_trans` and `WF.church_rosser` give joins without bounds,
  and eta/delta steps have no one-step diamond.) Conclusion: there is no single-step lemma whose
  composition gives (i); the obligation is global, the same shape as `JoinRepair`
  (`reflection_iff_supportedRepair`).
* Which guards: `ParRed.extra` compares matched subterms by `IsDefEqU Γ'` (`r.2.OK`), i.e.
  `Front` instances for lifted subterms of the current term; `ParRed.schema` has
  `CaseRedex.guard : IsDefEqU Γ' actual.expr (rule.lhs ..)`; `FullStep.delta` carries
  `UnfoldingCheck` (`source_typed`, `captures_typed` in the context extended by the opened
  binders, `major_prop`, `recursor_lhs : ConstSpineDefEq`); `projIota`, `structEta`, `funEta`
  carry typings at types above (`funEta` chooses the annotation from that type: the
  `headTypeBad` mechanism). For the *first* step from `F↑` every guard is on lifts of subterms
  of `F` (so a size induction on `F` could handle the first step); for later steps the guards
  are on subterms of reducts, which need not be smaller than `F` (beta duplicates, delta unfolds
  the stored value). So "every premise is on a lift of a subterm of the original term" is FALSE
  beyond the first step; the size induction does not close.
* Induction on the `IsDefEq` derivation of the typing judgment above, generalised to equations
  whose endpoints are lifts: fails at `trans` (the middle term is arbitrary) and at `defeqDF`
  (the type is arbitrary); the strong judgment `IsDefEqStrong` has the same `trans`. Not written
  in Lean: the failing case is immediate from `IsDefEq.trans`.

(ii) `TypeFrontN` ↔ `TypedFront` (section 2.4): `A↑ ≡ B↑` above for types `A B` of `Γ`. Via
Church-Rosser this is a join of two lifts above, i.e. `JoinRepair` restricted to types; the same
non-descending paths occur (`headSource` is a type). No new attack succeeded; the skeleton case
closes (`typeFrontN_skeleton`) because skeletons are stationary up to congruence and their
inversions (`sort_inv`, `forallE_inv`) are context-free.

Net result of step 2: `Cancel ↔ UninhabitedTypingFront ↔ TypingFrontN ↔ (AppFrontN ∧ TypeFrontN
∧ ProjFrontN ∧ ElimFrontN)`, with `AppFrontN ⇐ PiExposureN ∧ TypeFrontN`, `PiExposureN ⇐
PiExposureRedN`, `TypeFront ↔ TypedFront`, and `ElimFrontN ⇐ GenericTypesTyped`. The problem is
not solved; it is now stated as two obligations about *types of Γ* with lifts convertible above:
existential `Π` exposure (open, no reduction to anything known) and the fixed-type front
(`TypedFront`, known equivalent to `KeyFaithful`), plus the projection closure and an
environment lemma on generic eliminator types.
