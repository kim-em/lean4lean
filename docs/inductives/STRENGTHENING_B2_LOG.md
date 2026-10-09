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

## Step 2: descent of eta-free parallel steps (`Replay.lean`, part 2)

Design (after reading `FullReduction`, `ChurchRosser.ParRed`, `LevelledReduction.DeltaPar/EtaPar`,
`PrefixUnfolding/Rule`, `CaseReduction`, the concrete pattern table `Confluence/Patterns`): the
output of every `FullStep` rule except the two eta rules is a syntactic function of the lifted
input (beta `b[a]`, stored rules `r.1.apply`, case iota `rule.rhs`, prefix unfolding `program.rhs`
with generation commuting with lifting, projection iota the field), so a step above on a lift is
the lift of a step below *iff its guards hold below*. Eta steps are the only source of non-lift
reducts (`badEta`, `headTypeBad`). So the right unit of replay is a parallel eta-free step:
`ParRed` (core) and `DeltaPar` (delta, quotDelta, projIota), both already in the library with
`weakN`/`instN`.

Checked (`TypedFrontN` is `TypedFront` along any single-binder insertion, `typedFrontN_iff_typedFront`
under canonical `Eq`):

* `ParRed.descend` (hypotheses `TypedFrontN`, `CaseRedexDescends`, and `CheckVars` for every
  pattern): a `ParRed` above on the lift of a term typed below is the lift of a `ParRed` below.
  Per constructor: `bvar/sort/const/elim` trivial; `app/proj/lam/forallE` by inversion and the
  induction hypothesis; `beta` syntactic (`liftN_inst_hi`); `extra`: the match descends
  (`Pattern.matches_liftN`), the captured subterms are typed below (`Pattern.Matches.typed`), and
  the check descends (`Check.OK.descend`): `nonzero` is context-free, `defeq` compares two captured
  subterms (`CheckVars`; true of every concrete pattern: definitions `.true`, generated iota
  `ruleCheck` = `nonzero`/`true`, quotient `quotPatternCheck` = `nonzero` + one `defeq` of two
  captured `.var`s), discharged by `TypedFrontN.independent`. So the stored-rule guard is exactly
  a `TypedFront` instance. `schema`: the application descends syntactically
  (`case_application_liftN_inv`), the captures are typed below from the descended `CaseRedex`
  (`CaseStep.arguments_typed`), the output is syntactic (`instantiateParams_liftN`); the guard
  `CaseRedex` itself is the obligation `CaseRedexDescends`.
* `DeltaPar.descend` (hypotheses `TypedFrontN`, `UnfoldingCheckDescends`): `delta`/`quotDelta`:
  the generated program above is the renaming of the program generated below
  (`singletonUnfolding_sameArity` + `singletonUnfolding_lift'` + uniqueness; for `Quot.lift`
  `generate_inst` with the un-lifting instantiation at `sort 0` + `generate_rename`), the rhs is
  the lift (`rename_rhs` with `templateScope`), and the only remaining guard is `UnfoldingCheck`
  (`PrefixUnfold.descend`, `QuotPrefixUnfold.descend`). `projIota`: the field is typed below at
  the projection's type by `TypedFrontN.retype` (the field is an argument of the typed major, the
  projection's type is a type below, and the field's lift is typed above at that lift by unique
  typing); no saturation lemma is needed.

Not yet discharged (recorded as `def`s): `CaseRedexDescends` (the `CaseStep` typing of the
captures at their domains, and the alignment conversion `actual.expr ≡ rule.lhs …`), and
`UnfoldingCheckDescends` (`captures_typed`, `major_prop`, `recursor_lhs`). Analysis of their
contents is in step 3 below.

Build clean; axiom audit of all new declarations (`scratch/ReplayAxioms.lean`): no `sorryAx`.

## Step 3: the measure, the eta-chain invariant and the exact obligation (`Exposure.lean`)

Why no path measure exists with the invariant "the current reduct is a lift" (Astra round 9,
direction B): after an eta step the reduct is not a lift, the natural repair `out ≡ e'↑` is
*vacuous* (every step is a conversion, so `e' := e` always works and carries no shape), and
restarting the path from `e'↑` by `exposure_reduces` has uncontrolled length.

The invariant that works is **"the current reduct is an eta chain of a lift"**:
`EtaChain Γ' (e↑) X := ReflTransGen (EtaPar Γ') (e↑) X` with `EtaPar` the library's parallel
eta expansion (`LevelledReduction.lean`; its `funEta`/`structEta` constructors carry exactly the
"arbitrary convertible annotation" freedom). The induction is on the above `UpStep` path
(`FullStep.upStep`: core, delta or eta parallel steps), length decreasing, no size component:

* an eta step above extends the chain, nothing happens below (`etaReplay_eta`);
* an eta-free step above must be pushed through the chain: this is the exact remaining
  obligation **`EtaReplay`** (`Exposure.lean`): an eta chain above from the lift of a term typed
  below, followed by one `UpStep`, is simulated by a `FullReduction` below followed by an eta
  chain. On the empty chain it is exactly the descent of step 2 (`etaReplay_of_descent`,
  `etaReplay_empty_chain`), so its content is "descent + eta postponement".
* at the end, `EtaChain Γ' (F'↑) (Π A B)` with `F' : Sort u` forces `F' = Π A₀ B₀`
  (`EtaPar.forallE_inv_r`: a type is neither a function (`type_not_function`) nor a structure
  (`type_not_structure`), so only the `forallE` congruence applies; `EtaChain.forallE_inv`).

Checked: `path_replay` (induction on the `UpStep` path), `piExposureRed_of_etaReplay`
(`EtaReplay → PiExposureRedN`), `cancel_of_typedFront_of` and
`cancel_iff_typedFront_of : Cancel env ↔ TypedFront env` given `∀ U, EtaReplay`, `ProjFrontN`,
`ElimFrontN` (the typed front enters only through `AppFrontN.of_piExposure` and, inside
`EtaReplay`, through the guards of the replayed steps).

What `EtaReplay` says beyond descent, and why it is believed true: `EtaPar a b` (b more
expanded) followed by `ParRed b c`/`DeltaPar b c` should be simulated from `a` by eta-free steps
plus *structure eta at a firing major* and then `EtaPar d c`:

* fun-eta at a function position is undone by the following beta (`(λ D. f↑ 0) y →β f y`); at an
  argument or binder position it is junk, carried along by the chain (the library's `collapse_*`
  lemmas, `EtaPar.collapse_lam/spine/proj/major/elim`, are exactly these collapses in the peak
  orientation used by the confluence proof `EtaPar.parRed_peak`; `EtaReplay` needs the valley
  orientation, which is not in the library);
* struct-eta at a major position is **essential** (Astra's `Box.rec M f s = f s.1` by `rfl`): a
  neutral structure-typed major computes only after eta. It is replayable below *because the
  enclosing application is typed below*: `rec args s` typed below gives `s : I params₀ idx₀`
  below by `RecursorRegistered.major_type`, so `structEta` below is available with the lifted
  parameters, and the following iota discards the parameters (`Params.pat_iota_params`,
  `CaseRedex.struct_major`: iota reads only fields), so the outputs agree exactly. Struct-eta at a
  *non-major* position needs rigid-type exposure of the subject's type, which is not forced by
  the enclosing typing; it is junk for exposure (projections of a wrapper collapse) and must be
  postponed like fun-eta.

So `EtaReplay` is a statement about the reduction system above plus TF-guard descent; the
genuinely new part is eta postponement with struct-eta-at-majors absorbed. Whether `Cancel`
implies `EtaReplay` is not established (it is sufficient, not shown necessary).

## Step 4: the guards, one by one (the replay table)

For a `FullStep`/`UpStep` above on the lift `e↑` of a term `e : T` typed below. "TF" means the
guard is a `TypedFront` instance (`TypedFrontN.independent` for conversions between lifts of
typed-below terms, `TypedFrontN.retype` for typings at lifted types). "Env" means an
environment-level typing lemma the library lacks.

| rule above | output | guard(s) | status |
|---|---|---|---|
| `ParRed.beta` | syntactic (`liftN_inst_hi`) | none | proved (`ParRed.descend`) |
| `ParRed.app/proj/lam/forallE`, `bvar/sort/const/elim` | syntactic | none (inversion) | proved |
| `ParRed.extra`, definition pattern | syntactic (`liftN_apply`) | `.true` | proved |
| `ParRed.extra`, generated iota pattern | syntactic | `nonzero` (context-free) | proved |
| `ParRed.extra`, quotient pattern | syntactic | `nonzero` + `defeq` of two captured subterms | proved: TF (`Check.OK.descend`, `CheckVars`) |
| `ParRed.schema` (case iota) | syntactic (`instantiateParams_liftN`) | `CaseRedex`: `CaseStep` (closed rule typings `lhs/rhs : type` in Γ, Env; captures typed at domains: TF retyping given domains typed below, by telescope induction from the closed rule typing) and `guard : e ≡ rule.lhs[captures]` (TF once both sides typed below) | reduced to `CaseRedexDescends` (Env + TF) |
| `DeltaPar.delta` (singleton prefix unfolding) | syntactic (`singletonUnfolding_lift'`, `rename_rhs`) | `UnfoldingCheck`: `source_typed` (free: `prefixType`), structure (free: generation spec), `captures_typed` (TF retyping, given each capture typed below at some type: lifted args and variables yes; the reconstructed fields `PropElim.occ` yes *given* the cast equations `X ≡ Y` between index and field types, themselves TF instances between types typed below), `major_prop` (TF: `majorProp_descend`), `recursor_lhs` (TF: `ConstSpineDefEq.descend`, both spines typed below) | reduced to `UnfoldingCheckDescends` (all TF, no Env; the field-typing induction mirrors `occ_typed` with TF in place of the aligned field instance) |
| `DeltaPar.quotDelta` | syntactic (`generate_inst` at `sort 0`, `generate_rename`) | same `UnfoldingCheck`; captures are lifted args, variables and `propInhabitant`, all typed below directly | reduced to `UnfoldingCheckDescends` (TF) |
| `DeltaPar.projIota` | syntactic | field typed at the projection's type: TF retyping (`TypedFrontN.retype`) | proved (`DeltaPar.descend`) |
| `FullStep.structEta` at a major of a typed recursor/case application | not a lift (parameters from the type above), but the parameters are convertible to lifts and are discarded by the following iota | typing of the major below from the enclosing application (`major_type`) | replayable in principle as a composite struct-iota (see step 3); not mechanised |
| `FullStep.structEta` elsewhere | not a lift | rigid-type exposure of the subject's type: NOT TF, not forced by typing | blocked; must be postponed (`EtaReplay`) |
| `FullStep.funEta` | not a lift (`arbitrary_Q_eta`, `headTypeBad`: domain mentions the inserted variable) | `Π`-exposure of the subject's type: NOT TF | blocked; must be postponed (`EtaReplay`) |

Checked examples of the blocked cases: `arbitrary_Q_eta`/`headType_bad_reduct` (`TypingFront.lean`,
fun-eta output is not a lift for every `Q`), `headSource_path_not_descending`; Astra's round 9
regression (`history/StrengtheningRound9Regression_2026-10-09.lean`) shows a second-step
singleton guard on terms occurring in no subterm of the source, which is exactly why the
descent is organised per parallel step with guards discharged by TF rather than by a size
measure; Astra's `Box.rec` example (same file) shows the essential struct-eta at a major.

Remaining `def`s, with the checked implications: `EtaReplay` (step 3), `CaseRedexDescends`,
`UnfoldingCheckDescends` (step 2; both sufficient for `etaReplay_empty_chain`), `ProjFrontN`,
`ElimFrontN` (the last follows from `GenericTypesTyped`, `TypingFront.lean`; the `elimDF` typing
rule takes the generic type's sort typing as a premise in every context and the WF constructor
`inductEliminators` records only a `RegistrationCertificate`, so both `GenericTypesTyped` and
the closed case-rule typings inside `CaseRedexDescends` are environment lemmas to be derived
from the certificate).

## Step 5: the regression path under the eta-chain invariant (checked)

`headSource_etaReplay_instance` (`Exposure.lean`): Astra's `headSource` path, which defeats the
lift invariant (`headSource_path_not_descending`), satisfies the eta-chain invariant: the reduct
after the eta step is an eta chain of `headSource.lift` (`etaPar_headType_bad`: the eta step is
`EtaPar.funEta` at the domain `badDomain Q` inside the argument), the beta step above is simulated
by the beta step `headSource → headType` below, and `headTypeBad Q` is an eta chain of
`headType.lift`. So the `EtaReplay` instance for this path holds with `e' = headType`.

Final state. Files: `Lean4Lean/Theory/Typing/Strengthening/Replay.lean` (round 9 lemmas; part 2:
`TypedFrontN`, descent of `ParRed` and `DeltaPar`, alignment guards), `Exposure.lean` (eta-chain
invariant, `EtaReplay`, assembly, regression instance). Both build at zero `sorry`; axiom audits
(`scratch/ReplayAxioms.lean`, `scratch/ExposureAxioms.lean`): only `propext`, `Classical.choice`,
`Quot.sound`. Nothing outside `Strengthening/` and `docs/inductives/` was changed; no existing
statement was changed; no test was deleted.
