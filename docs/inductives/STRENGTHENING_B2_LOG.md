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
