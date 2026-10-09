# Direction F log: consolidation to the sharpest checked statement

Branch `agent/verify-inductives-strengthening3-F` (worktree `lean4lean-strength3-F`), off
`agent/verify-inductives-strengthening3`. Brief: discharge the guard descents that
`cancel_iff_typedFront_B3` (`EtaClosure.lean`) assumes (`UnfoldingCheckDescends`,
`CaseRedexDescends`, `MajorEtaDescends`), restate direction E's spine exposure over the proved
`EtaNE` closure, and assemble the final theorem (`Strengthening/Final.lean`) with its exact
hypothesis list. Files under `Lean4Lean/Theory/Typing/Strengthening/` are at zero `sorry` in every
commit; new work goes to new files (`Descents.lean`, `Final.lean`, ...).

## Step 0: merge of the integration branch

Merged `kim-em/agent/verify-inductives-strengthening3` at 8f0f2206 (fast-forward; mainline's
removal of unused hypotheses, `IsDefEqU.closed_telescope_instOuter` lost its `OnCtx` argument).
`lake build Lean4Lean.Theory` clean after the merge.

## Step 2 (done first, see step 1 for the reason): `CaseRedexDescends` (`Descents.lean`)

`caseRedexDescends : TypedFrontN env → GenericRulesTyped₀ env → CaseRedexDescends` (checked;
axioms `propext`, `Classical.choice`, `Quot.sound`). Contents, following B2's table row for
`ParRed.schema`:

* `source : CaseStep`: the closed typings `lhs/rhs : type` in `Γ` from
  `GenericRulesTyped₀.caseStep_premises` (E); `CaseArguments` by strong induction on the capture
  index: the capture is an argument of one of the two spines of the typed application below
  (`case_capture_wf`, `VExpr.WF.args_of_mkApps`), its specialized domain
  `instantiateParams (domains[j].instL lv) (caps.take j)` is a type below by
  `IsType.instOuter_telescope` over the specialized domain telescope (`caseRule_domains_ctx`:
  `IsType.wrapForalls_inv` of the closed left-hand side's type, `body_exact`), and the above
  typing (`instantiateParams_liftN` with `CaseStep.domains_closed`) is brought down by
  `TypedFrontN.retype`.
* the symbol and length fields are rename-invariant; `guard` is `TypedFrontN.independent`
  between `actual.expr` (typed below by hypothesis) and `rule.lhs lv caps` (typed below by
  `CaseStep.defeq` of the descended step).

So `CaseRedexDescends` is exactly `TypedFront` plus the closed rule typings, as B2 predicted.

## Step 3: spine exposure over `EtaNE` (`SpineClosure.lean`)

Direction E's `spineExposureRed_of_etaReplay` assumed `EtaReplay`, which is false
(`not_etaReplay`). Restated over the proved closure, mirroring `piExposureRed_of_etaReplayNE`:

* `LStep.chain_descend`: a `ReflTransGen (LStep Γ')` chain from the lift of a term typed below
  descends step by step (`ParRed.descend`, `DeltaPar.descend`, `MajorEtaIotaC.descend`), the
  same induction as the `redL` case of `EtaNE.forallE_inv_lift`.
* `EtaNE.const_spine_inv_lift`: `EtaNE Γ' (F↑) (mkApps (const S ls) args)` with `F : sort u`
  below gives `F →* mkApps (const S ls) args₀` below (`EtaNE.const_spine_inv`; the structure-eta
  branch is excluded by `type_not_structure`).
* `spineExposureRed_of_closure : TypedFront → (∀ U, CaseRedexDescends) →
  (∀ U, UnfoldingCheckDescends) → (∀ U, MajorEtaDescends) → SpineExposureRedN henv` and
  `ProjFrontN.of_closure` (plus `ProjFieldFrontN`). Axioms: `propext`, `Classical.choice`,
  `Quot.sound`.

Design note for step 4: `MajorEtaDescends` must not be derived from `ProjFrontN` (B3's log
suggested it for `numFields > 0`), since spine exposure itself descends composite steps and so
depends on `MajorEtaDescends`. The structure type of the major below is read instead from the
head of the application typed below (`RecursorRegistered.major_type` for recursor iota,
`CaseRedex.majorPremise` for case steps), which also removes the `numFields = 0` special case.

## Step 4: `MajorEtaDescends` (`MajorEta.lean`)

`majorEtaDescends : TypedFrontN env → CaseRedexDescends → (∀ p r, Pat p r → CheckVars r.2) →
ProjFieldFrontN env → MajorEtaDescends` (checked; axioms `propext`, `Classical.choice`,
`Quot.sound`). Following B3's log steps 6 and 7, with two changes:

* The structure type of the major below is not obtained from `ProjFrontN` (circular: spine
  exposure, hence `ProjFrontN.of_closure`, descends composite steps). It is read from the head of
  the application typed below: `RecursorRegistered.major_type` for a recursor iota pattern
  (`pat_recursor` gives the registered data, `pat_simple` and `iota_matches_spine` the shape
  `rc vs m₀` with `vs.length = majorOffset`), `QuotRegistered.major_type` for the quotient
  pattern (`Quot.lift [u, v] [α, r, β, f, h] m₀`), `HasType.caseMajor_type` for a case step
  (arity from `Certified.arguments_length`). In each case the head is rigid
  (`family_head_rigid`, `quot_rigid`, `case_family_head_rigid`), and the structure is rigid
  (`projectionRigid`), so `rigid_rigid` on the two types of `m₀↑` above identifies the family,
  gives `lv ≈ levels` and `args↑ ≡ params`. No `numFields = 0` special case.
* The structure eta step below needs the expansion `ctor lv args (proj i m₀)` typed below
  (`FullStep.structEta`'s premise), hence each `proj i m₀` typed below. For `Prop` structures
  with data fields this is exactly the field-type closure, so `ProjFieldFrontN` is a hypothesis
  of the descent (free outside `Prop` by `projField_of_neverZero`; its `Prop` part
  `ProjFieldFrontPropN` is a hypothesis of the final theorem anyway). `structExpand_descend`:
  the projections above are arguments of the typed expansion above; `ProjFieldFrontN` and
  `projDF` type them below; the lifted expansion at the data below is typed above by spine
  congruence (`constDF`, `IsDefEqU.mkApps_args`) from the expansion above; the spine descends
  at the constructor's closed telescope (`telInst_descend`: strong induction on the position,
  each argument retyped at its domain, the domain a type below by `IsType.instOuter_telescope`;
  the constructor constant and its telescope from `projectionConstructor`, `projectionShape`,
  `RawCtorShape.forallArity`), and the result is retyped at the structure type.
* The fire is transported from `.app f↑ (ctor levels params projs)` to
  `.app f↑ (ctor lv args↑ projs)`: for a stored rule, a new match by `constVarN_transport`, the
  same right-hand side and check by `pat_iota_params`; for a case step, `CaseRedex.transport`
  with the same capture (`schema_struct_major`: `rule.numFields ≤ info.numFields`, so the drop
  skips all parameters, `drop_append_eq_of_length`). The transported fire is a `ParRed` on the
  lift of `.app f₀ (ctor lv args projs₀)`, typed below, and `ParRed.descend` (B2) descends it.
  Below: `.app f₀ m₀ →structEta .app f₀ (expansion) →core c₀`.

## Step 5 (first assembly): `Final.lean`

`cancel_iff_typedFront_final (henv) (heq) (hGen : GenericTypesTyped₀ env)
(hRules : GenericRulesTyped₀ env) (hField : ProjFieldFrontPropN env)
(hunfold : ∀ U, UnfoldingCheckDescends) : Cancel env ↔ TypedFront env`, and
`strengthening_iff_typedFront_final` via `strengthening_iff_cancel`; axioms `propext`,
`Classical.choice`, `Quot.sound`. The variant `cancel_iff_typedFront_and_elim` replaces `hGen`
by the exact component `ElimFrontN` (`Cancel ↔ TypedFront ∧ ElimFrontN`, since `Cancel` implies
`ElimFrontN` by `cancel_iff_typedFront_and_closures`). The assembly: `descents_of_typedFront`
(steps 2 and 4 at every universe bound), `ProjFrontN.of_closure` (step 3), then
`cancel_iff_typedFront_B3`. `UnfoldingCheckDescends` remains (step 1 below).

## Step 1 (analysis): `UnfoldingCheckDescends` as stated is not a `TypedFront` instance

`UnfoldingCheckDescends` quantifies over an arbitrary `program : PrefixUnfolding`, not only the
one generated by `singletonUnfolding`/`QuotPrefixUnfolding.generate` at the source's arguments
(its two uses, `PrefixUnfold.descend` and `QuotPrefixUnfold.descend`, instantiate it at generated
programs). For an arbitrary program the field `source_typed : Γ ⊢ source : wrapForalls
program.domains program.result` has unconstrained `domains`: above, any `D` with
`D↑ ≡ A↑` (`A` the source's actual domain below) satisfies the check with `domains = [D]`, and
below `source : Π D. result` requires `D` to be a type below, i.e. a `TypingFrontN` instance for
`D` (the same shape as the typing gap of `not_cancel_iff_typing_gap`). So B2's row "source_typed
(free: prefixType)" holds only for generated programs, and the descent must be proved for the
generated program directly: `source_typed` by `RecursorRegistered.prefixType`/
`QuotRegistered.prefixType` from the source typed below, the context-free fields by renaming
invariance, `major_prop` by `majorProp_descend`, `recursor_lhs` by `ConstSpineDefEq.descend`,
and `captures_typed` by retyping (`TypedFrontN.retype`) once every capture and the reconstructed
constructor are typed below at some type. The captures of the generated program are lifted
arguments, variables, data fields read from the index slots (typed below directly) and the
reconstructed proof fields `PropElim.value i` applied to the parameters, indices, major and the
cast arguments `Eq.refl (Sort s) X_k`; typing these below needs the typed instance
`TelInst Δ (params ++ S.indices ++ [majorTy]) (ps ++ idx ++ [bvar 0])` below (the layout
agreement between the recursor telescope and the singleton layout), obtainable by spine descent
(`telInst_descend`) from the typing above of the first proof field, and then the cast arguments
and the proof fields descend by the same spine descent at the closed telescopes `valueType i`.
This is the remaining mechanisation (see the steps below).

## Step 1 (mechanised): the unfolding guard descends for generated programs (`Unfolding.lean`)

`DeltaPar.descend' : HasCanonicalEq → TypedFrontN env → Γ ⊢ e : T → DeltaPar Γ' (e↑) out →
∃ e', out = e'↑ ∧ DeltaPar Γ e e'` (checked; axioms `propext`, `Classical.choice`,
`Quot.sound`), i.e. B2's `DeltaPar.descend` with `UnfoldingCheckDescends` discharged for the
generated programs, together with `PrefixUnfold.descend'`, `QuotPrefixUnfold.descend'` and the
chain descents `LStep.chain_descend'`, `EtaNE.forallE_inv_lift'`, `EtaNE.const_spine_inv_lift'`.

* `UnfoldingCheck.descend_of_typed`: the descent of every field once each capture is typed below
  at some type and the instantiated left-hand side is `.app X constructor`. `captures_typed` by
  strong induction on the position (`TypedFrontN.retype`; the specialized domain is a type below
  by `IsType.closed_telescope_instOuter` over the closed telescope of the installed equation,
  `extract_sound`, `IsType.wrapForalls_inv` in `[]`); the constructor is then typed below as the
  last argument of the instantiated left-hand side (`IsDefEq.extra_instOuter`, `app_inv`);
  `major_prop` by `majorProp_descend` (the major's domain is the last opened binder); the left
  spine `.app (etaOpen (n-1) source).lift constructor` is typed below (`etaOpen_wf`) so its
  arguments are well formed, and `recursor_lhs` descends by `ConstSpineDefEq.descend` (its two
  heads coincide, read off the alignment above). Context-free fields are rename-invariant.
* `singleton_captures_typed`: captures of the generated singleton program typed below. Opened
  arguments by weakening and lookup. Fields by strong induction on the field index with the
  shape lemmas `occ_getD_data` (library), `occ_getD_proof`, `occ_fst_getD_data`,
  `occ_fst_getD_proof`: a data field is an index slot or `default`; a proof field is
  `PropElim.value l` applied to `ps ++ idx ++ [bvar 0] ++ hats`, typed above as a capture, and
  `value l` is closed and typed at the closed telescope `valueType l` (`value_typed`), so the
  prefix descent `telInst_descend_prefix` gives `TelInst Δ (P ++ S.indices ++ [majorTy])
  (ps ++ idx ++ [bvar 0])` below *without* relating the recursor telescope to the layout; the
  cast arguments `Eq.refl (Sort s) ((S.indices[k]).instOuter (ps ++ idx.take k))` are then typed
  below (`T.slotSort`, `T.scope.slot_lt`, `HasType.closed_instOuter`, `HasType.eqReflApp`), the
  proof-field casts by the induction hypothesis, and the full spine descends (`telInst_descend`,
  `HasType.mkApps_of_tel`). The left-hand side shape comes from `singleton_equation_syntax`
  (`map_instOuter_vars`, `instOuter_closed0`). `propElim_wf` needs the owner's constructor index,
  read from `singletonLayout` (`singletonLayout_ctor`, `singletonCtor_owner`).
* `quot_captures_typed`: the quotient captures are the five opened arguments and the
  `propInhabitant` proof; `etaOpen_mkApps_const` types the six-argument `Quot.lift` spine in the
  opened context, `quotient_walk` types its arguments, `propInhabitant_app` the proof; the
  left-hand side is the concrete `quotDefEq` body, computed by `simp`.

So the only content of B2's `UnfoldingCheckDescends` beyond `TypedFront` is the typing of the
reconstructed fields below, which follows from the typing above by spine descent at closed
telescopes; and the obligation as stated (for arbitrary programs) is not needed.
