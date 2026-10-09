# Direction E log: the projection and eliminator closures

Branch `agent/verify-inductives-strengthening3-E` (worktree `lean4lean-strength3-E`), off
`agent/verify-inductives-strengthening3` at 81ee106e. Brief: discharge the two environment-level
closures `ElimFrontN` and `ProjFrontN` that `cancel_iff_typedFront_of` (`Exposure.lean`) assumes,
or state the exact missing environment lemma as a `def` with checked implications. Files under
`Lean4Lean/Theory/Typing/Strengthening/` are at zero `sorry` in every commit; `Exposure.lean` and
`EtaPostponement.lean` are not touched (B3 owns `EtaReplay`).

## Step 0: what the library records about the two closures (reading)

* `ElimFrontN` needs, for a typed `elim block owner (target :: levels)` above, a typing of the
  closed generic type `type.instL (target :: levels)` at a sort *below* (`elimDF` takes it as a
  premise in every context). `GenericTypesTyped` (`TypingFront.lean`) asks for it in `[]`.
  The `inductEliminators` constructor of `VEnv.WF'` records a `RegistrationCertificate`
  (`CaseFormation.lean`): `Certified` (the case part `CaseCompilationData` of a compilation:
  `SourceWF`, `OrdinaryFormationWF`, `Models`, restoration scoping, `familyTypesWF` in the
  *expanded* constructor environment with the expanded declaration's own eliminators and projection
  entries), the key, and `HeaderAgreement` (declared family headers convertible to restored
  normalized headers in `envTypes`). No field types the restored case type. The only typing
  lemma about generic types is `WF.eliminator_genericType_closed` (closedness). The installed
  recursors are typed (`VInductBlock.WF`), but registration precedes recursor installation, and
  the case type is the recursor type with other families' motives and all induction hypotheses
  removed, so deriving it from the recursor type is a closed-telescope thinning, i.e. a
  strengthening instance. Deriving it from `familyTypesWF`/`Models` means re-proving the
  formation of the case telescope and transporting it out of the expanded environment through
  restoration: a large development not present in the library.
* `elimIota`/`CaseStep.iota` also take the closed typings `lhs/rhs : type` at the specialization
  as premises (`CaseReduction.lean`); `CaseRhsTyping.lean` types the rhs from the *layout* of the
  generic type only (no typing of the generic type is derived there).
* `ProjFrontN`: the library has `NormalEqN.spine_expose` (`FullReduction.lean`: a term normally
  equal to a rigid spine either is a proof, reduces to a spine with an equivalent head, or reduces
  to a lambda), `ParRed.rigid_const_spine`, `DeltaPar.rigid_spine`, `PrefixUnfold.not_rigid`,
  `QuotPrefixUnfold.not_rigid`, `NormalEq.fullReduction` (transport of normal equality along a
  reduction on the right), `WF.church_rosser`, `constHeadRigid_iff` (`Rigid ↔ ConstHeadRigid`).
  Field types: `projDF` takes `fieldType : sort fieldLevel` as a premise; the field-typing lemmas
  (`field_typing_aux`, `field_typing_of_ctorApp`, `field_walk`) are for constructor-application
  majors only, and `HeadInversionDefs.lean` records why the general field-type comparison went
  through the semantic model (a data field of a `Prop` structure is unprojectable, so the
  substitution instance of the constructor telescope cannot be typed by substitution).

## Step 1: spine exposure (`Strengthening/SpineExposure.lean`)

Namespace `VEnv.StrengtheningSpineExposure`, imports `Exposure`. Mirrors `Exposure.lean` for a
constant spine in place of a `Π`:

* `EtaPar.const_spine_inv_r`, `EtaChain.const_spine_inv`: an eta chain above from the lift of a
  type into `mkApps (const S ls) args` starts at `mkApps (const S ls) args₀` (at every node on the
  spine of a type, `funEta` produces a lambda and `structEta` needs a structure-typed subject,
  `TypeLike.not_struct`). The head and the levels are preserved exactly.
* `SpineExposureRedN hE` (reduction form: a type typed below whose lift reduces above to a
  constant spine reduces below to a spine with the same head and levels) and
  `spineExposureRed_of_etaReplay : (∀ U, EtaReplay) → SpineExposureRedN henv` by `path_replay`.
* Above, conversion to reduction: `spine_exposure_reduces` (canonical `Eq`): `T : sort u`,
  `T ≡ mkApps (const S ls) args`, `S` rigid and a type former ⟹ `T →* mkApps (const S ls') args'`.
  Through `WF.church_rosser`, both sides reduce to normally equal reducts. The reduct of the spine
  is not a spine in general (inner `funEta`: `S a b →* (λ x. S a x) b`), so the `Π`-stability
  argument of `exposure_reduces` does not transfer. Instead `EtaSpine S ls n` (head, applications,
  lambdas; `n` counts nodes) is preserved by `FullStep` when `S` is rigid (`ConstHeadRigid`, from
  `Rigid` by `constHeadRigid_iff`; stored rules, case rules and prefix unfolding are excluded by
  `ParRed.rigid_const_spine`, `Params.not_rigid_match`, `PrefixUnfold.not_rigid`,
  `QuotPrefixUnfold.not_rigid` and the head shape `EtaSpine.head_cases`) and a type former
  (`TypeFormerHead`: every node is typed at a `Π`-telescope ending in a sort,
  `EtaSpine.typeFormer`, so `structEta` applies to none, `EtaSpine.not_struct`); a sort-typed eta
  spine beta-reduces back to a syntactic spine (`EtaSpine.reduces_to_spine`, induction on `n`
  with the extra arguments generalized, substitution preserving `n`). Then
  `NormalEq.fullReduction` transports the join and `NormalEqN.spine_expose` (library) exposes the
  type's reduct: the proof and lambda alternatives are excluded by its sort typing.
* `TypeFormerHead.of_telescope` (a constant typed at `wrapForalls D (sort w)` in `[]` is a type
  former: partial applications by `HasType.mkApps_wrapForalls` and `instOuter_wrapForalls_sort`,
  over-applications contradict `sort_forallE_inv`) and `typeFormerHead_of_projections` (from
  `Ordered.projectionShape`: `TypeShape` gives the normalized header `wrapForalls (P ++ I) result`
  with `result ≡ sort rl`, closed by `wrapForalls_congr`).

Build clean, zero `sorry`.

## Step 2: the projection closure reduced (`SpineExposure.lean`, part 3)

`ProjFrontN.of_spineExposure : SpineExposureRedN henv → ProjFieldFrontN env → ProjFrontN env`
and `ProjFrontN.of_etaReplay`. From `proj_inv` above, `m↑ : S levels (params ++ indexArgs)`,
so `M↑ ≡ S levels …` for the type `M` of `m` below; `spine_exposure_reduces` and
`SpineExposureRedN` give `M →* S ls' args₀` below, `m : S ls' args₀`; `rigidApp_inv` above (the
lifted reduct against the structure type above) gives `ls' ≈ levels` pointwise and
`args₀.length = nparams + nindices`; `projDF` closes with the field type typed below by
`ProjFieldFrontN`:

```
ProjFieldFrontN env := ∀ U k Γ Γ' S info ls ps idx m i T, Ctx.LiftN 1 k Γ Γ' → OnCtx Γ → OnCtx Γ' →
  env.projections S info → ls.length = info.uvars → ps.length = info.nparams → idx.length = info.nindices →
  m : mkApps (const S ls) (ps ++ idx) below → proj S i m↑ : T above →
  ∃ F l, info.fieldType S ls ps i m = some F ∧ F : sort l below ∧ ((info.resultLevel.inst ls).IsNeverZero ∨ l ≈ 0)
```

This is the exact remaining obligation of the projection case. Analysis (see step 4 for what is
proved): `F = (doms[nparams + i].instL ls).instOuter (ps ++ [proj 0 m, …, proj (i-1) m])`
(`fieldType_eq_instOuter`). When `(resultLevel.inst ls).IsNeverZero`, every earlier projection is
typable (the guard's left disjunct) and `F` is typed by the typed telescope substitution
`IsType.instOuter_telescope`, with no information from above: a library fact. When the structure
is in `Prop` at these levels, an earlier data field `j` (field type not a proposition) has an
untypable projection; if `doms[nparams+i]` mentions binder `j` then the field type above mentions
`proj j sourceMajor`, itself untypable, so the typing above excludes this case; if it does not
mention `j`, `F` is typed only by thinning binder `j` out of the closed constructor telescope,
i.e. a `TypingFrontN` instance on an environment-determined closed term with an uninhabited
removed binder (`Cancel.inhabited` does not apply: no term of the data field's type is available
below). So the content of `ProjFieldFrontN` beyond library telescope facts is closed-telescope
strengthening for `Prop` structures with data fields, the same shape as `GenericTypesTyped₀`.

## Step 3: the eliminator closure and the assembly (`Strengthening/Closures.lean`)

* `GenericTypesTyped₀ env` (generic type typed at a sort in `[]` at `schema.genericUvars`) ⟹
  `GenericTypesTyped env` (`GenericTypesTyped.of_generic`, by `HasType.instL` with
  `Permission.packedWF`) ⟹ `ElimFrontN env` (`ElimFrontN.of_generic`). The quantification over
  all permitted specializations in `GenericTypesTyped` is therefore free; the generic typing is
  the missing environment lemma. Why it is not in the library: step 0.
* `GenericRulesTyped₀ env` (generic equations typed in `[]`) ⟹ the closed typing premises of
  `CaseStep.iota` at every permitted specialization in every context
  (`GenericRulesTyped₀.caseStep_premises`, `instL` then `weak0`). These are the closed typings
  `CaseRedexDescends` needs; the remaining content of `CaseRedexDescends` (captures typed at
  their domains, the alignment guard) is `TypedFront` retyping (B2 log, step 4), not attempted
  here.
* `cancel_iff_typedFront_of_etaReplay (henv) (heq) (H : ∀ U, EtaReplay) (hGen : GenericTypesTyped
  env) (hField : ProjFieldFrontN env) : Cancel env ↔ TypedFront env`, and the `₀` variant with
  `GenericTypesTyped₀`.

Build clean, zero `sorry`.

## Step 4: the field-type closure outside `Prop` (`SpineExposure.lean`, part 4)

`projField_of_neverZero`: for `m : mkApps (const S ls) (ps ++ idx)` in `Γ` with
`(info.resultLevel.inst ls).IsNeverZero` and `i < info.numFields`, the field type
`info.fieldType S ls ps i m` is `some F` with `F : sort l` in `Γ`. No information from any other
context. Proof: `Ordered.projectionShape` gives the declaration, the constructor's raw telescope
`ctor.type = wrapForalls doms result` (`RawCtorShape.forallArity`, `numFields = doms.length -
nparams`), its well-formedness in `[]`, and the two parameter shapes (`TypeShape` for the type
former, `CtorParameterShape` for the constructor) through the common `params`; the type former's
header is `wrapForalls (P ++ I) (sort rl)` up to conversion (as in step 1), so
`HasType.mkApps_wrapForalls` types `ps` at the type former's parameter domains; these are
converted to the constructor's (`IsDefEqCtx.trans_empty`, `reverse_getElem`,
`IsDefEqU.closed_telescope_instOuter`); the field domains are types in their closed telescopes
(`IsType.wrapForalls_inv`, `OnCtx.getElem_reverse_append`) and
`IsType.closed_telescope_instOuter` (new: closed-context weakening by `Ctx.LiftN.right` then
`IsType.instOuter_telescope`) instantiates them at `ps ++ [proj 0 m, …, proj (j-1) m]`; the
earlier projections are typed by induction on the field index with `projDF` and the guard's left
disjunct. Hence `ProjFieldFrontN.of_notNeverZero : ProjFieldFrontPropN env → ProjFieldFrontN env`,
where `ProjFieldFrontPropN` is `ProjFieldFrontN` with the extra hypothesis
`¬ (info.resultLevel.inst ls).IsNeverZero` (the field index bound comes from
`HasType.proj_index_lt` above). `Closures.lean`: `cancel_iff_typedFront_of_etaReplay₀` takes
`GenericTypesTyped₀` and `ProjFieldFrontPropN`.

Axiom audit (`scratch/SpineAxioms.lean`, all theorems of both files): `propext`,
`Classical.choice`, `Quot.sound`; no `sorryAx`.

## Final state

Files: `Lean4Lean/Theory/Typing/Strengthening/SpineExposure.lean` (spine exposure, `EtaSpine`,
the projection closure, the field-type closure outside `Prop`) and `Closures.lean` (the
eliminator closure from `GenericTypesTyped₀`, the closed rule typings from `GenericRulesTyped₀`,
the assembled biconditionals). Nothing outside `Strengthening/` and `docs/inductives/` changed;
`Exposure.lean` and `EtaPostponement.lean` untouched; no statement changed; no test deleted.

The exact missing environment lemmas, as `def`s with checked implications:

* `GenericTypesTyped₀ env` ⟹ `GenericTypesTyped env` ⟹ `ElimFrontN env`. Content: formation of
  the restored case type of every registered schema in `[]` at the generic universes. Not
  derivable from the installed recursor's type without thinning (closed-telescope
  strengthening), and registration precedes recursor installation anyway.
* `GenericRulesTyped₀ env` ⟹ closed typing premises of `CaseStep.iota` in every context at every
  permitted specialization (one of the two parts of `CaseRedexDescends`; the other is `TypedFront`
  retyping of the captures and the alignment guard, B2 log).
* `ProjFieldFrontPropN env` ⟹ `ProjFieldFrontN env` ⟹ (with `EtaReplay`) `ProjFrontN env`.
  Content: typing below of the field type of a `Prop`-structure (or possibly-`Prop` at the given
  levels) field whose projection is typable above; beyond library telescope facts this is the
  thinning of unprojectable data-field binders out of the closed constructor telescope, i.e.
  closed-telescope strengthening with an uninhabited removed binder.
