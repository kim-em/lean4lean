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

(entries follow)
