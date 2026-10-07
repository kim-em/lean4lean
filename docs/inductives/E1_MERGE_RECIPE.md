# Recipe for merging `agent/verify-inductives-e1` into the mainline

Partial findings from a dry run (E1 463c99d4 + mainline f72c08fd; 2026-10-07).
The partial diff is `E1_MERGE_PARTIAL.diff`.

- Six text conflicts: HANDOFF.md, Theory/Typing/Env.lean (WF' docstring),
  scripts/inductive-audit-inventory.json, and
  Verify/Inductive/Nested/{RecursorProvenance,RestoredRecursorShape,RestoringExpansion}.lean.
  - HANDOFF and the Env docstring: keep both texts; the `StructCompat`
    sentence goes before E1's "certificate is the case part" paragraph.
  - Inventory `openProofs`: exactly `Lean4Lean.VEnv.WF.headInjectivity`.
- Relocations: mainline `Theory/Inductive/NativeIotaRestoration.lean` and E1's
  `RestorationShapes.lean` share 16 declarations (15 textually identical;
  `Restoration.expr_liftN` same statement, different proof). Resolution:
  `NativeIotaRestoration` imports `RestorationShapes` and drops its copies.
- E1's changes to the moved code: `Restoration.restored_iota_shape` (new
  `hfieldDoms` premise; helpers `List.mapM_append_eq_some`,
  `VExpr.wrapForalls_subst_doms`, `VExpr.subst_liftN_ofList`,
  `VExpr.liftN_at_instOuter`) and `CompilationData.restoredConstructorFieldDomains`
  (Verify RecursorProvenance) must move into `NativeIotaRestoration`,
  replacing the old `restored_iota_shape`, since the auto-merged Theory
  `NativeIotaSoundness` uses both and imports only `NativeIotaRestoration`.
- `RestoredRecursorShape` needs both imports. `RestoringExpansion`: take E1's
  side (mainline's private `specialization_liftN'` moved to
  `NativeIotaRestoration`; E1 renamed it `HeadSpecialization.apply_liftN`).
- First remaining build error after these: `Theory/Inductive/CaseRegistration.lean:186`
  (auto-merged), `rw [hnames …]` where `hnames` is no longer an equation
  (an E1/mainline change to the names field). Not yet resolved.

## Update (dry run continued)

- `CaseRegistration.lean:186`: `Certified.structCompat`'s pattern becomes
  `⟨expanded, auxiliaries, hdata, _, _, hnames, _⟩` (E1's `Certified` dropped
  `g` and added `RecursorNamesFresh` last); every field it reads is in
  `CaseCompilationData`.
- ShapeModel destructures `Certified` the old way
  (`⟨expanded, g, aux, hdata, hprior, hr, hnames⟩`) in about 15 places:
  EnvTablesRegistration, EnvSchemaMajors, EnvHeaderArity, EnvSigSchema,
  RuleValidGeneric(Syntax/Sem), RuleValidHistory, EnvSchemaTypes; mechanical.
- Real obstacle: `CaseSchema.Certified.genericType_closed` (EnvSchemaTypes.lean,
  `WF.eliminator_genericType_closed`) restores the generic case type by
  restoring the native recursor (`hdata.recursors`), absent from the case-only
  certificate; family index domains do not restore from `CaseCompilationData`.
  Decision: E1 adds the clause `∀ owner, ∃ RI, indices.mapM restoration.expr =
  some RI` (with the original-family header agreement folded in), which also
  discharges the indexed corner's `hhdr`.
- Scratch worktree with the partial resolution: /tmp/l4l-integrate (detached
  at 463c99d4, MERGE_HEAD f72c08fd, uncommitted).
