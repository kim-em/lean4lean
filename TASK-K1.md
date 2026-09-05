# Task K1: discharge `VContext.recursorRules` and `VContext.quotCoherent`

Worktree/branch: create a worktree from the main branch HEAD (after the projection registry
refactor has merged). Copy `.lake/build` from the main worktree first. Build with
`lake build`; check with `grep -rn sorry Lean4Lean/Verify/TypeChecker/Recursor.lean`.

## Goal

`Lean4Lean/Verify/TypeChecker/Recursor.lean` contains two `sorry` placeholders:

    theorem VContext.recursorRules (c : VContext) :
        RecursorRulesCoherent c.safety c.env.constants c.venv
    theorem VContext.quotCoherent (c : VContext) (h : c.env.quotInit = true) :
        QuotCoherent c.venv

Both predicates are defined in `Lean4Lean/Verify/Environment/Recursors.lean`, together with
monotonicity lemmas (`RecursorAlignment.mono`, `KLikeAlignment.mono`, `QuotCoherent.mono`,
`VEnv.RigidPreserving.*`). Replace the placeholders by fields carried through the checking
invariant, exactly the way `projectionRegistry : ProjectionRegistryCoherent ...` is carried
(see `CheckingEnv.Projectable` in `Lean4Lean/Verify/Environment/Lemmas.lean` and its
`add*` lemmas, `TrEnv.toCheckingValid`, and every `VContext` constructor in
`Lean4Lean/Verify/TypeChecker/Basic.lean` and the inductive `Run/*` files).

## Part 1: the invariant fields

Add to the checking invariant (the structure that `VContext.trenv` is built from) the fields

    recursorRules : RecursorRulesCoherent safety env.constants venv
    quot : env.quotInit = true → QuotCoherent venv

and prove preservation for every step that builds a checking environment:

- adding a non-recursor constant (`CheckingEnv.Valid.add` and friends): `RecursorRulesCoherent`
  only quantifies over `.recInfo` entries, so the new entry is irrelevant; the old entries are
  preserved by `RecursorAlignment.mono`, `KLikeAlignment.mono` with `venv ≤ venv'`
  (`VEnv.addConst_le`) and `VEnv.RigidPreserving.addConst`. `QuotCoherent.mono` likewise.
- adding projections: `VEnv.addProjections_le`, `VEnv.RigidPreserving.addProjections`.
- adding a definition's delta rule (`defn`/`mutualDef` steps of `TrEnv'`, or wherever
  `addDefEq` is used for definitions): the rule's left-hand side is `.const name ls` with `name`
  fresh, so `VEnv.RigidPreserving.addDefEq_fresh` applies to every existing constant; note that
  `RigidPreserving` is only needed for constants that exist (`venv.contains c`), and every rigid
  constant mentioned by the invariants (major inductives, `Quot`) exists.
- the `quot` step (`TrEnv'.quot`, `AddQuot` in `Verify/Environment/Basic.lean`): produce
  `QuotCoherent` from `AddQuot`: the four constants are added by `addConst` and the equation by
  `addDefEq quotDefEq`; `Quot` is rigid afterwards because the only new equation is headed by
  `Quot.lift` (`quotDefEq.lhs.stripLams.getAppFnArgs.1 = .const ``Quot.lift _` by `rfl`) and
  `Quot` was fresh before the step. Recursors already present stay aligned by monotonicity.
- the inductive installation boundary (`AddInduct` in `Verify/Environment/Basic.lean`,
  discharged in `CompletedBlockCertificate.addInduct` and the nested `Nested/FinalAssembly.lean`):
  this is the real work, Part 2.

Also record how `TrEnv.toCheckingValid` (the entry point from a complete `TrEnv`) obtains the
fields: by induction on `TrEnv'` using the step lemmas above.

## Part 2: the inductive step

For each recursor `rec` installed by the block (ordinary and nested/auxiliary), produce
`RecursorAlignment venv rec rec.numParams` and, when `rec.k = true`, the `KLikeAlignment` clause
of `RecursorRulesCoherent`.

`RecursorAlignment venv rec cnparams` needs, with `cnparams = rec.numParams`:

1. `VRecursorShape venv rec.name rec.levelParams.length rec.numParams rec.numParams rec.numMotives
   rec.numMinors rec.numIndices rec.getMajorInduct indLevels` for some `indLevels`: the abstract
   recursor type is `wrapForalls doms result` with
   `doms.length = numParams + numMotives + numMinors + numIndices + 1` and the major domain
   `doms[majorIdx] = mkApps (.const majorInduct indLevels) (bvarRange numParams majorIdx ++ bvarRange numIndices numIndices)`.
   Source: `VInductDecl.RecursorShape` / `NestedRecursorShape` (Theory/Inductive.lean, produced by
   `OrdinaryCompilation.recursors` and the nested compilation) give the telescope split by
   `takeForalls`; the major domain's syntactic form comes from the executable recursor
   construction (the major premise is the inductive type applied to the parameter and index free
   variables, then abstracted), see `GeneratedRecursorTelescopeTranslation` in
   `Verify/Inductive/Recursor/*` and the `finalCanonicalRecursorPrefixFrame` lemmas in
   `Verify/Inductive/CompletedEquationLhs.lean`. `VExpr.bvarRange` is in
   `Theory/Typing/RecursorLemmas.lean`.
2. `venv.Rigid rec.getMajorInduct`: no stored equation is headed (under its lambdas) by the
   inductive type constant. Every equation of the environment is headed by a definition name, a
   recursor name, or `Quot.lift`; the cleanest way is to carry, as part of the invariant, that
   every stored equation is headed by a constant whose `ConstantInfo` is not `.inductInfo`
   (state it as a predicate on `(C, venv)`, preserve it along the trace, and derive `Rigid` for
   inductive types from it). For the block itself the iota rules are headed by the new recursor
   names: `VInductDecl.IotaRule.lhs_pattern` with `lhs_wrapped` gives
   `rule.lhs.stripLams = mkApps (.const recursor.name _) _`; the nested auxiliary rules have
   `NestedIotaRule.lhs_pattern` (Theory/Inductive.lean:1426). Note `VExpr.stripLams` of
   `wrapLams doms body` is `body.stripLams`; if `body` is itself a lambda this differs, but iota
   rule bodies are applications.
3. For every `rule ∈ rec.rules`, a `df` with `RecursorRuleAlignment venv rec rule indLevels
   rec.numParams df`:
   - `VIotaRuleShape venv rec.name rec.levelParams.length rec.numParams rec.numParams
     rec.numMotives rec.numMinors rec.numIndices rule.ctor indLevels rule.nfields df`, i.e.
     `venv.defeqs df`, `df.uvars = rec.levelParams.length`, `df.lhs = wrapLams doms lhsBody`,
     `df.rhs = wrapLams doms rhsBody`, `df.type = wrapForalls doms typeBody`,
     `doms.length = numParams + numMotives + numMinors + nfields`, and
     `lhsBody = mkApps (.const rec.name (VLevel.params rec.levelParams.length))
        (bvarRange (numParams + numMotives + numMinors) doms.length ++ indexArgs ++
          [mkApps (.const rule.ctor indLevels)
            (bvarRange numParams doms.length ++ bvarRange nfields nfields)])`
     with `indexArgs.length = numIndices`. Source: `BoundGeneratedRecursorRule.EquationTranslation`
     (Verify/Inductive/Recursor/Rules.lean:2325) gives the wrapped shapes and
     `lhs_residual : TrExprS ... (H.sourceLhsBody.abstractList H.binders) lhsBody`, where
     `sourceLhsBody = mkAppN (mkAppN (mkAppN (mkAppN (.const recName lvls) params) motives) minors) indices).app major`
     with `params`, `motives`, `minors` the binder free variables (`BoundFVarArray`), so after
     `abstractList binders` they are the de Bruijn variables `bvarRange`; `abstractedParamsUnique`
     and `BoundFVarArray.abstractedUnique` (Rules.lean:2344) are the relevant lemmas, and
     `TrExprS.unique` turns unique syntax into the exact abstract term. The constructor major is
     `mkAppN (mkAppN (.const ctor ctorLevels) params) allArgs` with `allArgs` the field free
     variables. `ctorLevels` must be the `indLevels` of the recursor shape (the inductive's levels
     as seen from the recursor's level parameters), which the construction guarantees because the
     major premise's type and the constructor application use the same level list.
   - `TrExprS venv rec.levelParams [] rule.rhs df.rhs`: from `rhs_eq` in
     `BoundGeneratedRecursorRule` (the closed `mkLambda` form) and `rhs_residual` via the
     `mkLambda`/`abstractList` translation lemmas (`MLCtx.WF.mkLambda_trS` in
     Verify/TypeChecker/Basic.lean, `abstractForallContext` lemmas in Verify/Inductive).
   - `∃ ctorUvars, indLevels.length = ctorUvars ∧ VConstructorShape venv rule.ctor ctorUvars
     rec.numParams rule.nfields rec.numIndices rec.getMajorInduct`: the constructor's abstract type
     is `wrapForalls doms (mkApps (.const majorInduct (VLevel.params ctorUvars)) (bvarRange numParams (numParams + nfields) ++ indices))`
     with `doms.length = numParams + nfields` and `indices.length = numIndices`. Source: the
     constructor certificates (`VInductDecl.ValidIndAppAt` for the result, the parameter prefix
     being the common parameters; compare how `VContext.registryShape` is derived for
     structures).

`KLikeAlignment venv rec ctorName` (only when `rec.k = true`): the executable sets `k` exactly when
the block has one type, one constructor with zero fields, and the type lives in `Prop`
(`mkRecInfos`/`getElimLevel` in `Inductive/Add.lean`, certified in `Run/Formation.lean`). Needed:
`venv.constants majorInduct = some ⟨indUvars, wrapForalls indDoms (.sort .zero)⟩` with
`indDoms.length = numParams + numIndices`, `venv.constants ctorName = some ⟨indUvars, wrapForalls ctorDoms ctorBody⟩`
with `ctorDoms.length = numParams`, and for every `k`, `venv.IsDefEqU indUvars ((indDoms.take k).reverse) indDoms[k] ctorDoms[k]`
(the constructor's parameter binders are definitionally the type's parameter binders; the
executable checks this by `isDefEq` in `checkConstructors`, see Run/Constructors or wherever
`checkParams` is verified). Also `C.find? majorInduct = some (.inductInfo info)` with
`info.ctors = [ctorName]`.

## Constraints

- Do not change the statements of `RecursorRulesCoherent`, `RecursorAlignment`,
  `RecursorRuleAlignment`, `KLikeAlignment`, `QuotCoherent`, `VRecursorShape`,
  `VConstructorShape`, `VIotaRuleShape` unless a certificate genuinely cannot provide a clause; in
  that case state precisely what it can provide and adapt `Lean4Lean/Verify/TypeChecker/Recursor.lean`
  (`toCtorWhenK.WF`, `inductiveReduceRecTail.WF`, `quotReduceRecCont.*.WF`) accordingly, keeping
  them sorry-free.
- No new `sorry` anywhere; if a part cannot be finished, leave the placeholder theorem in place
  for exactly that part and document what is missing in its docstring.
- Commit in the worktree when the build is green; do not push. Report the commit hash, the files
  touched, and anything left out.

## Site map (added after the registry refactor merged)

The projection registry is carried as a field at exactly these places; mirror each for the
recursor rules (`RecursorRulesCoherent safety env.constants venv`) and the quotient facts
(`env.quotInit = true → QuotCoherent venv`), and also for `EquationHeadsCoherent env.constants venv`
if you use it to obtain rigidity:

- `CheckingEnv.Valid` (Verify/Environment/Lemmas.lean:901): field `projectionRegistry`; constructed
  by `TrEnv.toCheckingValid` (takes the facts as explicit arguments), `CheckingEnv.Valid.add`
  (per-constant step, uses `ProjectionRegistryStep`), `CheckingEnv.Valid.addProjections`
  (monotone), `CheckingEnv.ValidCore.toValid`, `CheckingEnv.Valid.mapExt`
  (Verify/Inductive/Nested/OrderInsensitiveAlignment.lean:229, transport by lookup equality;
  the recursor predicate depends on the map only through `find?`, use `ConstMap` lookup equality).
- `VEnvAt` (Verify/Environment/Extension.lean:255 region): field `projectionRegistry`; the
  `addAxioms`/definition steps prove it by the insert lemmas. Definitions add equations headed by
  the fresh definition name (`VEnv.RigidPreserving.addDefEq_fresh`, `EquationHeadsCoherent.addDefEq`).
- `ContextWF` (Verify/TypeChecker.lean:74) from `wf.projectionRegistryCoherent`
  (`InstalledInductiveProvenance.projectionRegistryCoherent`, Verify/Environment/Basic.lean);
  the analogous `InstalledInductiveProvenance.recursorRulesCoherent` is the certificate-level
  lemma to write for the inductive step.
- `VContext` (Verify/TypeChecker/Basic.lean:302) with `VContext.withMLC_projectionRegistry`;
  the constructions in Verify/TypeChecker.lean:130,143,186,240 (`mkCheckingValid`,
  `emptyChecking`, `runChecking`) pass `wf.projectionRegistry`.
- `StagedContextWF.complete` (Verify/Inductive/PrimitiveAtomicInstallation.lean:81) takes the
  facts as explicit arguments; its callers supply them from the primitive batch certificates.

Then replace the bodies of `VContext.recursorRules` and `VContext.quotCoherent`
(Verify/TypeChecker/Recursor.lean) by the new `VContext` fields.
