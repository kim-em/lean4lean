# Scoping report: replacing `IsDefEqU.weakN_iff`

Worktree `agent/verify-inductives` at commit 5051e0d, 2026-10-06. This was a read-only investigation. The dependency data was extracted from the built oleans with a scratch meta-program (`/tmp/l4l-scratch/WeakNGraphAll.lean`). It imports 580 of the 581 source modules that have up-to-date oleans; `Nested/RestorationAgreement` and `RestorationCommutation` were excluded because of a duplicate declaration while those files are being edited. It walks the type and value of every constant, including opaque theorem bodies.
- `/tmp/l4l-scratch/weakn-graph-all.tsv`: every dependent constant, one row each. Columns: name, module, kind, whether it is in the `addDecl.WF` cone, dependent direct dependencies, and line.
- `/tmp/l4l-scratch/layer1.tsv`: the direct use sites.
- `/tmp/l4l-scratch/layer2.txt`: the direct consumers of each use site.

## 0. Headline findings

1. **The dependency graph is much larger than the textual count.** 3445 constants depend transitively on `IsDefEqU.weakN_iff`, and 1523 of them are in the `addDecl.WF` cone (35579 constants).
   - There are 67 direct use sites outside `UniqueTyping.lean`, plus 14 family lemmas inside it.
   - **Every declaration kind depends on it**, through the type checker: `addAxiom.WF -> checkConstantVal.WF -> ... -> ensureSort.WF -> RecM.WF.run -> isDefEqCore'.WF -> quickIsDefEq.WF -> IsDefEqU.weak'_iff`.
   - `addDefinition.WF` also goes through `M.WF.withLocalDecl -> ConditionallyWHNF.weakN_inv`.
   - The inductive path goes through `CheckedSourceHeaderTranslation.checkedLaterForall -> initialLaterHeaderDefEqOfTranslation`.
   - **No module in `Theory/Inductive/*` (the inductive spec) depends on `weakN_iff`.**
2. **Weaker statements are false as well.** Existential `VExpr.WF` strengthening, `IsType` strengthening, typing at sort types, `OnCtx.weakN_inv` with k>0, and `TrExprS.weakFV'_inv` are all false, given the STRENGTHENING.md countermodel together with the branch's own base conjectures.
   - The argument: in Γ with `z : SI`, the term `t := (fun x : SJ => x) z` is well typed in `Γ, q : P v`.
   - Suppose `Γ ⊢ t : V`. Then `HasType.app_inv` (Strong.lean:1157), the lambda's own typing, `uniq`, and `IsDefEqU.forallE_inv` (Injectivity.lean:22, a sorried base conjecture) give `Γ ⊢ SI ≡ SJ`, which the model refutes.
   - `(fun x : SJ => Prop) z` does the same for `IsType` and for typing at sort types.
   - So HANDOFF's hope that "consumers mostly need existential WF strengthening and strengthening at sort types, which the countermodel does not refute" does not hold. Those targets are inconsistent with `forallE_inv`, conditional on the soundness of the model, which is argued in prose but not formalized.
   - Neither of these restrictions helps:
     - "both endpoints are well typed in the smaller context": SI and SJ both have type `Type` there;
     - closedness: the smaller-context variables can be axioms.
3. **The only true inverse principles available:**
   - (i) **Substitution:** `IsDefEq.instN` (Theory/Typing/Lemmas.lean:915) gives strengthening whenever each removed binder has an inhabitant in the smaller context.
   - (ii) **Round trip:** keep the fact that was originally established in the small context.
   - (iii) **Syntactic strengthening:** strengthening of untyped relations.
   - (iv) **Uniqueness plus `sort_inv`:** when the term is already known to be typed in the small context and the target is a sort.
   - (v) **A new executable-locality theorem:** a fresh checker run on inputs whose fvars lie in a dependency-closed set S only consults S, so it can be replayed in the context restricted to S. It is true, missing, and large.
   - (vi) **Changing the executable** so that it does not carry facts across scope exit: save and restore the caches and the `EquivManager` around `withLocalDecl`/`withLetDecl`.

## 1. The statements

`Lean4Lean/Theory/Typing/UniqueTyping.lean`; each statement has `henv : VEnv.WF env` and `hΓ : OnCtx Γ' (env.IsType U)`:

```lean
-- :203  (the sorry is at :205; the .2 direction is the true IsDefEqU.weakN)
theorem IsDefEqU.weakN_iff (W : Ctx.LiftN n k Γ Γ') :
    env.IsDefEqU U Γ' (e1.liftN n k) (e2.liftN n k) ↔ env.IsDefEqU U Γ e1 e2
```

Derived family, all false in the `.1` direction (or false outright):

| line | lemma | notes |
|---|---|---|
| 208 | `VExpr.WF.weakN_iff` | definitionally `IsDefEqU.weakN_iff`; false, see 0.2 |
| 211 | `IsDefEq.skips` | |
| 221 | `IsDefEq.weakN_iff'` | |
| 229 | `OnCtx.weakN_inv` | true only for `.zero` (k = 0, trailing drop) |
| 242 | `IsDefEq.weakN_iff` | |
| 247 | `HasType.weakN_iff` | |
| 252 | `IsType.weakN_iff` | |
| 257 | `HasType.skips` | |
| 262 | `IsDefEqU.weak'_iff` | |
| 275 | `IsDefEq.weak'_iff` | |
| 288 | `HasType.weak'_iff` | |
| 293 | `IsType.weak'_iff` | |
| 298 | `VExpr.WF.weak'_iff` | |
| 302 | `OnCtx.weak'_inv` | |

The true direction already exists: `IsDefEq.weakN` (Theory/Typing/Lemmas.lean:696), `HasType.weakN` (768), `IsType.weakN` (772), `IsDefEqU.weakN` (784) and the `weak'` analogues. These are not sorried, and the inverse lemmas below wrap them as well.

Derived lemmas (second layer) that are false as stated and must be restated or deleted:
- `VLocalDecl.weak'_iff` / `weakN_iff` (Verify/Typing/Lemmas.lean:356/362)
- `VLCtx.FVLift'.wf` (451) / `BVLift.wf` (572)
- `TrProj.weak'_inv` (833)
- `TrExprS.weakFV'_inv` (1291) / `weakFV_inv` (1367)
- `TrExprS.weakBV_inv` (LevelEquiv.lean:172)
- `ConditionallyHasType.weakN_inv` (ConditionallyTyped.lean:58) / `ConditionallyWHNF.weakN_inv` (128)
- `VExpr.WF.of_occurs` (ProjectionLemmas.lean:480)
- `WHRed.weakU_inv` (HeadReduction.lean:129)
- `FullWHRed(S).weak'_inv` (FullHeadStrengthening.lean:14/61). HANDOFF item 8 proposes building on this one; it is tainted.
- `NormalEq.weakN_inv_DFC` / `NormalEq.weakN_iff` (ChurchRosser.lean:492/614)
- `ParRed.weakN_inv` (1163)
- `CaseStep`/`MatchedCaseStep.weak{N,'}_inv` (CaseReduction.lean:366/412/545/582)
- `NativeSpineMatch`/`NativePrefixReplay.weak'_inv` (NativePrefixStrengthening.lean:24/57)
- `TrExprS.weakBV_inv_lift` (CanonicalRecursiveShape.lean:67)
- `MLCtx.restrictUpSet`/`restrictUpSetCtx` (Recursor/ContextRestriction.lean)

## 2. Consumer graph, summary

`layer1.tsv` lists 67 direct use sites (constants outside UniqueTyping that reference a family lemma); 39 are in the cone. They are classified per file in sections G1 to G4 below. By module (total dependents / dependents in the cone), the largest are:
- `Nested/FinalAssembly` 270/99, `Nested/AssemblyProviderEvidence` 190/1
- `Equation/Setup` 188/67, `PrimaryIotaTrace` 89/22
- `CompletedEquationRecursiveCall` 83/52, `CompletedEquationCanonical` 82/46
- `Recursor/CanonicalConstruction` 70/47, `EquationWF` 67/49
- `ConsumedGenerationAssembly` 59/55, `CanonicalRecursorTelescope` 51/51

Hub use sites, by number of transitive dependents (and how many are in the cone):

| site | dependents (cone) | class |
|---|---|---|
| `VLocalDecl.weak'_iff` -> `FVLift'.wf` | 3332 (1461) | (c) as stated; repaired at callers |
| `TrProj.weak'_inv`, `TrExprS.weakFV'_inv` | 3042 (1218) | (c) as stated |
| `VLocalDecl.weakN_iff` -> `BVLift.wf` | 2863 (1099) | (c) as stated; repaired at callers |
| `ConditionallyHasType`/`ConditionallyWHNF.weakN_inv` -> `withLocalDecl`/`withLetDecl` | 2844 (1077) | (c); needs E1/E2/E3 (G2) |
| `VIotaRuleShape.args_typing` | 2822 (1064) | (b) once a domain-agreement field is added |
| `VExpr.WF.of_occurs` | 2820 (1062) | (b) by a direct proof at its single user |
| `TrExprS.weakBV_inv` | 2814 (1054) | mostly (b) via the projection inhabitant; one Prop-structure corner stays open |
| `quickIsDefEq.WF` | 2809 (1051) | (c); the checker cache, same fix as `withLocalDecl` |
| `RecursorMotiveTelescopeSeed.consumedTranslation` | 2646 (981) | (b) via locality |
| `TrExprS.weakBV_inv_lift` | 2549 (912) | (c) as a lemma; fixed forward at the caller |
| `NarrowRuntimeScope.hasTypeOfFull` | 2528 (886) | (b) once an `IsType` premise is added (`sort_inv` route) |
| `ConsumedDomain.proof_of_largeEliminationCheck` | 2510 (875) | (b) via `sort_inv`, about 15 lines |

Class totals over the 67 sites:
- **(a), pure weakening:** 2 sites, `FirstPass.lean` `parameterStepOfCheckedRecursorHeader` (cone) and `parameterStepOfCheckedHeader` (off cone). Each is a one-line swap to `IsDefEqU.weakN`.
- **(b)** splits by how it is repaired:
  - by local evidence or an extra premise (lookup, `sort_inv`, uniqueness, substitution, domain field): about 12 sites;
  - by executable locality: about 15 sites.
- **(c):**
  - the checker-cache cluster: 5 sites;
  - false lemmas whose consumers must be rebuilt by construction: about 12 sites;
  - off-cone false lemmas, to delete or reduce to their syntactic part: about 20 sites.

## 4. Effect on the final theorems

- `Theory/Inductive/*` (the inductive spec) needs no change; none of it depends on `weakN_iff`.
- Whether `addDecl.WF` (Verify/Environment.lean:462) changes depends on the checker-cache cluster (G2):
  - **E1:** change the executable so that it saves and restores the infer/whnf caches and the `EquivManager` around `withLocalDecl`/`withLetDecl`, and always opens a binder in `isDefEqLambda`/`isDefEqForall`. Also re-check the Primitive gadget pieces in the empty context and re-infer `F`/`natRec` in `unfoldNatWellFounded`. With these, **neither the hypotheses nor the conclusion of `addDecl.WF` change**; only the executable does. The cost is a departure from the C++ kernel and possibly performance; benchmark the `Std` replay.
  - **E2:** prove executable locality. Thousands of lines. The union-find in the `EquivManager` still needs scoping, because transitivity through a middle term that mentions the removed variable is exactly the countermodel's `SI ≡ K v q ≡ SJ`.
  - **E3:** keep the executable and add a hypothesis to `addDecl.WF` that the environment validates context strengthening. This really restricts the theorem: it fails for Lean-valid environments (the countermodel environment needs no `Eq`). `addDecl.WFCanonicalEq` (Environment.lean:480) already assumes `CanonicalEqEnvs`, and STRENGTHENING.md notes that `Eq` defeats this particular model. But there is no theorem that `Eq` restores strengthening, so this would be a new unproved hypothesis, not a repair.
- **The inductive-side clusters (G3/G4) do not touch any final statement.** They need either locality (E2 restricted to fresh checker runs on fvar upsets, which is cheaper than full cache locality: about 1.5k-8k lines) or producer changes that keep a narrow-context run, for example checking later headers and family indices in a parameters-only context.
- **Junction sorries:**
  - `canonicalConsumedGeneration` and `canonicalCompletedRuleTranslation` are closed proofs now, but both rest on false lemmas: `weakBV_inv_lift`, `consumedTranslation`, `FVLift'.wf`, and the `NarrowScope.scopeWF` fields of `CompletedRecursorConstruction` (G4).
  - HANDOFF item 7's shape-definition program (`restrictUpSetCtx`, `weakFV'_inv`) is built on a false lemma and must be redesigned on locality.

## 5. Plan (ordered), with suggested true statements

1. **Trivial and dead code** (about 1 day).
   - Swap the 2 class (a) sites to `IsDefEqU.weakN`.
   - Delete the unused false lemmas:
     - `HasType.skips` (both copies), `InstForalls.defeq`, `VExpr.WF.of_inst_occurs`, `HasType.proj_weakN_iff`
     - `ProjectionDesugaring.weakN_inv`/`weak'_inv`, `ownerMotiveFirstDomainDefEq`, `dropFVarPrefix_*`
     - `hasTypeOfFullPair` (LoopType 832/1180)
     - `ContextRestriction.lean`, `Bindings.lean:138`, `RecursiveShapeRow.lean:68`
     - the off-cone `Equation/*` twins (after a full cone check)
   - Mark the off-cone Theory inverses (CaseStep, ParRed, NormalEq, WHRed, FullWHRed, NativePrefix) as either deleted or reduced to their syntactic content: "the reduct is a lift".
2. **Split `UniqueTyping` honestly.**
   - Delete `weakN_iff` and its family.
   - Keep `OnCtx.of_append` for the k = 0 drop.
   - Add `IsDefEq.strengthen_of_inhabited` for the substitution case (a wrapper around `instN`).
   - Add `HasType.strengthen_sort`: `Γ ⊢ A : sort v` together with `Γ' ⊢ A↑ : sort u` gives `Γ ⊢ A : sort u`, via `uniq` and `sort_inv`.
   - About 100-200 lines.
3. **Restate the context-WF lemmas.** Change `FVLift'.wf`/`BVLift.wf` to take `Δ.WF`, which callers have through `H.context.wf` or the scope structures, and restate `VLocalDecl.weak*` as one direction only. About 100-300 lines of caller churn.
4. **Theory cone sites** (G1).
   - `VExpr.WF.of_occurs`: direct proof at `field_typing_of_ctorApp`, 100-200 lines.
   - `VIotaRuleShape`: add a domain-agreement field and discharge it at its producers (`Recursors.lean:60`, `RecursorAlignment.lean:37/247`, `GeneratedShapes.lean:81`), 150-400 lines.
5. **Checker caches** (G2, decision E1/E2/E3). With E1: 20-40 executable lines, about 300 proof lines, plus the Primitive re-checks (about 10 executable lines, 150-300 proof lines) and benchmarking.
6. **Locality for fresh runs.** Prove the theorem: if a fresh run's inputs have fvars in an `IsFVarUpSet`, its WF conclusion holds in the restricted context. The scopes already carry `upset` fields (LoopType.lean:689/1015, RecursiveCallScope.lean:26).
   - Then restate `NarrowRuntimeScope.restrict`, `FVarNarrowScope.restrict`, `FVarNarrowCore.restrict` and `restrictTrExpr` to consume narrow-run evidence instead of `weakFV'_inv`.
   - Cost: 1.5k-8k lines for the theorem, then 40-150 lines per site (about 15 sites). Producer changes that keep a narrow run are an alternative.
7. **Rebuild by construction** (G3/G4): `canonicalApplicationContext`, `mkApps_canonical_prefix`, `cancelLiftForallDomains`, the `hasTypeOfFullPair` users, `weakBV_inv_lift` (replace with `weakBV` plus `uniqueS` from a small-scope translation), `consumedTranslation`, `finalSelectedMinorNarrowFieldAlignment`. About 1-2.5k lines.
8. **Out of the `addDecl.WF` cone:** the Church-Rosser eta/eta case of `NormalEq.trans` needs the redesign in STRENGTHENING.md. That is research-sized and affects only the `full_church_rosser`/`headParallel` audit roots.

**Total estimate**, excluding the Church-Rosser redesign:
- with E1 and locality: about 4k-12k lines;
- the cheapest honest route (E1 plus producer changes instead of a general locality theorem): about 3k-5k lines.

The per-group detail follows.

## G1: Theory/Typing use sites

All paths under `Lean4Lean/Theory/Typing/`. "Cone" = in the `addDecl.WF` dependency cone
(per `/tmp/l4l-scratch/weakn-graph-all.tsv`). Every site below uses the `.1` (strengthening)
direction; none is class (a). Only two G1 sites are in the cone: `VExpr.WF.of_occurs` and
`VIotaRuleShape.args_typing`. Everything else feeds only the Church-Rosser / full-reduction
audit roots (`full_church_rosser`, `headParallel`, `NormalEq.fullStep`) or nothing.

Under the framing (countermodel plus `forallE_inv`), every relation here that carries typed
side conditions (`CaseStep`, `MatchedCaseStep`, `WHRed` `.schema`/`.extra`, `FullWHRed`
`.projIota`/`.delta`/`.quotDelta`, `NativeSpineMatch`, `NativePrefixReplay`, `ParRed`
`.schema`/`.extra`, `NormalEq` leaves) has a strengthening lemma that is **false as stated**:
take the typed premise to be about `(fun x : SJ => x) z` or `SI ≡ SJ`.

### Out of cone (Church-Rosser / reduction strengthening): all class (c)

| file:line | theorem | family use | removed / source | class, repair |
|---|---|---|---|---|
| CaseReduction.lean:366 | `CaseStep.weakN_inv : CaseStep Γ' rule levels (args.map liftN) → CaseStep Γ rule levels args` | `HasType.weakN_iff`.1 at 374, 378 (lhs/rhs equation typing, closed terms), 386 (argument typing `args[i] : dom_i[args.take i]`) | arbitrary LiftN n k | lhs/rhs parts: (b), since they are closed instL instances of a stored env equation; derive in `[]` from `env.WF` and weaken. Argument typing: (c). Statement false. Users: only `MatchedCaseStep.weakN_inv`. |
| CaseReduction.lean:412 | `CaseStep.weak'_inv` (Lift' analogue) | `HasType.weak'_iff`.1 | Lift' ρ | same as above, (c). Users: `MatchedCaseStep.weak'_inv`. |
| CaseReduction.lean:545 | `MatchedCaseStep.weakN_inv` | `CaseStep.weakN_inv` and `IsDefEqU.weakN_iff`.1 at 562 (guard defeq `lhs[actual] ≡ actual`) | LiftN | (c): guard defeq strengthening is exactly the refuted shape. User: `ParRed.weakN_inv`. |
| CaseReduction.lean:582 | `MatchedCaseStep.weak'_inv` | as above with `weak'_iff` | Lift' | (c). User: `AppliedSchemaReduction.weak'_inv` (1008), then `WHRed.weakU_inv`, `FullWHRed.weak'_inv`. |
| ChurchRosser.lean:480 | private `HasType.proj_weakN_iff` | `HasType.weakN_iff` | LiftN | false, **0 users**: delete. |
| ChurchRosser.lean:492 | `NormalEq.weakN_inv_DFC (W : LiftN n k Γ Γ₂) (W₂ : IsDefEqCtx Γ₀ Γ₁ Γ₂) (H : Γ₁ ⊢ e1↑ ≡ₚ e2↑) : Γ ⊢ e1 ≡ₚ e2` | 501/507 (`IsDefEqU`, elim/refl leaves), 527/530 (`WF` of apps), 532 (`IsDefEqU`, domain agreement), 546 (`WF` proj), 552/560 (`IsDefEq` at sort), 561 (`HasType` at sort), 577/579, 595/597 (eta: `IsDefEqU`, `IsDefEq` at forallE), 606, 609-611 (proofIrrel), plus `OnCtx.weakN_inv` (523, k>0) | arbitrary LiftN | (c): `NormalEq` leaves are typed defeqs, so the statement is false. Users: `NormalEq.weakN_iff` (614). |
| ChurchRosser.lean:614 | `NormalEq.weakN_iff : Γ' ⊢ e1↑ ≡ₚ e2↑ ↔ Γ ⊢ e1 ≡ₚ e2` | wrapper | | **False theorem, must be restated** (keep only `.2` = `NormalEq.weakN`). Essential consumer: `NormalEq.trans` eta/eta case (670), with `.one`, removing the fresh lambda binder `A`. No inhabitant of `A` exists. Needs the redesign in STRENGTHENING.md (a bound-indexed comparison closing by lam congruence plus eta instead of erasing the binder). Downstream (16, none in cone): `NormalEq.trans`, `ParRed.triangle/church_rosser`, `ParRedS.church_rosser`, `CRDefEq.trans`, `NormalEq.parRed(S)`, `NormalEq.fullStep(_funEta)`, `fullReduction`, `FullReduction.church_rosser`, `IsDefEq.church_rosser`, `IsDefEq.full_church_rosser`. |
| ChurchRosser.lean:1163 | `ParRed.weakN_inv (h : Γ' ⊢ e1↑ : A) (H : Γ' ⊢ e1↑ ≫ e2') : ∃ e2, Γ ⊢ e1 ≫ e2 ∧ e2' = e2↑` | `MatchedCaseStep.weakN_inv` (1206, schema), `IsDefEqU.weakN_iff`.1 at 1244 (pattern `extra` guard) | LiftN | (c), false (the guards are typed defeqs). Note the other cases need only inversion (`app_inv`, `lam_inv`, base conjectures) in Γ'. Possible true variant: make `ParRed`'s guards context-independent or strengthen only along an inhabited context. User: `NormalEq.parRed` (2169; already sorried nearby at 2165). |
| ChurchRosser.lean:1779 | `hasType_app_bvar0 (H : A :: Γ ⊢ e.lift.app (bvar 0) : B) : ∃ B', Γ ⊢ e : forallE A B'` | `IsDefEqU.weakN_iff`.1 `.one` at 1790 (eta defeq) | removes the fresh binder `A` | (c), false: `e := (fun x : SJ => fun _ : P v => x) z` with `A := P v`. User: `ParRedExt.parRed_beta`. |
| ChurchRosser.lean:1795 | `ParRedExt.parRed_beta` | `IsDefEqU.weakN_iff`.1 `.one` at 1850 and 1910, `HasType.weakN_iff` (sort) at 1912; also uses `hasType_app_bvar0` | `lift` layer of `ParRedExt`: removes the binder introduced by an eta layer | (c). Same redesign as `NormalEq.trans` eta. User: `NormalEq.parRed`. |
| HeadReduction.lean:129 | `WHRed.weakU_inv (H : Γ' ⊢ e1.lift' ρ ⤳ e2') : ∃ e2, e2' = e2.lift' ρ ∧ Γ ⊢ e1 ⤳ e2` | `IsDefEqU.weak'_iff`.1 at 159 (`extra` guard) and `AppliedSchemaReduction.weak'_inv` (schema) | Lift' | **False theorem** ((c)). Users: `WHRedS.weakU_inv` (448, 0 users) and `FullWHRed.weak'_inv`. True replacement: the untyped (syntactic) part only, i.e. "the reduct is a lift" (`∃ e2, e2' = e2.lift' ρ`). That holds for each rule, so state it separately without the `Γ ⊢ e1 ⤳ e2` conjunct. |
| FullHeadStrengthening.lean:14 | `FullWHRed.weak'_inv` (and `FullWHRedS.weak'_inv` at 61) | `VExpr.WF.weak'_iff`.1 (42), `HasType.weak'_iff`.1 (46) in `projIota`; `WHRed.weakU_inv`, `NativeDeltaRule.weak'_inv`, `QuotDeltaRule.weak'_inv` | Lift' | **False** ((c)). 0 users downstream (`FullWHRedS.weak'_inv` has no users). HANDOFF item 8 proposes building on `FullWHRedS.weak'_inv`, which is tainted. Same syntactic-only replacement as for `WHRed`. |
| NativePrefixStrengthening.lean:24 | `NativeSpineMatch.weak'_inv` | `IsDefEqU.weak'_iff`.1 on the argument list (`Forall₂`) | Lift' | (c), false. User: `NativePrefixReplay.weak'_inv`. |
| NativePrefixStrengthening.lean:57 | `NativePrefixReplay.weak'_inv` | `HasType.weak'_iff`.1 (`source_typed`); `captures_typed` lives in `domains.reverse ++ Γ` | Lift' | (c), false. Users: `NativeDeltaRule.weak'_inv` (131) and `.weakN_inv` (158), `QuotPrefixStrengthening.lean:42` `QuotDeltaRule.weak'_inv` and `.weakN_inv` (58). All of these lead only to `FullWHRed.weak'_inv`, out of cone. |
| ProjectionLemmas.lean:42 | `InstForalls.defeq` | `IsDefEqU.weakN_iff`.1 `.one` at 73 (vacuous/vacuous case: strengthen `hB : A::Γ ⊢ B↑ ≡ B'↑`) | removes the forall binder `A` | (c) in that case (no inhabitant: the vacuous binder's argument is untyped by design). **0 users**: delete, or restate the vacuous/vacuous case with a hypothesis `HasType Γ a A` (then use `instN`). |
| ProjectionLemmas.lean:183 | `VExpr.WF.of_inst_occurs` | `IsDefEqU.weakN_iff`.1 `.zero Δ` (197): strengthen `WF (Δ++Γ) (a↑)` to `WF Γ a` | binders Δ above `a` | **False** ((c)): the subterm can sit under a `P v` binder. **0 users**: delete. |

Repair size, out of cone: `ParRed.weakN_inv`, the four `CaseStep` inverses, `WHRed(S).weakU_inv`,
`FullWHRed(S).weak'_inv`, `Native*/Quot*` `weak'_inv`/`weakN_inv`, `proj_weakN_iff`,
`InstForalls.defeq` and `of_inst_occurs` can be deleted (about 450 lines) or downgraded to the
syntactic "reduct is a lift" statements (about 100 lines). Their only live consumers are
`NormalEq.parRed` and the eta cases. The real cost is the Church-Rosser redesign of `NormalEq.trans`
eta/eta and `parRed_beta` lift (STRENGTHENING.md, "Consequence"). That is research-sized, but it sits
outside `addDecl.WF`.

### In cone

**ProjectionLemmas.lean:480, `VExpr.WF.of_occurs`**
`∀ Δ, Occurs a e Δ.length → OnCtx (Δ++Γ) → WF (Δ++Γ) e → WF Γ a`. It uses
`IsDefEqU.weakN_iff`.1 `.zero Δ` (490), where Δ is the binders of `e` above the occurrence.
- **Statement false (c)**: `e := fun q : P v => (fun x : SJ => x) z`.
- True restricted version: the `Δ = []` occurrence path (no `lamB`/`forallB` steps). Occurrences
  in a domain (`lamA`/`forallA`), the function or argument of an `app`, or a projection major
  need no strengthening.
- Only user: `VProjectionInfo.field_typing_of_ctorApp` (923; call at 1030 with `Δ = []`).
  The occurrence there is of `proj S j sm` (j < index) inside the instantiated field type `D`.
  `D` may be a Pi, so the occurrence can be under binders, and the general lemma is needed.
- Repair (b), origin available: show `WF Γ (proj S j sm)` directly. The major `sm` is typed at
  the structure type in Γ (`hsm`). Projection typing for every earlier field index should follow
  by induction on `index` from the projection data (`proj_inv` gives `hfield`/`hFty` for
  `index`; the field telescope before `index` is typed in Γ). This needs a new lemma
  "`proj S j major` is typed for `j < index` whenever `proj S index major` is", about 100-200
  lines. Projection typing premises are close to inversion territory, so this may lean on
  existing base conjectures but not on strengthening.
- Downstream: 2819 constants, 1061 in cone. These include every `Primitive.check*.WF`
  (Verify/Environment/Primitive/*), `Primitive.checkDef.WF`, and through them `addDecl.WF`.

**RecursorLemmas.lean:596, `VIotaRuleShape.args_typing`**
Actual recursor-application arguments are typed along the stored rule telescope. Uses:
- `OnCtx.weakN_inv` at 712 with `W : LiftN (len-j) 0 ...`. That is the k = 0 suffix drop, which
  is true: use `OnCtx.of_append` (590), class (a).
- `IsDefEqU.weakN_iff`.1 at 715 (parameter/motive/minor positions) and 752 (field positions).
  These strengthen `hU : doms'.reverse++Γ ⊢ (declared rule domain j)↑ ≡ (recursor/constructor
  telescope domain j)↑` to the prefix context `(doms'.take j).reverse ++ Γ`, removing the later
  rule binders `j..len-1`.
- The defeq's origin is the typing of the rule LHS in the **full** rule telescope (`Hrule.body_typing`,
  then `Hrec.spine_typing`/`Hctor.spine_typing`, then `uniqU`). There are no inhabitants of the
  later binders, so as stated it is (c).
- Repair (b) by strengthening the invariant: add a field to `VIotaRuleShape` (RecursorLemmas.lean:443),
  e.g. `doms_agree : ∀ j, doms[j]` is (syntactically, or prefix-context defeq) the recursor
  domain `j` instantiated with `bvarRange` for `j < m`, and the constructor field domain for
  fields. Then 715/752 read it off without strengthening. Constructors of the shape to update:
  `Verify/Environment/Recursors.lean:60` (Quot.lift, explicit), `Verify/Environment/RecursorAlignment.lean:37/247`
  (`mono` is trivial), and `Verify/Inductive/Recursor/GeneratedShapes.lean:81` (generated rules,
  where the domains are literally the recursor binder types, so syntactic equality should be cheap).
  Estimate 150-400 lines.
- Downstream: `VIotaRuleShape.iota` (838) and `iota_body` (1089, used by `Verify/TypeChecker/Recursor.lean:172`).
  That is 2822 constants, 1064 in cone, including the type checker's iota soundness and so
  every `addDecl.WF` path.

### Theory lemmas whose statements are false and must be restated or deleted
`NormalEq.weakN_iff` (keep `.2`), `NormalEq.weakN_inv_DFC`, `ParRed.weakN_inv`, `hasType_app_bvar0`,
`WHRed.weakU_inv`, `WHRedS.weakU_inv`, `FullWHRed.weak'_inv`, `FullWHRedS.weak'_inv`,
`CaseStep.weakN_inv`/`weak'_inv`, `MatchedCaseStep.weakN_inv`/`weak'_inv`,
`AppliedSchemaReduction.weak'_inv`, `NativeSpineMatch.weak'_inv`, `NativePrefixReplay.weak'_inv`,
`NativeDeltaRule.weak'_inv`/`weakN_inv`, `QuotDeltaRule.weak'_inv`/`weakN_inv`, `VExpr.WF.of_occurs`
(restrict to `Δ = []`), `VExpr.WF.of_inst_occurs`, `InstForalls.defeq` (vacuous/vacuous case),
`HasType.proj_weakN_iff`.
# G2: Verify/Typing, TypeChecker caches, Primitive

Paths are relative to the worktree. Every site below uses the **.1 (strengthening)** direction; none uses only `.2`.
"CONE" means the site is inside the `addDecl.WF` dependency cone (Verify/Environment.lean:462).

## Hub lemmas in Verify/Typing/Lemmas.lean

| site | statement | family use | removed | class |
|---|---|---|---|---|
| `VLocalDecl.weak'_iff` Lemmas.lean:356 (CONE) | `VLocalDecl.WF Γ' (d.lift' n) ↔ VLocalDecl.WF Γ d` | `IsType/HasType.weak'_iff` .1 | arbitrary `Lift'` | (c) as stated. Its only user is `FVLift'.wf`. Replace it with the `.2` direction only (`VLocalDecl.weak'`, true) |
| `VLocalDecl.weakN_iff` Lemmas.lean:362 (CONE) | same for `LiftN` | `.1` | arbitrary `LiftN` | (c). Its only user is `BVLift.wf`. Keep only `VLocalDecl.weakN` |
| `VLCtx.FVLift'.wf` Lemmas.lean:451 (CONE, about 3330 transitive dependents) | `FVLift' Δ Δ' → Δ'.WF → Δ.WF` | `VLocalDecl.weak'_iff.1` in the `cons_fvar`/`cons_bvar` cases | fvars dropped *below* later entries | (c) in general: this is context strengthening with k>0, which is false by the `(fun x:SJ => x) z` argument. In the `skip_fvar`-only case (head drop) it is true and trivial (the tail). **Repair:** callers supply `Δ.WF` themselves. Callers: `TrExprS.weakFV'_inv`, `VLCtx.FVLift.wf` (536), `MLCtx.restrictUpSetCtx` (off-cone), `CompletedRecursorConstruction.consumedMotiveAtParameters` (CanonicalMotiveReplay.lean:51), `finalSelectedMinorNarrowFieldAlignment` (CompletedEquationRecursiveCall.lean:2511 and Equation/RecursiveCall.lean:2538), and `FVarNarrowCore.scopeWF` (Equation/RecursiveCallScope.lean:67), `FVarNarrowScope.scopeWF` (Header/LoopType.lean:1050), `NarrowRuntimeScope.scopeWF` (LoopType.lean:730). The last three all have the form `H.lift.wf henv H.context.wf`; whether the narrow scope's own WF is available at construction is for the G3/G4 analysis |
| `VLCtx.BVLift.wf` Lemmas.lean:572 (CONE) | `BVLift Δ Δ' → Δ'.WF → Δ.WF` | `VLocalDecl.weakN_iff.1` | bvars inserted below `cons` entries | (c) in general, and true if `BVLift` is only `skip`. Same repair (callers supply `Δ.WF`). Callers: `TrExprS.weakBV_inv`, `TrExprS.weakBV_inv_lift` and `removeBeforeInner` (CanonicalRecursiveShape.lean:67 and 258) |
| `HasType.skips` Lemmas.lean:829 | wrapper of `IsDefEq.skips` | `.1` | | dead (0 users): delete |
| `TrProj.weak'_inv` Lemmas.lean:833 (CONE) | projection side conditions `VExpr.WF` strengthen | `VExpr.WF.weak'_iff.1` | `Lift'` | (c): existential WF strengthening. Only used in the `proj` case of `weakFV'_inv`; it goes with that lemma |
| `TrExprS.weakFV'_inv` Lemmas.lean:1291 (CONE, about 3040 dependents) | `TrExprS Δ₁ e e'`, Δ₁≡Δ₂ ⊒ Δ via `FVLift'`, e closed with fvars in Δ ⟹ `∃ e', TrExprS Δ e e'` | `VExpr.WF.weak'_iff.1` (app case, on `f₁.app a₁`), `HasType.weak'_iff.1` at sort types (lam/forallE/letE), `TrProj.weak'_inv`, `FVLift'.wf` | arbitrary fvars not mentioned by e | **(c), false as stated**: the Lean expression `(fun x : SJ => x) z` translates only in the larger context. No general true replacement. True restricted forms: (i) *substitution form*: if every dropped fvar has an inhabitant in Δ, then `TrExprS.instN`/`inst_fvar` (Lemmas.lean:1427) gives the translation, the source expression being unchanged because it does not mention the variable; (ii) *round trip*: consumers keep the translation they already had in Δ |
| `TrExprS.weakFV_inv` Lemmas.lean:1367 | `FVLift` wrapper | | | same as `weakFV'_inv` |

### Direct consumers of `TrExprS.weakFV'_inv` (12) and of `weakFV_inv` (14)

`weakFV'_inv`:
1. `TrExprS.weakFV_inv` (Lemmas.lean:1367): wrapper.
2. `MLCtx.restrictUpSet` and `restrictUpSetCtx` (Recursor/ContextRestriction.lean): off-cone. They restrict the context to an up-set; no smaller-context origin by construction.
3. `CompletedRecursorPhasesResult.finalOwnerNarrowMotiveTranslationAt` (CompletedEquationMotive.lean:1084, CONE) and its `Equation/Motive.lean:1099` twin (off-cone): G4.
4. `RecursorContextExtension.restrictTrExprS` (Recursor/Bindings.lean:138): off-cone.
5. `RecursorMotiveTelescopeSeed.consumedTranslation` (Recursor/CanonicalMotiveReplay.lean:7, CONE): G4.
6. `SemanticBoundGeneratedRecursiveCall.restrictToFieldPrefix` (Recursor/RecursiveShapeRow.lean:68): off-cone.
7. `checkClosedType.rawSourceTranslationWF` (Header/Existential.lean:119, CONE): G3.
8. `FVarNarrowCore.restrict` (Equation/RecursiveCallScope.lean:93), `FVarNarrowScope.restrict` (Header/LoopType.lean:1117) and `NarrowRuntimeScope.restrict` (LoopType.lean:736), all CONE: G3. This is the "narrow scope" machinery that later feeds `restrictTrExpr`.

`weakFV_inv` users:
- G2-owned: `ConditionallyTyped.weakN_inv` (off-cone), `ConditionallyHasType.weakN_inv`, `ConditionallyWHNF.weakN_inv`, `isDefEqLambda.WF`, `isDefEqForall.WF` and `unfoldNatWellFounded.WF'` (all below).
- `TrExprS.uninstantiateAfterWeakFV_eq` (Lemmas.lean:2481, CONE). It drops cached-parameter fvars after entering a larger retained reader context. Its users are `RecursorLaterParameterScope.uninstantiateEq` (Constructor/Replay.lean:1705) and `LaterParameterScope.uninstantiateEq` (Header/LoopType.lean:3989), both G3. The production checker substitutes cached parameters, so the removed fvars are header parameters with no inhabitant. A round trip is plausible: the header was checked in the parameter context.
- Inductive-side, for G3/G4: `RecursorContextWF.initialClosedHeaderDefEq` (Context.lean:1470), `RecursorLaterParameterScope.domainTranslation` and `normalizedBody` (Constructor/Replay.lean:1506 and 1750), `TrExprS.dropFVarPrefix` (Recursor/Telescope.lean:2559), `initialLaterHeaderDefEqOfTranslation` (Header/LoopInd.lean:137), and `LaterParameterScope.domainTranslation` and `normalizedBody` (LoopType.lean:3779 and 4037).

## Verify/Typing/LevelEquiv.lean

- **`TrExprS.weakBV_inv` LevelEquiv.lean:172 (CONE)**: `BVLift Δ Δ'`, `TrExprS Δ' e e'`, e closed below dk ⟹ `∃ e₀, TrExprS Δ e e₀ ∧ e' = e₀.liftN n k`. It uses `VExpr.WF.weakN_iff.1` (app and proj cases), `IsType.weakN_iff.1` (lam, forallE), `HasType.weakN_iff.1` (letE) and `BVLift.wf`. This is **(c)**, false as stated for the same reason as `weakFV'_inv`.
- **`weakBV_inv₁` (231)**: a single binder. Its only user is `instantiateProjectionFields.WF_all` (TypeChecker/Projection.lean:248, CONE, via `inferProj.WF_all`, InferType.lean:433). That code handles the non-dependent branch of a projection field telescope: field type `forallE d body` where `body` does not mention the field.
  - **Repair (b), mostly.** The removed binder *is* inhabited: by `proj st position e'`. The dependent branch right above already uses `hbody.inst … hp hp_tr`, and `body.instantiate1 p = body` syntactically when `body` is closed. Typing `hp` needs `hp0 u hu (G u)`. That is available when `maybePropType = false` (`hG`) or when `d` is a Prop (`hG0`).
  - **Residual (c) corner:** a Prop structure with an earlier *non-dependent data* field. The executable (like C++ `infer_proj`) allows this, and the projection onto the data field is not typable, so there is no inhabitant. Either prove the needed later-field fact another way, or accept this corner as open.
  - **Size:** 50 to 100 lines in Projection.lean, after which `weakBV_inv`/`₁` can be deleted.

## Checker caches: Verify/Typing/ConditionallyTyped.lean and TypeChecker/Basic.lean

The invariants are `InferCache.WF` (`ConditionallyHasType`) and `WHNFCache.WF` (`ConditionallyWHNF`) (Basic.lean:584 ff). For every cached `e ↦ r`: "if `e`'s fvars lie in the current `Δ`, then e translates in `Δ` and the typing/defeq holds in `Δ`".

**What the lemmas do.** On exit from `withLocalDecl`/`withLetDecl` (`RecM.WF.withLocalDecl` Basic.lean:980, `M.WF.withLocalDecl` 1041, `RecM.WF.withLetDecl` 1104, all CONE), every entry is transported from `(fv,d)::Δ` to `Δ`:
- `ConditionallyHasType.weakN_inv` (58): `weakFV_inv` ×2 plus `HasType.weakN_iff.1`, a fixed-type strengthening of `e : A`.
- `ConditionallyWHNF.weakN_inv` (128): `weakFV_inv` ×2 plus `IsDefEqU.weakN_iff.1` on `e ≡ whnf e`.

The removed variable is the innermost binder (`skip_fvar` at the head, LiftN n 0), so `OnCtx` is not the issue; defeq/typing strengthening is. The binder's type has no inhabitant (it is the domain of the lambda/forall being checked).

**Classification: (c).** The lemmas, as statements about arbitrary entries satisfying the invariant, are false: an entry `SI ↦ SJ`-style could satisfy the larger-context invariant. The executable is very likely sound: the real algorithm can never derive `SI ≡ SJ`, because it never synthesises the constructor application that proof irrelevance needs. But the invariant does not record that.

`LevelsCache.WF.weakN_inv` (Basic.lean:968) is purely syntactic and clean.

**Same issue, harder: `quickIsDefEq.WF` IsDefEq.lean:149 (CONE, about 2810 dependents).** Its users are `isDefEqCore'.WF`, `lazyDeltaReductionStep.WF` and through them the whole checker.
- The `EquivManager` invariant lives in `VState.WF.ectx`: `∃ Δ' n, Δ'.WF ∧ c.vlctx.FVLift' Δ' 0 n 0 ∧ EquivManager.WF …`. Δ' is the ever-growing context of all fvars created so far, including popped scopes.
- A union-find hit gives `Δ' ⊢ e₁ ≡ e₂`, and `IsDefEqU.weak'_iff.1` pulls it down to the current context. That is defeq strengthening across arbitrary popped fvars: (c).
- A per-entry context-restricted invariant does **not** rescue the union-find. A link `a ≡ b` in Δ'|cl(a,b) and a link `b ≡ c` in Δ'|cl(b,c) compose to `a ≡ c` only in Δ'|cl(a,b,c). The middle term may mention removed fvars, which is exactly the countermodel shape `SI ≡ K v q ≡ SJ`.

**`isDefEqLambda.WF` / `isDefEqForall.WF`** (IsDefEq.lean, around 50 to 95 and 125 to 145) are an extra `weakFV_inv` use. In the non-dependent-body branch the executable compares bodies *without opening a binder*, instantiating the loose bvar with `default`. The proof must therefore translate the body in the outer context from its translation under `t₂'`. Classification: (c) proof-wise.

**Repair options for the whole checker-cache cluster** (Kim's decision):
- **E1, executable scoping (recommended, small).** Make `withLocalDecl`/`withLetDecl` save and restore the infer/whnf caches and the `EquivManager` (or drop entries added inside the scope). The exit proofs then use the *pre-scope* state's WF (already available as `wf`), so `ConditionallyHasType/WHNF.weakN_inv` disappear. `ectx` can then be the current context, so `quickIsDefEq.WF` needs no transport. For lambda/forall, always open a binder in the non-dependent branch too (as the dependent branch does). Then the body comparison happens in the extended context, which is where `lamDF`/`forallEDF` need it anyway.
  - Cost: the executable `addDecl` changes. It loses cross-binder cache reuse and departs from C++ kernel behaviour, so the performance effect needs measuring (the `Std` replay is already slower than upstream).
  - The `addDecl.WF` statement is unchanged.
  - Proof size: roughly 150 to 400 lines (Basic.lean withLocalDecl/withLetDecl ×3, `VState.WF.ectx` simplification and its users, quickIsDefEq, isDefEqLambda/Forall), plus executable changes of about 20 to 40 lines in Lean4Lean/TypeChecker.lean.
- **E2, algorithmic locality (large).** Prove that every checker result about inputs with fvar-closure S holds in Δ|S. This means restating `inferType.WF`, `whnf.WF`, `isDefEq.WF` and so on relative to the fvar-closure: a re-proof of most of Verify/TypeChecker, thousands of lines. Even then the `EquivManager` still needs scoping or a subformula-closed invariant, because of the transitivity problem above. Not recommended.
- **E3, hypothesis.** Thread a strengthening hypothesis on the environment into `VEnvs.WF`/`addDecl.WF`. It would have to hold for the *output* environment too, and the countermodel shows it fails for some Lean-valid inductive declarations. So it is an honest but unattractive restriction of the final theorem.

## Verify/Typing/ProjectionDesugaring.lean

`ProjectionDesugaring.weakN_inv` (228) uses `HasType.weakN_iff.1` and `IsDefEqU.weakN_iff.1`; `weak'_inv` (294) uses `OnCtx.weakN_inv`. Both are off-cone, and `weak'_inv` has 0 users outside the file. Classification: (c), false. **Delete both.**

## Primitive extension checks (Verify/Environment/Primitive)

### `Primitive.TrExprS.ofClosed` Condition.lean:540 (layer-1 line 527, CONE)

Its user is `Condition.check.gadget_pieces` (2241), then `Condition.check.WF`, then the primitive-definition checks inside `addDefinition.WF`.
- It uses `OnCtx.weakN_inv`, `VExpr.WF.weakN_iff`, `IsType.weakN_iff` and `HasType.weakN_iff`, all `.1` with `Ctx.LiftN.right`. It brings readings of *closed* pieces (`prop`, `asBool`, `proof` under `x y : Nat`; `r.toDec` under `x y : Nat, p : Prop, b : Bool, H : type p b`) down to `[]`. The removed context is the gadget's binders.
- Closedness does not save it (the environment can hold axioms), so the lemma is (c) as stated.
- **(b) for the three pieces under `x y : Nat`:** substitute a closed Nat inhabitant via instN. This needs `[] ⊢ Nat.zero : Nat` (or a literal); check that `hnat` / the primitive setup provides it.
- **(c) for `toDec`:** `p : Prop` has a closed inhabitant (`∀ p : Prop, p`) and `b : Bool` needs `Bool.true`, but `H : type p b` has no inhabitant in general.
- **Repair:** an executable change, checking `toDec` (and, more simply, all four pieces) at `[]` in the `Condition`/`Reflection` check. This contradicts the documented design ("no check has to exist merely to produce that reading") but is cheap and does not reject Lean-valid input. Size: a few executable lines plus 100 to 200 proof lines; `ofClosed` is then deleted.

### `Primitive.unfoldNatWellFounded.WF'` Recursion.lean:540 (CONE)

Its users are `unfoldNatWellFounded.WF` (1699), then `WF₂`, then the primitive checks.
- It uses `IsDefEqU.weakN_iff.1` (1123), `HasType.weakN_iff.1` (1157) and `TrExprS.weakFV_inv` (949, 1002, 1045). It pushes `F`, `natRec` and `F`'s inferred type from inside the `lambdaTelescope` (the definition's own binders, arbitrary types with no inhabitants) down to the outer context. The guards (`containsFVar`, `hasLooseBVars`) only establish syntactic independence. Classification: (c).
- **Repair (executable, cheap):** after the guard, re-run `inferType`/`check` on `F` and `natRec` in the outer context (`c.withMLC m₀`). That gives a genuine outer-context origin, and the defeqs then come from uniqueness in one context. Size: about 10 executable lines and 150 to 300 proof lines in Recursion.lean.

## Impact on final theorems

All G2 cone sites (checker caches, `quickIsDefEq`, lambda/forall comparison, `instantiateProjectionFields`, primitive checks, `FVLift'.wf`/`weakFV'_inv`) are below **every** branch of `addDecl.WF`, not just `inductDecl`.
- With options E1 plus the Primitive executable re-checks, no final hypothesis or conclusion changes. Only the executable `addDecl` changes (cache scoping, always opening a binder for lambda/forall, a few extra closed-piece checks).
- Without executable changes, `addDecl.WF` would need an environment-level strengthening hypothesis (E3) that is false for some Lean-valid environments.

## Size estimate for G2

- Delete dead or off-cone code: `HasType.skips`, `ProjectionDesugaring.weakN_inv/weak'_inv`, `ConditionallyTyped.weakN_inv`, `TrProj.weak'_inv`, `VLocalDecl.weak'_iff/weakN_iff` (replace with the true `.2` lemmas).
- `FVLift'.wf`/`BVLift.wf`: change to take `Δ.WF` (about 9 + 3 callers; supplying it is G3/G4 work).
- `weakFV'_inv`/`weakBV_inv`: delete and replace with an inhabitant-substitution form plus round trips at consumers (12 + 14 consumers, mostly inductive-side).
- Checker cluster via E1: about 300 lines plus the executable change.
- `instantiateProjectionFields`: about 100 lines plus the Prop-structure corner.
- Primitive: about 300 to 500 lines plus small executable checks.
# G3: header, context and replay sites (Lean4Lean/Verify/Inductive/{Basic,Context,Constructor/Replay,Header/*,Equation/RecursiveCallScope,Equation/Setup}.lean)

All paths below are relative to `Lean4Lean/Verify/Inductive/`. Every use is the `.1`/`.mp`
(strengthening) direction. No G3 site uses only the true weakening direction, so none is class (a).

## Shared diagnosis

Almost every G3 site follows one pattern. The executable (`Inductive/Add.lean`) runs a
`TypeChecker` call (`checkType`, `whnf`, `isDefEq`, `ensureType`/`ensureSort`) in the
*ambient* local context. Examples:
- later headers are `checkClosedType`d and `whnf`ed inside the first header's parameter
  binders (`loopInd`, Add.lean:136-160);
- later parameters are compared with `isDefEq dom (← getType param)` in the full lctx;
- the recursor phase normalizes in the full recursor context `R.mlctx`.

The proof then pulls the resulting typing, defeq or translation back to a narrow semantic
scope (`[]`, `H.older`, or the dependency-closed `scope` of
`NarrowRuntimeScope`/`FVarNarrowScope`/`FVarNarrowCore`) by inverse weakening. The removed
binders are free variables with no inhabitant in the narrow scope, so `IsDefEq.instN` does
not apply. Uniqueness only gives the fact in the large context.

The repair is a true *checker locality (frame) theorem*. Take a fresh-state `TypeChecker.M`
run whose input expressions have fvars in a set `S` that is dependency-closed in the lctx
(`IsFVarUpSet`). Such a run consults only declarations in `S`. So it returns the same
result when run in `lctx` restricted to `S` with the same `ngen`. The existing WF theorems
applied to the narrow `MLCtx` then give narrow-scope facts directly.

The infrastructure for `S` already exists: `NarrowRuntimeScope.upset`,
`FVarNarrowScope.upset`, `FVarNarrowCore.upset` (Header/LoopType.lean:689, 1015;
Equation/RecursiveCallScope.lean:26), and `LaterParameterScope`/`RecursorLaterParameterScope`
`older` suffixes.

`AlphaLocality.lean` gives only syntactic alpha-renaming facts, not this frame property.

This is the same theorem the G2 cache invariant (`ConditionallyWHNF.weakN_inv`) needs, so it
should be proved once.

Estimate: 3-8k lines (a simulation over `whnf`/`inferType`/`isDefEq`/`ensure*`), unless it
is admitted as a single named, *true* sorry.

Each run here is fresh (`TypeChecker.M.run c.env c.safety c.lctx …`, see Context.lean:1440),
so caches play no role in G3.

Hard requirement: no executable code may read the lctx globally (for example its size or
`getFVars`) on these paths. The only allowed accesses are lookups of encountered fvars. Fresh
names come from `ngen`.

## Site table

| site | statement shape / what is removed | source of large-ctx fact | class | repair, size |
|---|---|---|---|---|
| Basic.lean:1179 `VExpr.WF.mkApps_canonical_prefix` | WF of full canonical app `fn↑ #0..#n` in `actual.reverse++outer` ⇒ WF of each prefix app in the smaller prefix ctx (removes the remaining `actual` binders), via `VExpr.WF.weakN_iff.mp` | generic inversion | (c): statement false. Counterexample: `fn : (x:SJ) → P v → T`, `actual = [SI, P v]`. The full app is typed (the `q` binder present makes SI ≡ SJ), but `fn x` in `outer, x:SI` is not. | delete; only user is `canonicalApplicationContext` |
| Basic.lean:1284 `VEnv.HasType.canonicalApplicationContext` | WF canonical app ⇒ `IsDefEqCtx (actual++outer) (expected++outer)`, binder-by-binder `IsDefEqU.weakN_iff.mp` over the one binder `x : actual_j` | inversion of application typing | (c): false, same counterexample (conclusion would force `outer ⊢ SI ≡ SJ`). True weaker conclusion: per-binder defeq in the *full* ctx only, which is not a context conversion. | Users: `Nested/Replacement.lean:1810 ownerMotiveSuffixContext` (CONE), `Basic.lean:1441 _of_defeqCtx` (not cone), `_of_weakened`. The consumers compare generator-built telescopes (recursor indices/major vs motive domains; equation fields vs installed minor fields). These should be aligned *by construction* (both come from the same header and field telescopes), not by inversion: likely (b) by construction, 150-400 lines per consumer (G4 owns those files). |
| Basic.lean:1469 `canonicalApplicationContext_of_weakened` | `HasType.weakN_iff.mp`: `fn↑ : (wrapForalls expected body)↑` in `actual++outer` ⇒ in `outer` | lookup typing of a bound minor in the equation ctx | (c) as stated (fixed-type strengthening), and it feeds the false lemma above | Caller `CompletedEquationRhs.lean:985` already has the minor's declared type in the outer telescope (round trip): pass the outer typing directly, about 30 lines. Its other half falls with `canonicalApplicationContext`. |
| Context.lean:1470 `RecursorContextWF.initialClosedHeaderDefEq` | closed source header vs its `whnf` normal form: defeq in `R.mlctx` ⇒ defeq in `[]` (removes the whole recursor ctx). Also two `weakFV_inv` translation strengthenings. | executable `whnf` in the recursor ctx | (b) via checker locality on a closed input (`S = ∅`), about 60 lines given locality | user `Recursor/FirstPass.lean:580 startRecursorHeaderSemantics` (CONE) |
| Constructor/Replay.lean:1665 `RecursorLaterParameterScope.domainDefEq` | defeq of the parameter domain with the cached param type, `R.mlctx` ⇒ `H.older` (removes later recursor binders) | executable `isDefEq` in the full ctx | (b) locality | 0 users; delete or rewrite |
| Constructor/Replay.lean:1750 `RecursorLaterParameterScope.normalizedBody` | `whnf` result after cached-param substitution, defeq + `weakFV_inv` restricted to `fv :: older` | executable `whnf` | (b) locality, about 60 lines | → `FirstPass continueRecursorParameterSemantics` (CONE) |
| Header/Elimination.lean:191 `ContextWF.ConsumedDomain.proof_of_largeEliminationCheck` | `Γ, x:A ⊢ A↑ : Prop` ⇒ `Γ ⊢ A : Prop` (removes the field binder itself) | `ensureType dom` run under the field's own binder | (b), **no locality needed**: `A` is already a type in Γ (`Hdom.isType`, `source_defeq`). Uniqueness in `Γ,x:A` gives `sort u ≡ sort 0`, then `IsDefEqU.sort_inv` (existing base conjecture, a context-free level fact) gives `u ≈ 0`, then use `sortDF` in Γ. | about 15 lines; → `LargeEliminationTrace.singletonTelescope` (CONE) |
| Header/LoopInd.lean:137 `initialLaterHeaderDefEqOfTranslation` | later closed header vs its `whnf`: defeq in the first-header param ctx ⇒ `[]`, plus two `weakFV_inv` | executable `whnf` inside the first header's binders (Add.lean:141) | (b) locality (closed input), about 60 lines | → `RawMaterialization checkedLaterForall`, `initialLaterHeaderSynthesisStateOfTranslation` (CONE) |
| Header/LoopType.lean:736 `NarrowRuntimeScope.restrict`, :1117 `FVarNarrowScope.restrict`, Equation/RecursiveCallScope.lean:93 `FVarNarrowCore.restrict` | `TrExprS.weakFV'_inv`: runtime translation ⇒ narrow-scope translation | translation in the runtime lctx | (c) as stated: translation needs scope typing (cast-term counterexample). For executable *outputs* this is (b) via locality. For *source* subterms the narrow translation already comes from the narrow certificate (`hnarrow`). | Restate to take a narrow-run witness. About 20 lines each plus caller threading. |
| LoopType.lean:784 `NarrowRuntimeScope.restrictTrExpr` | `whnf` output: defeq in runtime ⇒ scope (`IsDefEqU.weak'_iff.1`) | executable `whnf` | (b) locality | users: `Constructor/Positivity.lean:3268 refinesNarrow`, `Constructor/Normalization.lean:35 uniformNormalFormNarrow` (CONE). This is the header/positivity `restrictTrExpr` named in HANDOFF. |
| LoopType.lean:814 `NarrowRuntimeScope.hasTypeOfFull`, :1162 `FVarNarrowScope.hasTypeOfFull`, RecursiveCallScope.lean:150 `FVarNarrowCore.hasTypeOfFull` | `narrow'↑ : sort u` in runtime ⇒ `narrow' : sort u` in scope | runtime typing | (c) as stated: it needs `T ≡ sort u` strengthening for the narrow type `T`. Becomes (b) with **no locality** if a premise `IsType scope narrow'` is added: weaken, `uniqU` in runtime, `sort_inv`, `sortDF`. | About 20 lines each. Callers must supply `IsType` in scope; usually available (header/field domains were checked as types by the narrow certificate). Users: `SingletonElimination:183`, `Recursor/Structure.lean:2704 tailRefinesNarrow` (CONE), `CompletedEquationMinorContext:1517` (CONE), `NarrowFieldRuntimeFrame.closedTargetTranslation`, `narrowSemanticExposedType`. |
| LoopType.lean:832 `NarrowRuntimeScope.hasTypeOfFullPair`, :1180 `FVarNarrowScope.hasTypeOfFullPair` | general fixed-type typing strengthening | n/a | (c), false | 0 users: delete |
| RecursiveCallScope.lean:130 `FVarNarrowCore.hasTypeOfFullPair` | general fixed-type typing strengthening | runtime typing of recursive-call arguments/major | (c) false as stated | 6 users in `CompletedEquationRecursiveCall.lean`/`Equation/RecursiveCall.lean` (`cachedCoreSemanticCallArgumentFrame` CONE, `narrowSemanticAppliedMajorTyping[For]`). Needs the narrow typing built constructively from the field telescope (generator-built terms), or locality if the typing came from an executable `inferType`. Defer to G4; probably 100-300 lines. |
| LoopType.lean:922 `NarrowRuntimeScope.resultSort` | runtime `X↑ ≡ sort ℓ` ⇒ scope `X ≡ sort ℓ` | executable `ensureSort`/`whnf` | (b) locality (strengthening "≡ sort" is not justified otherwise) | users: `LoopInd:948`, `SemanticFold:206, 286` (CONE) |
| LoopType.lean:3855 `LaterParameterScope.domainDefEq` | `isDefEq dom (getType param)`: full ctx ⇒ `H.older` | executable `isDefEq` (Add.lean:121) | (b) locality | users: `Recursor/Structure.lean:2236 parameterSynthesisWF`, `LoopType:4914 checkedScopeWF` (CONE) |
| LoopType.lean:4037 `LaterParameterScope.normalizedBody` | `whnf` after param substitution, full ⇒ `fv :: older` | executable `whnf` | (b) locality | users: `LoopType:4841 scopeWF` (CONE), `FirstPass continueCheckedSemantics` |
| LoopType.lean:5255 `laterIndexSynthesisWF` (use at :5410) | index-step `whnf`: runtime defeq ⇒ `indexType :: scope` via `weak'_iff.1` | executable `whnf` | (b) locality | users: `LoopInd:1272`, `SemanticFold:286` (CONE) |
| Header/RawMaterialization.lean:190 `CheckedSourceHeaderTranslation.checkedTerminal` | `IsType.weakN_iff.mp`: closed header target is a type in the runtime ctx ⇒ in `[]` | `ensureSort` at the end of `loopType` in the first-header ctx | (b) locality (closed input); alternatively derive from the narrow header certificate (`checkedSourceOfSort`, :165, works in `[]`), but that certificate itself relies on locality | users: `MaterializedFold:171`, `SemanticFold:11, 286` (CONE) |
| Header/Existential.lean:119 `checkClosedType.rawSourceTranslationWF` | `weakFV'_inv` of a closed type to `[]` | `checkType` in the ambient lctx (non-empty for later headers and constructors) | (b) locality (closed input, `S = ∅`), about 30 lines | users: `Existential:228`, `Constructor/ExistentialTargets:222` (CONE) |
| Equation/Setup.lean:3336 `VEnv.IsDefEqCtx.cancelLiftForallDomains` | context conversion of two telescopes in `expanded` ⇒ in `outer`. Uses `IsDefEqU.weak'_iff.1` on the closed forall telescope plus `OnCtx.weak'_inv`. | equation-field telescope conversion | (c): false as stated. `OnCtx.weak'_inv` is also unjustified, though the caller could pass `OnCtx outer`. | users: `CompletedEquationRecursiveCall:1866, 2145` (CONE) and Equation/ copies. Needs the narrow conversion produced directly (G4). |

## Effect on the final spec

None of these lemmas appears in the statement of `addDecl.WF` or of `Theory/Inductive/*`.
They are all internal steps that seed the empty-context header telescope (`VInductDecl`
header types, `TrInductDeclCore`), parameter agreement, and the recursor first pass.

With the locality theorem, every (b) site is repaired without touching any final statement.
Without it, there is no honest way to obtain the empty-context header certificate. The
alternative would be stating header well-formedness only in the checker's ambient context,
which is meaningless for the spec.

So the decision point is: prove (or admit as one *true*, named theorem) TypeChecker run
locality, instead of `weakN_iff`.

## Estimated plan for G3
1. TypeChecker frame/locality theorem (shared with G2): 3-8k lines, or one true sorry.
2. Use `sort_inv` instead of strengthening at Elimination:191 and in the three
   `hasTypeOfFull` variants (add an `IsType scope` premise): about 100 lines plus caller
   threading.
3. Rewrite the 11 locality sites (Context:1470, Replay:1665/1750, LoopInd:137,
   LoopType:784/922/3855/4037/5255, RawMaterialization:190, Existential:119) and the three
   `restrict`s to take narrow-run evidence: about 40-80 lines each, 600-900 total.
4. Delete the false lemmas `mkApps_canonical_prefix`, `canonicalApplicationContext`,
   `NarrowRuntimeScope/FVarNarrowScope.hasTypeOfFullPair` and `cancelLiftForallDomains`.
   Re-prove their CONE consumers (ownerMotiveSuffixContext, finalCanonicalMinorFieldContext…,
   FVarNarrowCore.hasTypeOfFullPair users, cancelLiftForallDomains users) by construction
   from the generator telescopes: roughly 1-2k lines, overlapping with G4.
## G4: recursor / equation / nested-replacement use sites (Lean4Lean/Verify/Inductive/)

Paths relative to `Lean4Lean/Verify/Inductive/`. "Cone" means in the `addDecl.WF` dependency cone
(from `/tmp/l4l-scratch/weakn-graph-all.tsv`). Every site below uses the `.1`/`.mp` (strengthening)
direction except the two marked (a).

Classes, applying the parent framing (defeq, typing-at-sort, existential WF, `TrExprS.weakFV'_inv`,
`weakBV_inv_lift` and `FVLift'.wf` strengthening are all false given the countermodel plus
`forallE_inv`):
- (a): only weakening is used. Repair: `IsDefEqU.weakN` (`Theory/Typing/Lemmas.lean:784`).
- (b-lookup): the small-context fact is a direct `HasType.bvar`/`Lookup` already available.
- (b-fwd): repair by building forward. Take a small-scope translation that already exists, weaken it,
  and use `TrExprS.uniqueS`/`uniq` in place of the inversion.
- (b-loc): the large-context fact comes from an executable run (whnf, inference, `checkRecursorTypes`)
  in an lctx with extra ambient fvars. It needs either an executable-locality theorem or a narrow
  re-run that the producer retains. The locality theorem would say that the checker's derivation for
  `e` uses only lctx entries in the up-set closure of `fvars e`, so it replays in the restricted
  context. This is shared infrastructure with G2 and G3 (`NarrowRuntimeScope`,
  `FVarNarrowSources`, `ConditionallyWHNF`).
- (c): false as stated, with no small-context evidence available.

No G4 site requires a change to `Theory/Inductive/*`: no module there depends on `weakN_iff`.
`canonicalCompletedRuleTranslation` and `canonicalConsumedGeneration` are now closed proofs, and
both depend on these sites. So a "closed" junction is currently closed modulo the false lemma.

### Sites in the cone

| site | stmt / use | removed binders; origin of large fact | class | repair |
|---|---|---|---|---|
| `Recursor/FirstPass.lean:2569` `mkRecInfos.loopArgs1.parameterStepOfCheckedRecursorHeader` (decl 2519) | `(IsDefEqU.weakN_iff ..).2 hnarrowMatch` | weakening of a narrow defeq into the runtime lctx | **(a)** | Replace with `hnarrowMatch.weakN henv Hscope.olderLift.toCtx`. 1 line. |
| `Recursor/FirstPass.lean:3590` `continueRecursorIndexSynthesisSemantics` (`_unary`) | `IsDefEqU.weak'_iff .1`: `narrowBody ≡ normalizedNarrow` in `indexType :: scope` from the runtime ctx | Ambient runtime fvars (`Hruntime'.lift`). The fact comes from executable `whnf` (`hnormalizeEq`) in the runtime lctx. | **(b-loc)**, else (c) | Needs a whnf-locality theorem, or restating index synthesis in the runtime context and narrowing only via locality. HANDOFF item 7 already notes that the header must retain its whnf telescope syntactically. |
| `Recursor/RecursiveCalls.lean:823` `loopInd1.resultSemantics` (`_unary`) | `IsType.weak'_iff .1`: `IsType (I params indices)` in the narrow scope | Ambient runtime fvars. The fact comes from the major's type in the runtime ctx. | **(b-fwd)**, conditional | Build `I params idx` typing directly in the narrow scope from the constant's type plus the narrow index-domain defeqs that the synthesis certificate carries. That certificate currently comes from the site above, so it is conditional on that repair. About 60-100 lines. |
| `Recursor/CanonicalMotiveReplay.lean:7` `RecursorMotiveTelescopeSeed.consumedTranslation` (→ `consumedMotiveAtParameters` → `consumedMotiveDomains` → `chooseOriginalIndexDomains_*` → `sourceIndexDomains` → `metadataRealization` → `canonicalCompletedRuleTranslation` → … → `addDecl.WF`) | `weakFV'_inv` (translation), `HasType.weak'_iff .1` (sort), `IsDefEqU.weak'_iff .1` (vs `S.canonical.motiveType`) | Ambient frames between `motiveSourceScope` and `motiveSourceExpanded`, i.e. earlier families' indices and majors. The fact comes from the first-pass motive translation in the expanded lctx. | **(b-loc)**, else (c) | The canonical motive type is defined in the narrow scope, but the executable source (`mkForall indices (mkForall major sort)`) was only translated in the expanded scope. The repair needs (i) locality, or (ii) the first pass to open each family's indices in a params-only lctx and retain that translation. With either, the remainder is uniq in the narrow scope (about 50 lines). |
| `CompletedEquationMotive.lean:1084` `CompletedRecursorPhasesResult.finalOwnerNarrowMotiveTranslationAt` (→ `finalOwnerCanonicalMotiveDomainAt` → … `ruleRhsTyped` → `canonicalCompletedRuleTranslation`) | Same three strengthenings as `consumedTranslation`, at the installed stage | Same | **(b-loc)** | Derive it from the repaired `consumedTranslation` (the seed `S` is the same object), not re-strengthen. About 30 lines after that repair. |
| `CompletedEquationRecursiveCall.lean:2511` (use 2688) `GeneratedRuleAlignment.finalSelectedMinorNarrowFieldAlignment` (→ `finalCheckedNarrowFieldAlignment` → … `canonicalEquationFrame` → `canonicalCompletedRuleTranslation`) | `IsDefEqU.weak'_iff .1`: `wrapForalls narrowDomains R ≡ wrapForalls B.fieldDomains R` in `parameterDecls` | Rule-wide ambient fvars (`Wbase`). The fact comes from translation uniqueness in `baseExpanded`. Both sides are well-typed in the small scope, which does not help. | **(b-fwd)**, conditional | `B.runtime.sources : FVarNarrowSources` (`Header/LoopType.lean:100`) carries a narrow-scope translation of each field domain. The other side, `narrowDomains`, is a narrow translation of `parameterTail`. Both translate the same source binders, so the repair is a domain-by-domain `TrExprS.uniq` in the narrow field contexts with no strengthening. Two inputs are themselves strengthening products: `parameterTranslationAtSuffix` (`Recursor/Origins.lean:4467`, via `TrExprS.dropFVarPrefix` → `weakFV_inv`) and `FVarNarrowSources`/`NarrowRuntimeScope` (G3 `restrict`). So this repair is sound only after those are produced by locality or a narrow re-run. About 150 lines locally. |
| `CompletedEquationRhs.lean:985` (use 1146) `GeneratedRuleAlignment.finalCanonicalMinorFieldContextOfApplication` (→ `finalCanonicalMinorApplicationPositiveArity` → … `canonicalCompletedRuleTranslation`) | `HasType.weakN_iff .mp Hminor`: the minor `bvar` typed at the installed telescope, drop `equationFieldDomains` (k = 0). It also calls `Basic.lean` `canonicalApplicationContext_of_weakened`, which does the same (G3). | Equation field binders. `Hminor` is the lookup typing of the minor variable, lifted. | **(b-lookup)** | In `outer`, `HasType.bvar` with `Lookup` of the minor declaration plus `hminorType` (the minor's declared type equals `wrapForalls (fields ++ hyps) residual`) gives the small fact directly. Then call `canonicalApplicationContext` on the base fact; that lemma is itself a G3 site. About 30-40 lines. |
| `Recursor/CanonicalRecursiveShape.lean:67` `TrExprS.weakBV_inv_lift` (generic inverse of `weakBV`; uses `VExpr.WF.weakN_iff` on `app`, `IsType.weakN_iff` on lam/forall domains, `HasType.weakN_iff` on let, and `BVLift.wf`) → `removeBeforeInner:258` → `unliftStep`/`unliftTelescope` → `recursorTelescope_hypothesisUnlift` → … `consumedGeneration` → `generationSignature` → `nativeTarget` → `RecursorPhasesResult.mk` → nested final result → `addDecl.WF` (and `canonicalConsumedGeneration`) | Arbitrary-source BV strengthening | Inserted motive group `M` and earlier minor/hypothesis group `G`. The fact comes from the retained `checkRecursorTypes` run in the full generator context. | **(c)** as a lemma, **(b-fwd)** at the caller | The lemma is false (same `app` counterexample, and the motives have no closed inhabitants, so `instN` does not help). Replace it with a true forward variant: given a small translation `t₀` of `source`, `weakBV` plus `uniqueS` yields `T = t₀.liftN ..`. That is about 40 lines. `recursorTelescope_hypothesisUnlift` must then obtain small-scope translations of the blueprint hypothesis sources. The per-field rows (`RecursorFieldPrefixScope`, `Recursor/SecondPass.lean:302`) are only an up-set predicate on the full executable context, not a restricted context, so a small translation still needs locality (b-loc). About 300-600 lines plus the shared locality work. |

`CompletedRecursorConstruction` itself (the structure) is weakN-dependent through
`ParameterContextSuffix.toRecursorContext → NarrowRuntimeScope.scopeWF → VLCtx.FVLift'.wf →
VLocalDecl.weak'_iff`, which is G2/G3 context strengthening. Every G4 cone theorem inherits that path
too.

### Sites outside the cone (no `addDecl.WF` dependent)

| site | class | note |
|---|---|---|
| `Recursor/FirstPass.lean:2479` `parameterStepOfCheckedHeader` (decl 2432) | **(a)** `.2` | 1 line. This is the non-recursor twin. |
| `Recursor/FirstPass.lean:3000` `continueIndexSynthesisSemantics._f` | (b-loc) | Twin of 3590. |
| `Equation/Motive.lean:1099` `RecursorPhasesResult.finalOwnerNarrowMotiveTranslationAt` | (b-loc) | Twin of `CompletedEquationMotive:1084`. |
| `Equation/RecursiveCall.lean:2538` `RecursorPhasesResult…finalSelectedMinorNarrowFieldAlignment` | (b-fwd), conditional | Twin of `CompletedEquationRecursiveCall:2511`. |
| `Nested/Replacement.lean:1740` `GeneratedRecursorTelescopeTranslation.ownerMotiveFirstDomainDefEq` | (c) as stated, (b-fwd) possible | Typing uniqueness of `bvar numIndices` in the larger context, then dropping indices and major (uninhabited). It could be replaced by `TrExprS.uniqueS` if the motive's first domain and the first index domain translate the same source. Its only users are `finalOwnerMotiveFirstDomainAlignment` in `CompletedEquationMotive.lean:282` and `Equation/Motive.lean:287`, both outside the cone. Delete rather than repair. |
| `Recursor/CanonicalConstructorModel.lean:8` `TrExprS.dropFVarPrefix_defeq`, `:30` `isType_dropFVarPrefix`; `Recursor/CanonicalConstructorReplay.lean:6` `dropFVarPrefix_typed` | (c) as lemmas, (b-loc) at origin | They drop `ambientDecls` from a translation, defeq or sort typing produced in the ambient lctx. Their only users are `constructorDefEqAtSuffix` and `constructorTranslationAtSuffix`, both outside the cone. Delete. Note the live sibling `TrExprS.dropFVarPrefix` (`Recursor/Telescope.lean:2563`, cone, via `TrExprS.weakFV_inv`). It feeds `RecInfoMinorSemanticSource.parameterTranslationAtSuffix` (`Recursor/Origins.lean:4467`, cone), the input of the 2511 site above. |
| `Recursor/ContextRestriction.lean:18,98` `MLCtx.restrictUpSet`/`restrictUpSetCtx`; `Recursor/Bindings.lean:138` `RecursorContextExtension.restrictTrExprS`; `Recursor/RecursiveShapeRow.lean:68` `SemanticBoundGeneratedRecursiveCall.restrictToFieldPrefix` | (c) | Generic translation restriction via `weakFV'_inv`. False as stated, with no cone users. The HANDOFF item 7 "shape-definition program" (restrict the per-hypothesis call row to `params ∪ fields.take f ∪ args`, read `Recursive` binders off the restricted `MLCtx`, `closeAllLams`, weaken, `uniqueS`) relies on exactly these. The program needs a new restriction principle (executable locality) and cannot use these lemmas. Delete them or re-hypothesise them on locality. |

Twin files: the `Equation/{Canonical,MinorAlignment,MinorContext,Motive,RecursiveApplication,
RecursiveCall,RecursiveCallFrame}.lean` (`RecursorPhasesResult.*`) weakN-dependent declarations all lie
outside the cone (counts 81/47/49/29/28/83/41, cone 0). `Equation/Setup.lean` and
`Equation/RecursiveCallScope.lean` do have cone users and must stay. The first group is dead with
respect to `addDecl.WF` and can be deleted instead of repaired, subject to a full-cone check of their
non-dependent declarations.

### Estimate (G4 only)
- (a): 2 one-line edits.
- (b-lookup) Rhs:985: about 40 lines, plus G3's `canonicalApplicationContext`.
- Deletions outside the cone: about 10 theorems in G4, plus the dead `Equation/*` twins.
- Conditional (b-fwd): 2511, `RecursiveCalls:823`, and the forward replacement of `weakBV_inv_lift`.
  About 300-500 lines once narrow-scope evidence exists.
- (b-loc) cluster: index synthesis 3590, motive `consumedTranslation`/1084, small hypothesis sources
  for `hypothesisUnlift`, `parameterTranslationAtSuffix`. These cannot be repaired locally. They need
  either the executable-locality theorem (shared with G2/G3; a large project, 1.5-3k lines, at the
  level of the `TypeChecker.*.WF` invariants) or changes to the executable/producer so that it opens
  family indices and checks field and hypothesis sources in a params-only (or field-prefix-only)
  lctx and retains that run. With either in place, each site is 50-150 lines.
- No change to `Theory/Inductive/*` or to the statement of `addDecl.WF` is forced by G4.
