# Astra review 4: the frame-lemma route for the projection corner (2026-10-08)

Question: /tmp/astra4_q.txt, reproduced below; answer follows.

```text
You are reviewing a design in this repository (lean4lean, a verified reimplementation of the Lean 4 kernel). Read docs/inductives/STRENGTHENING_PLAN_2026-10-08.md first, then CORNER_ASTRA_REVIEW.md (your earlier review), then the code it cites: Lean4Lean/TypeChecker.lean (the executable core checker, in particular inferForall, instantiateProjectionFields, inferProj, whnf', whnfCore', inferType', withFreshId/State.leaveScope, isDefEqLambda), Lean4Lean/Inductive/Add.lean (checkClosedType, checkConstructors.loopCtor, validateRestoredConstructorParameters.run, the Context.checkLCtx comment), Lean4Lean/Verify/TypeChecker/Projection.lean (instantiateProjectionFields.WF_all and the corner callback), Lean4Lean/Verify/Typing/ProjectionCorner.lean, Lean4Lean/Verify/TypeChecker/Basic.lean (VContext, VState.WF, Methods.WF, M.WF/RecM.WF), Lean4Lean/Verify/TypeChecker.lean (VEnvs.WF).

The design replaces the canonical-choice hypothesis of the projection-walk corner by (F) a frame lemma for the executable core checker (a successful run in a local context with extra "ghost" declarations that never occur in inputs or state is the same successful run in the context without them), (G) a ghost version of the verification of the inferForall loop, yielding a "telescope-closed translation" TelTr of each constructor type (the translation survives deleting any subset of non-dependent binders), (I) a new VEnvs.WF invariant field recording TelTr for every constructor constant, proved preserved by addDecl, and (C) the projection walk carrying TelTr instead of TrExprS, the corner being the delete branch.

Please answer concretely and critically:
1. Is the frame lemma (F) true for this executable? Look for every read of the local context (getLCtx, Context.lctx, find?, mkForall/mkLambda, isLetFVar, withLCtx, error construction), every place a ghost free variable could leak into an Expr or the caches, pointer-equality or hashing behaviour that could differ, and anything else that could make a run in the ghost-extended context succeed while the run in the smaller context fails or returns something different. Is the proposed statement (GhostRel, GF, GFState, Reserved) the right one, and is anything missing (e.g. eqvManager, failure cache, unfold cache, name generator)?
2. Is (G) sound: at a non-dependent binder of a constructor type checked by checkType in the empty context with a fresh state, do all later sub-runs satisfy the hypotheses of (F)? Does the existing verification really apply to the ghost-free run (VState.WF in the smaller VContext with the advanced name generator)?
3. Is the TelTr definition sufficient for the walk (C), including level instantiation (TrExprS.instL gives only TrExpr; there is TrExprS.instL_lequiv), weakening into the checker's context, substitution of parameters and typable projections, and whnf on the spine? Are constructor-type spines really syntactic forallE on every installation path (ordinary, nested restored, primitive/bootstrap)? If not, what breaks?
4. Is adding the TelTr field to VEnvs.WF an honest invariant (not a hidden conjecture), given that VEnvs.WF already carries checker-derived fields (inductiveProvenance, constructorSemantics)? What would a skeptical reviewer object to, and how should the final report describe the result (e.g. it does not prove the corner for arbitrary well-formed VEnvs)?
5. Is there a simpler or more robust variant (e.g. putting the frame argument at a different point, recording a weaker invariant, or avoiding the VEnvs.WF change)?
Be concrete, cite file and line numbers, and say plainly if any part is false.
```

## Answer

**This is a promising provenance-based route, but the plan is not correct as stated.** I found a concrete counterexample to (F)’s stated hypotheses, a context-relation problem under fresh binders, and an unrestricted substitution obligation for `TelTr` that would recover much more strengthening than the plan intends. The ghost replay argument itself looks sound after repairing those points.

1. **(F): false as stated; a suitably restricted frame lemma looks viable.**

   **The missing environment hypothesis is a real counterexample.** `GhostRel` equates the environments but does not require their expression payloads to avoid ghosts. The executable can obtain expressions from:

   - Constant types: [TypeChecker.lean:135](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/TypeChecker.lean:135).
   - Definition values, including the uncached zero-universe-parameter path: [TypeChecker.lean:479](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/TypeChecker.lean:479).
   - Constructor types during projection inference: [TypeChecker.lean:288](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/TypeChecker.lean:288).
   - Recursor-rule right-hand sides: [Reduce.lean:73](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/Inductive/Reduce.lean:73).

   I ran a small executable counterexample with identical environments containing `D := g`, where the larger local context contains the ghost let declaration `g : Sort 1 := Sort 0`, and the smaller context is empty. Both start with empty caches; `g` is reserved because its name is outside the generator’s prefix. All the proposed hypotheses hold. The results were:

   | Call | Larger context | Empty context |
   |---|---|---|
   | `whnf D` | `Sort 0` | free variable `g` |
   | `ensureSort D` | success | error |

   This deliberately malformed environment is allowed by the proposed *pure executable* statement. Add a syntactic `GFEnv`, covering stored types, unfoldable values, and recursor RHSs. Global free-variable closure is a convenient stronger assumption and should follow from the checking-environment invariants at intended applications.

   **The proposed exact `find?` equality is not stable under opening a binder.** `mkLocalDecl` assigns `LocalDecl.index := lctx.decls.size`. Opening the same fresh ID in contexts of different sizes therefore creates unequal declarations, despite equal names, types and binder information. The actual constructors are at [Lean LocalContext.lean:286](/home/kim/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/src/lean/Lean/LocalContext.lean:286).

   Compare declarations modulo `setIndex 0`, rather than by full equality. The repository already has exactly the relevant abstraction lemma, `mkBindingListN_congr_setIndex`, at [Verify/LocalContext.lean:295](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/Verify/LocalContext.lean:295). This also accommodates the smaller context reconstructed from an `MLCtx`.

   The local-context audit otherwise supports the intended argument:

   | Read | What must agree |
   |---|---|
   | `inferFVar`, line 130 | Type of the input non-ghost fvar |
   | `whnfFVar`, line 383; `isLetFVar`, line 415 | Declaration kind and let value |
   | `inferLambda`/`inferLet`, lines 174/238 | Declarations selected by their explicit binder arrays |
   | `etaExpand`, line 1032 | Same, for `mkLambda` |
   | `withLocalDecl`/`withLetDecl` | Fresh IDs and declaration payloads, modulo indices |
   | Error construction, lines 114, 122, 232, 282, 350 | No equality needed for a success-only theorem |

   `mkForall`/`mkLambda` do not enumerate arbitrary ambient declarations: they look up the explicitly supplied variables. `withLCtx` is defined at line 105 but is not used elsewhere in this core file. A generic theorem about that combinator would need hypotheses relating its replacement contexts and continuation; “every function” cannot literally have one uniform first-order contract.

   **State details:**

   - Requiring ghost-free **values** of the inference, whnf and unfold caches is sufficient for preventing cache hits from returning ghosts. Keys need not be ghost-free for the same-state frame theorem: both executions perform the same lookups in the same maps.
   - Omitting ghost-freeness of `failure` is fine for that theorem.
   - Omitting ghost-freeness of `eqvManager` is also fine for operational replay. It mutates union-find state, rather than merely “answering booleans”, but never returns its stored expressions to the checker. Identical inputs and identical manager state give identical operations; see [EquivManager.lean:29](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/EquivManager.lean:29).
   - **Add name-generator monotonicity, or at least preservation of `Reserved`, to the conclusion and recursive-method contract.** The stated contract for arbitrary `m` permits a method to reset `ngen`. Its caller then cannot justify that the next generated ID is non-ghost.
   - `unfold` must remain covered: unlike the other caches, it survives `leaveScope`. The implementation explicitly retains it at [TypeChecker.lean:66](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/TypeChecker.lean:66).

   `isDefEqLambda` always opens a binder, even for unused bodies, at [TypeChecker.lean:602](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/TypeChecker.lean:602). That does not defeat framing: both executions must open that binder with the same fresh ID. Do not optimize it away in the replay.

   **Pointer equality deserves an explicit scope qualification.** In Lean’s logical model, equality of the arguments gives equality of calls to the opaque pointer predicates by congruence; hashing likewise introduces no new context dependence. But the unsafe implementations inspect addresses, and [PtrEq.lean:6](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/PtrEq.lean:6) explicitly acknowledges acceptance-sensitive sharing behavior. An extensional Lean proof establishes the frame theorem **in the repository’s pointer-equality model**. It does not independently establish a heap-level simulation between executions with different sharing. I found no additional concrete ghost-deletion counterexample here, but would not describe such a theorem as proving identical native execution traces.

2. **(G): the replay argument is sound in outline, but `GFState` alone does not justify verification in the smaller context.**

   At a syntactically unused binder, its freshly generated fvar cannot occur in the later opened domains or result. This is the relevant property of the *whole remaining body*, not just the immediately following domain. The executable checks domains before introducing their binders and processes the spine directly; see [TypeChecker.lean:177](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/TypeChecker.lean:177).

   The correct induction maintains **a state already well formed in the smaller context**:

   - Replay each domain/result call there using repaired (F).
   - Apply checker verification there, obtaining the next smaller-context `VState.WF`.
   - When ghosting a binder, advance the generator without extending that context.
   - When retaining a binder, extend both contexts and use ordinary verified binder introduction.

   Advancing only the generator preserves the relevant state facts. Inference and whnf cache predicates are monotone in the generator; the equivalence manager and universe facts remain in the same context; the generator prefix is unchanged. The ingredients appear in [ConditionallyTyped.lean:30](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/Verify/Typing/ConditionallyTyped.lean:30) and the existing scope proof at [Basic.lean:1241](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/Verify/TypeChecker/Basic.lean:1241).

   This distinction matters because `VState.WF` includes semantic validity of cached equivalences and typing judgments, plus level and hit invariants—not just support conditions. See [Basic.lean:685](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/Verify/TypeChecker/Basic.lean:685). A ghost-free equivalence established in a larger context is not thereby valid in the smaller context. The proof must never make that inference.

   The proposed use of freshly reserved IDs is otherwise appropriate: before opening the ghost, inference/whnf cache keys and values are reserved by the previous generator, so they cannot contain its next ID. Environment closure handles `unfold`. Subsequent ghost-free replay preserves absence of existing ghosts.

   Two implementation details remain:

   - The actual loop’s `fvars` array **contains ghosts**. Apply (F) to the instantiated domain/result calls, not indiscriminately to the whole loop with that array as a ghost-free input.
   - Rebuilding translations must identify the smaller derivation, weakened back, with the stored larger translation. Syntactic uniqueness is available—including projections—at [CanonicalMinorFields.lean:17](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/Verify/Inductive/Recursor/CanonicalMinorFields.lean:17).

   Existing verification requires the initial `VState.WF` explicitly, through [Basic.lean:726](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/Verify/TypeChecker/Basic.lean:726). With the induction above, applying it is legitimate. Without that induction, the plan’s state argument is incomplete.

3. **`TelTr` supplies the delete step, but its unrestricted transport story is too strong.**

   At an already exposed syntactic forall, the proposed delete clause supplies precisely the missing certificate. For the executable’s `!body.hasLooseBVars` branch, take the deleted source body to be `body` itself, since lifting it changes nothing. The abstract lift equality then makes substitution by even an untypable projection a syntactic no-op. This replaces the choice callback currently used at [Projection.lean:296](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/Verify/TypeChecker/Projection.lean:296).

   **The major problem is unrestricted `TelTr.instN`.** Consider a telescope residual consisting only of a type variable `X`. Its `TelTr` certificate has vacuous keep/delete obligations. Substitute an arbitrary translated, typable type `A` for `X`. An unrestricted substitution theorem would now produce `TelTr A A'`, including certificates for every unused binder exposed inside `A`.

   Thus that theorem would upgrade arbitrary translated types to telescope-closed translations. It is **not a routine consequence of ordinary typed substitution**; it reintroduces the unrestricted strengthening problem that provenance was meant to avoid. I am not claiming a counterexample to its mathematical truth. I am saying the proposed proof architecture does not justify it.

   Use a **bounded telescope certificate**, indexed by the number of source binders still relevant to the walk:

   - At depth zero, require only `TrExprS`.
   - At positive depth, require a syntactic forall and keep/delete certificates at smaller depth.
   - Substitution transports only those existing binders; it does not certify newly exposed spines after the budget reaches zero.

   A constructor certificate needs the parameter-and-field prefix. This fits the walk’s actual consumption exactly.

   **Universe transport also needs a real lemma.** As the question notes, [Lemmas.lean:1685](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/Verify/Typing/Lemmas.lean:1685) gives only `TrExpr`. [LevelEquiv.lean:132](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/Verify/Typing/LevelEquiv.lean:132) supplies a syntactic translation with an `LEquiv` relationship. The telescope analogue must recursively transport certificates into contexts with the *actual translated domains*, using appropriate context equivalence. Ordinary `TrExprS.instL_lequiv` does not automatically provide that recursion.

   Weakening is conventional once contexts are well formed. Parameter and typable-projection substitutions additionally need the existing domain-alignment conversions; those are already performed in [Projection.lean:87](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/Verify/TypeChecker/Projection.lean:87). The nondependent delete branch removes the need to establish projection typability only for that branch.

   **Whnf preservation is already available.** `Methods.WF.whnf_forall_eq` exists at [Basic.lean:808](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/Verify/TypeChecker/Basic.lean:808), and the fuel implementation discharges it at [Verify/TypeChecker.lean:113](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/Verify/TypeChecker.lean:113). No new method field is needed.

   **Installation-path assessment:**

   - **Ordinary:** yes, the accepted constructor prefix is syntactic. `loopCtor` matches `forallE` without whnf and ultimately requires a constant-headed inductive application: [Add.lean:344](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/Inductive/Add.lean:344), [Add.lean:287](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/Inductive/Add.lean:287).
   - **Nested restored:** restoration preserves existing forall nodes: it opens/recloses parameters and replaces constant-headed nodes, rather than reducing telescope heads. See [Add.lean:943](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/Inductive/Add.lean:943). I found no supported successful path admitting a metadata/let wrapper around a consumed field binder.
   - **Primitive/bootstrap:** primitive checking does not bypass ordinary installation. The finite accepted `Bool`/`Nat` constructor shapes are explicit at [Primitive.lean:596](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/Primitive.lean:596). Their certificates can be proved directly. This is useful because partial primitive batches need not satisfy `HasPrimitives`; see [PrimitiveBootstrap.lean:22](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/Verify/Inductive/PrimitiveBootstrap.lean:22).
   - **Quotients:** `Quot.mk` is `quotInfo`, not a constructor consumed by this projection path.

   Nevertheless, **record or expose the source-prefix fact in the checker-facing invariant**. Plain `TelTr` permits a metadata-wrapped forall with vacuous keep/delete clauses. Whnf then exposes a binder for which it supplies no certificate. Existing production provenance already records concrete arity through `ProductionConstructorAlignment.numFields` at [Environment/Basic.lean:740](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/Verify/Environment/Basic.lean:740); the narrower `VContext` projection registry does not currently expose that field.

   There is also a concrete correction to the plan’s provenance claim: **nested validation checks the original constructor type, whereas installation stores `restoreNested loweredCtor.type`.** Compare [Add.lean:1422](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/Inductive/Add.lean:1422) with [Add.lean:1284](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/Inductive/Add.lean:1284). Existing semantics records translations of both source types to the same abstract constructor, not literal source equality: [ConstructorInstallation.lean:163](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/Verify/Inductive/Nested/ConstructorInstallation.lean:163). You need a deletion-compatible restoration transport theorem, or validation of the exact stored type. Merely citing the original check is insufficient.

4. **(I) can be an honest invariant, but preservation—not its placement in `WF`—makes it honest.**

   The existing fields at [Verify/TypeChecker.lean:14](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/Verify/TypeChecker.lean:14) establish a reasonable precedent. However, a skeptical reviewer should require:

   - Base/bootstrap proofs.
   - Preservation through every declaration and safety observer.
   - Certificates for newly visible constructors before subsequent checker calls use them.
   - The nested source-to-stored-type bridge above.
   - A dependency argument showing that deriving a new certificate uses only previously available certificates.

   Ordinary constructor checking occurs in the header environment before new constructors are installed, which supports a noncircular proof: [Add.lean:892](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/Inductive/Add.lean:892). Nested original-type validation similarly uses the header-only environment at [Add.lean:2116](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/Inductive/Add.lean:2116).

   Existing `inductiveProvenance` is **abstract installation provenance**, not a retained successful executable checking trace: its payload is visible at [Environment/Basic.lean:896](/home/kim/worktrees/lean4lean/lean4lean-strength/Lean4Lean/Verify/Environment/Basic.lean:896). It does not already discharge the new locality obligation.

   An accurate final claim would be:

   > Canonical choice is unnecessary for declaration-checker preservation over environments satisfying the strengthened constructor-telescope invariant. The invariant is established at bootstrap and preserved by checked installation. The result does not establish the projection corner for arbitrary declaratively well-formed environments, or for every environment satisfying the previous `VEnvs.WF`.

   The plan’s qualification is substantially right. Until preservation is proved, however, adding the field merely relocates an assumption.

5. **My preferred variant is a bounded constructor-prefix certificate plus exact-state replay.**

   Keep the executable frame proof independent of typing, but repair its contract with environment support, declaration equality modulo indices, and generator monotonicity. Prove it for the checker entry points and helpers with their actual shape/continuation preconditions.

   Then prove ghost telescope verification by maintaining smaller-context `VState.WF` throughout, and export a bounded certificate tied to constructor metadata. This avoids unrestricted `TelTr.instN`, makes the whnf argument explicit, and fits the existing source-arity provenance.

   I would also strengthen only the projection-relevant constructor invariant unless other consumers need the general version. Put the certificate alongside source/abstract constructor alignment so its relationship to the stored type cannot be lost during restoration.

   Avoid rerunning each suffix with empty caches as a shortcut: removing cache hits can change success under the fixed fuel limits. Replay from the exact carried state is the stronger argument.

   Avoiding a literal change to `VEnvs.WF` is possible by introducing a separate checker-reachability/certificate predicate and proving preservation of that conjunction. That changes packaging, not theorem scope. I do not see a justified route from the **existing** `VEnvs.WF` alone to the required certificate that bypasses the original strengthening problem.
