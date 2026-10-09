# Spike: `VEnv.WF.patsStrong` without circularity

Branch `agent/iota-port-patsstrong-spike`, on top of #43 (`e11876df`). Lean files:
`Lean4Lean/Theory/Typing/PatsStrong/{ConstExt,Telescope,Spec,Rule,History}.lean` (1,185 lines,
all building); `SPIKE/premise-variant.diff` (the reduct-typing premise tried on #43's build).

Summary of the findings, in one paragraph. The history induction (route (a)) can be set up with
no circularity, and the spike proves it: a per-stage invariant `Stage env` that deliberately
excludes `PatsStrongOn env`, from which `PatsStrongOn env` is *derived* through the per-rule
argument, whose substitution step (iii) and conversion step (iv) are proved here with `Ordered env`
alone. What the route then needs from wave 1C is head inversion **on strong derivations with strong
conclusions** (`StrongHeadInversion`, `Spec.lean`), and that is not what the branch's observation
model produces: its collapse lemma returns weak `IsDefEq`s, and the `patsStrong` argument cannot
use a weak `cp ≡ p` because the constructor's field types depend on the parameters and the fields
must be retyped inside the strong derivation. Nobody has strong-conclusion head inversion; it is
new research, not a port. The alternative, a reduct-typing premise on `IsDefEq.pat`, was tried on
#43's full build (Theory, Verify, Experimental): it removes `patsStrong` entirely, changes
+90/-129 lines in 12 files, and leaves exactly one new obligation, `VEnv.WF.iotaReductTyped`, which
is the *weak* inversion argument that the branch's model already supports. I recommend the premise.

## 1. Dependency graph and the cycle

Names are #43's unless marked (B) for `agent/verify-inductives`.

```
VEnv.WF.orderedStrong  (EnvLemmas)
  ├─ WF.ordered
  ├─ WF.strong hp                       hp : PatsStrong env, used at each addConst/addDefEq stage
  │    ├─ OnTypes.addConst … hpats       (Strong) ← EnvStrong.of_hasType ← IsDefEq.strong' … hpats
  │    ├─ addQuot_strong hpats, addInduct_strong hpats, foldlM_addConst_strong hpats
  │    └─ IsDefEq.strong' (Strong)       pat case: `.pat hp hm he (hpats hp hΓ hm he hr hall) hr hall`
  └─ WF.patsStrong                       ← sorry  (EnvLemmas:334)

Everything in the strong system is under WF.orderedStrong:
  IsDefEq.strong, CtxStrong.strong, HasType.app_inv/lam_inv/const_inv (Strong),
  IsDefEqStrong.substEq'/subst, IsDefEq.substDF/subst, HasType.subst, IsType.subst (Strong),
  Verify/Primitive.lean, Verify/Environment/Primitive/*, Verify/Typing/TrTerm.lean.

What a proof of patsStrong needs (PORT_PLAN §4.3):
  (i)   spine inversion of the strong redex typing      ← HasTypeStrong inversion (syntax-directed)
                                                            + Π-injectivity (Injectivity.lean: sorry)
  (ii)  alignment: major typed at I us p idx (rec) and at I cus cp ι (ctor)
                                                         ← uniqueness (UniqueTyping: sorry on #43;
                                                            (B) IsDefEq.uniq via chainHeadInjectivity)
                                                         ← type-former injectivity
                                                            ((B) HeadInversion.former_args)
  (iii) instantiate the rule's generic typing by the actual arguments
                                                         ← #43: IsDefEqStrong.substEq' (OrderedStrong!)
                                                         ← spike: IsDefEqStrong.instOuter_telescope (Ordered)
  (iv)  convert to the redex's type                      ← uniqueness again + IsDefEqStrong.defeqDF

(B)'s head inversion:
  VEnv.WF.headInversion ← headSeparationModel, chainHeadInjectivity (HeadInjectivity/Model/EnvValid)
    ← chainHeadInjectivity_of_sound (Model/Extract) ← Model.SoundEnv (Model/Sound, induction on
      IsDefEqStrong) and  chain_sub : TypeChain link h ↦ (h.strong henv hΓ)   ← IsDefEq.strong
  ElCls.collapse / TyCls.mem_iff_chain return IsDefEq (weak); SpineArgsEq is weak.
```

The cycle, exactly: `(ii)` needs head inversion in `env₀`; (B) obtains it by `IsDefEq.strong` at
`env₀` (`chain_sub`, and `IsDefEq.uniq`'s `h1.strong henv.ordered hΓ`, which on (B) needs only
`Ordered` because (B) has no `pat` rule); on #43 `IsDefEq.strong` needs `OrderedStrong env₀`, whose
`pats` field is `PatsStrongOn env₀`, which is what `patsStrong` is proving for `env₀`.

A second, independent gap: #43's `substEq'` takes `OrderedStrong` only because `Ctx.SubstEq`
types the substituted terms weakly and strengthens them (`(W.lookup h).strong henv hΓ₀.defeq`).
Single-variable `IsDefEqStrong.instN` needs `Ordered` only. Step (iii) is therefore done here by
instantiating the telescope one outermost variable at a time (`Telescope.lean`), never through
`substEq'`.

### The two cuts

**(a) History induction over strict prefixes.** Carry along `WF'` an invariant that does *not*
contain `PatsStrongOn env`; derive `PatsStrongOn env` from the invariant plus head inversion at
`env`; prove head inversion at `env` from the invariant alone. The generic typing of each rule
lives at the stage-2 environment `envR` of its block, a constant-only extension of a *strict*
prefix, where `PatsStrongOn envR` is available from the induction; strengthen it there
(`IsDefEq.strong'`), carry it forward by `IsDefEqStrong.mono`. This is what the spike implements
(`History.lean`): the induction closes, with head inversion as a hypothesis (`Wave1C`).

**(b) Auxiliary endpoint-typed pattern calculus (Astra §4).** Give an auxiliary pattern rule both
endpoint typings, prove substitution and model soundness for it without raw-to-strong, prove
raw-to-aux by induction with step (ii)–(iii) in the `pat` case. Inspection: `IsDefEqStrong` *is*
that calculus (its `pat` carries the reduct typing), the branch's `Model.Sound` already runs on
it, and the raw-to-aux conversion's `pat` case is exactly `PatStrong`. So (b) changes nothing
about the hard part: the alignment `cp ≡ p` must be produced *in the auxiliary (strong) system*
to retype the fields, which is head inversion with strong conclusions. (b) adds a calculus and
its lemma suite (1–2k lines) for no reduction in risk.

**Recommendation between (a) and (b): (a).** Both need the same new metatheory; (a) is shorter
and is now prototyped. The real decision is (a) versus the premise (section 3).

### Why weak conclusions do not suffice (the fact that drives everything)

`PatStrong env p r` asks: from a *strong* `Γ ⊢ rec us (p ++ M ++ m ++ idx ++ [c cus (cp ++ f)]) : A`,
produce a *strong* `Γ ⊢ rhs us p M m f : A`. The template `rhs` binds its fields at types
`Fields(p)` (the recursor's parameters); the fields `f` come typed at `Fields(cp)` (from the
constructor spine). Retyping `f : Fields(cp)` to `f : Fields(p)` is `IsDefEqStrong.defeqDF`
along `Fields(cp) ≡ Fields(p)`, a strong equality obtained from a strong `cp ≡ p` by
`instDF`. A weak `cp ≡ p` (what `HeadInversion.former_args`/`ElCls.collapse` give) cannot be
strengthened here: strengthening a weak derivation is `IsDefEq.strong'`, whose `pat` case is
`PatStrong` of whatever redexes occur inside that derivation, which are unrelated to the one at
hand. No measure decreases. The same holds for `idx ≡ ι(cp, f)` and the levels. Hence
`StrongHeadInversion` (strong `forallE_forallE`, `former_args`, and `sort_sort`) is the
irreducible input of route (a), and uniqueness in the strong system (`uniqS`) with it.

The branch's model produces weak conclusions by construction: observation classes
(`TyCls`, `ElCls`) are sets of terms up to weak `IsDefEq`, valuations are `Ctx.SubstEq` (weak),
and `collapse` returns an `IsDefEq`. Making the classes strong is a redesign of `Classes`
(389), `Obs` (637), `Sound` (813), `EnvValid` (849), `Extract` (332) and the substitution
closure of classes (strong valuations need a strong substitution theorem, i.e. a strong
`Ctx.SubstEq` and a re-proved `substEq'`). Whether the soundness induction survives with strong
classes is unknown; the `pat` case is fine (the strong rule carries the reduct typing), the
risk is in class closure under substitution and in the collapse.

## 2. The Lean prototype

Five files under `Lean4Lean/Theory/Typing/PatsStrong/`. Build: `lake build
Lean4Lean.Theory.Typing.PatsStrong.History`. Axiom audit (`#print axioms`): `ConstExt.of_ordered`,
`IsDefEqStrong.instOuter_telescope`, `IotaRuleData.reduct_typed` are sorry-free; everything
above `IotaRuleData.patStrong` depends on `sorryAx` only through the two named stubs
`IotaRuleData.align` and `HasTypeStrong.uniqS`.

### `ConstExt.lean` (163 lines, no stubs)

* `VEnv.ConstExt env env₀`: `env₀` extends `env` by well-typed `addConst` steps.
* `ConstExt.of_ordered`: `env₁ ≤ env₀ → env₀.defeqs = env₁.defeqs → env₀.pats = env₁.pats →
  Ordered env₀ → ConstExt env₁ env₀`. So #43's four hypotheses on `env₀` are exactly a
  constant-only extension (proof: induction on `Ordered env₀`, joining each stage with `env₁`).
* `ConstExt.foldlM`: a `foldlM addConst` of constants typed in the start environment is a
  `ConstExt` (the shape of every stage in `WF.strong`, `addQuot_strong`, `addInduct_strong`).
* A defect in #43's statement: `VEnv.WFPrefix env env₁` does not make `env₁` well-formed.
  `WFPrefix.rfl` holds for any `env₁`, and a `decl` step may be a re-ordering of the history:
  with history `axiom x : Nat; def a := 1; axiom v : P a`, the environment `{Nat, P, v : P a}`
  (no `x`, no `a`, no `δa`) is a `WFPrefix` of the result (one `def a` step), but it is not
  `Ordered` (`v`'s type mentions a missing constant). The history argument needs `env₁.WF`.
  `PatsStrongWF` states the tightened form; `History.lean` proves #43's statement with `env₁.WF`
  in place of `env.WFPrefix env₁` (`WF.patsStrong'`). The bound `env₀ ≤ env` is unused. `WF.strong`
  only ever applies `hp` at a genuine prefix with a `foldlM` stage, so both changes are free.

### `Telescope.lean` (190 lines, no stubs)

* `VExpr.instOuter`, `instTail`, `instDoms`, `Ctx.InstN.append`, `CtxStrong.instTail`.
* `IsDefEqStrong.instOuter_telescope (henv : Ordered env)`: a strong judgement in
  `doms.reverse ++ Γ`, with arguments `args[j]` strongly typed at `doms[j].instOuter (args.take j)`,
  instantiates to a strong judgement in `Γ`. One `IsDefEqStrong.instN` per argument. This is step
  (iii)'s substitution theorem with `Ordered` in place of `OrderedStrong`.

### `Spec.lean` (245 lines, definitions only)

* `TypeChainS`, `SpineArgsEqS` (strong chains/spines), `Rigid env c` (no δ rule's left head and no
  pattern's head is `c`), `SimplePattern.head`.
* **`StrongHeadInversion env`**, the wave-1C target:
  * `sort_sort : CtxStrong → TypeChainS Γ (sort u) (sort v) → u ≈ v`
  * `forallE_forallE : CtxStrong → TypeChainS Γ (∀A.B) (∀A'.B') → (∃ u, Γ ⊢ A ≡ A' : sort u) ∧ ∃ v, A::Γ ⊢ B ≡ B' : sort v`
    (strong equalities)
  * `former_args : CtxStrong → Rigid env c → constants c = some ci → TypeChainS Γ (c ls args) (c ls' args') →
    Forall₂ (≈) ls ls' ∧ SpineArgsEqS Γ (ci.type.instL ls) args args'` (strong, typed pairwise).
* `IotaRuleData` (an ι rule as `addRecRule` registers it, with its own `cnp` so `ofRule` is
  definitional), `pattern`, `rhsR`, `genericRedex`, `genericReduct`.
* `IotaRuleData.GenericStrong env D`: the generic instance of the rule strongly typed in its
  telescope context `doms` (parameters, motives, minors, fields), both redex and reduct at a
  common `B`; `GenericWeak` the same in the weak system (what the installer supplies);
  `SyntaxAt`/`ShapeAt` the syntactic shape of the rule's constants plus rigidity of the former.
* **`Stage env`**: `Ordered env`, `OnTypes env (EnvStrong env)`, every registered rule is an
  `IotaRuleData` with `GenericStrong env` and `ShapeAt`, and every constant-headed definitional
  axiom is headed by a constant of `env`. **No `PatsStrongOn env`.**
* `Wave1C : ∀ env, Stage env → StrongHeadInversion env` and
  `RulesGenericTyped` (the installer's obligation at the stage-2 environment: `GenericWeak` and
  `SyntaxAt` for each rule of a well-formed block). These are the two explicit hypotheses of the
  main theorems, so the no-circularity condition is visible in their types: head inversion is
  demanded from `Stage` data, which excludes subject reduction at that environment.

### `Rule.lean` (266 lines; stubs `align`, `uniqS`)

* `Pattern.matches_varN_const_inv` (inverse of #43's `matches_varN_const`),
  `IotaRuleData.rhsR_apply` (the registered reduct applied to a match is
  `(rhs.instL us).mkApps (pre.take k ++ cargs.drop cnp)`, via `iotaRHS'_apply`),
  `genericReduct_instOuter`, `CtxStrong.instL`, `CtxStrong.append_closed`,
  `IsDefEqStrong.weak_below`.
* **Stub `HasTypeStrong.uniqS`**: two strong typings of one term have strongly equal types.
  Derivable from `StrongHeadInversion` as on the branch (`HasTypeStrong.uniq_chain_of_chainHeadInjectivity`,
  `TypeChain.collapse_of_chainHeadInjectivity`), by induction on `HasTypeStrong`.
* **Stub `IotaRuleData.align`** (steps (i)–(ii)): from `Ordered`, `EnvStrong`,
  `StrongHeadInversion`, `Shape`, the generic data and a strong redex typing, produce `Aligned`:
  `us.length = U`, level well-formedness, every actual argument strongly typed at the generic
  telescope instantiated (`args_typed`), and `A ≡ (B.instL us).instOuter args` strongly (`type_eq`).
  Its docstring gives the intended proof.
* **Proved, step (iii)+(iv)**: `IotaRuleData.reduct_typed (henv : Ordered env)`: from `Aligned` and
  the generic strong reduct typing, `Γ ⊢ (rhs.instL us).mkApps args : A` strongly: level
  instantiation (`IsDefEqStrong.instL`), `weak_below`, `instOuter_telescope`, `defeqDF`.
* **Proved**: `IotaRuleData.patStrong`: `PatStrong env D.pattern D.rhsR` from `GenericStrong`,
  `Shape`, `StrongHeadInversion`, `EnvStrong`, `Ordered` (match decomposition, `align`, `reduct_typed`).
* **Proved**: `Stage.patsStrongOn : Stage env → StrongHeadInversion env → PatsStrongOn env`.

### `History.lean` (321 lines, no new stubs)

* `Rigid.of_same/addDefEq/addPat`, `SyntaxAt.mono`, `ShapeAt.mono`, `former_eq`,
  `SimplePattern.head_eq_of_iota`, `quotDefEq_lhs_not_const` (the quotient rule's left side is a
  λ-abstraction, so it is headed by no constant).
* `GenericWeak.strong`: the one use of `IsDefEq.strong'`, at an environment with `PatsStrongOn`.
* `Stage.addConst`, `Stage.constExt` (through constants: `OnTypes.addConst` with `PatsStrongOn` of
  the previous environment, derived from its `Stage` and `Wave1C`).
* `Stage.addDefEq'` (a definitional axiom headed by a constant fresh in the base stage),
  `Stage.addDefEqs` (mutual blocks), `Stage.addQuot` (four constants and the quotient rule),
  `Stage.addInduct` (three constant stages to `envR`; each new rule's `GenericWeak envR` is
  strengthened with `PatsStrongOn envR`, which `Stage envR` and `Wave1C` give, and moved to the
  result; rigidity of old and new type formers by freshness of the new recursors in `envC`).
* **`WF'.stage (h1C : Wave1C) (hgen : RulesGenericTyped) : WF' ds env → Stage env`**.
* `patsStrongWF`, `WF.patsStrong'` (#43's statement with `env₁.WF`), `WF.orderedStrong'`.

The per-stage invariant is `Stage`; the induction is on `WF'`; the only place `IsDefEq.strong'`
is invoked at an environment is after that environment's `PatsStrongOn` has been derived from
`Stage` and `Wave1C`, never assumed.

### What wave 1C must target, precisely

`Wave1C`: for every `env` with `Stage env` (so: `Ordered`, `EnvStrong`, rules with
`GenericStrong` and `ShapeAt`, constant-headed axioms headed by existing constants; such `env` are
exactly the well-formed environments and their constant-only extensions), `StrongHeadInversion env`
with the three clauses above, **conclusions in `IsDefEqStrong`**, and `uniqS`. Not allowed:
`PatsStrongOn env`, `IsDefEq.strong` at `env`. Allowed: `IsDefEqStrong.weakN/instN/instL/mono`
(all `Ordered`), the telescope lemma, `forallE_inv'`/`isType'` (`Ordered` + `EnvStrong`).

Not done in the spike: `GenericWeak → PatTyped` (showing the installer form implies #43's
`rules_wf`), unnecessary since the port replaces `rules_wf`.

## 3. The alternative: a reduct-typing premise on `IsDefEq.pat`

Tried on #43's full build; the result is `SPIKE/premise-variant.diff` (580 lines of diff, +90/-129
in 12 files). `lake build Lean4Lean.Theory Lean4Lean.Verify Lean4Lean.Experimental` succeeds.

The change to `Basic.lean`:
```
  | pat … : env.pats p r → p.Matches e m1 m2 → Γ ⊢ e : A →
    Γ ⊢ r.1.apply m1 m2 : A →            -- new
    r.2.Realizes m1 m2 chk → (∀ t ∈ chk, …) → Γ ⊢ e ≡ r.1.apply m1 m2 : A
```

What changes in #43:
* `Lemmas.lean`: nine `pat` cases gain a binder and pass the reduct's induction hypothesis
  (mirrors the existing `IsDefEqStrong` cases; `liftN_apply`/`instL_apply`/`instN_apply` rewrites).
* `Strong.lean`: `IsDefEq.strong'`'s `pat` case is `.pat hp hm (ihe hΓ) (ihred hΓ) hr hall`; the
  `hpats` hypothesis disappears from `strong'`, `CtxStrong.strong'`, `EnvStrong.of_hasType`,
  `OnTypes.addConst`; `OrderedStrong` loses its `pats` field (`Ordered` + `EnvStrong`, master's
  shape, name kept so `Verify/Primitive`, `Verify/Environment/Primitive/*`, `TrTerm.lean` are
  untouched). `PatStrong`/`PatsStrongOn` become unused.
* `EnvLemmas.lean`: `PatsStrong`, `WF.patsStrong` (the sorry) and every `hp`/`hpats` argument of
  `foldlM_addConst_strong`, `addQuot_strong`, `addInduct_strong`, `WF.strong` are deleted;
  `WF.orderedStrong := ⟨H.ordered, H.strong⟩`. Net −114 lines in that file.
* `ChurchRosser.lean`: the `church_rosser` `pat` case binds the extra hypothesis and passes it;
  `Params.pat_env` unchanged; nothing else in the Church–Rosser development is touched (the
  `NormalEq` side never constructs `IsDefEq.pat`).
* `InductiveParams.lean`: `toParams.pat_wf` constructs `IsDefEq.pat` and must now supply the
  reduct typing: it calls the new `VEnv.WF.iotaReductTyped`. This is the one real consequence for
  confluence: `Params.pat_wf`'s contract (`Pat → Matches → HasType e A → OK → IsDefEqU e reduct`)
  has no context hypothesis, while the real `iotaReductTyped` needs `OnCtx Γ (env.IsType U)`
  (inversion in an ill-formed context is not available). Fix: add `OnCtx Γ (IsType env univs)` to
  `Params.pat_wf`; its only use (`ChurchRosser.lean:571`, inside the `NormalEq → IsDefEq` theorem)
  has `hΓ` in scope. Not done in the diff; the stub is stated without it.
* `Verify/Environment/Lemmas.lean`: `TrEnv.iota_defeq` takes `hred : venv.HasType U Γ (r.1.apply m1 m2) A`;
  `TrEnv.iota_rec` takes `venv.WF` and discharges it with `iotaReductTyped`.
* `Verify/TypeChecker/WHNF.lean`: `inductiveReduceRecCore.WF` passes `c.Ewf`; its `hredty` is
  still read off the defeq as before. No other checker change.
* `Experimental/`: `Stratified.lean` and `StratifiedUntyped.lean` define their own `IsDefEq1.pat`
  without a reduct premise and convert to `IsDefEq`; they get the same premise (mechanical, the
  strong-to-stratified direction already had `ihred`); `ParallelReduction.lean` two binder
  changes; `ShapeLogRel.lean` has its own `pat` and is untouched.

Sorry inventory after the change (Theory + Verify): identical to #43's, minus
`EnvLemmas.lean:334 patsStrong`, plus `Env.lean:78 VEnv.WF.iotaReductTyped`.

What the checker (and `toParams`) then has to supply: **one theorem**, in the weak system,
```
VEnv.WF.iotaReductTyped : env.WF → OnCtx Γ (env.IsType U) → env.pats p r → p.Matches e m1 m2 →
  env.HasType U Γ e A → env.HasType U Γ (r.1.apply m1 m2) A
```
Its proof is the same argument as section 1's (i)–(iv) in the weak system: spine inversion
(`HasType.app_inv`, now unconditional), uniqueness and type-former injectivity with weak
conclusions ((B) `IsDefEq.uniq`, `HeadInversion.former_args`, exactly what the model produces),
substitution `IsDefEq.substDF`/`instN` into the rule's generic typing (`rules_wf`, or the
installer's telescope form), `defeqDF`. On the branch this is the content of
`VIotaRuleShape.iota` in `Theory/Typing/RecursorLemmas.lean` (there via the stored equation's
`extra`; here via substitution into `PatTyped`). PORT_PLAN §4.4's "~150 lines moved" is an
underestimate: it is the weak inversion lemma, 1–2k lines, but it is a port, with the model as
planned (no strength upgrade), and `IsDefEq.strong` is unconditional again, so the model's
`chain_sub`/`Extract` entry points work as on master.

Logical relationship between the two rules: on well-formed environments and well-formed contexts
they derive the same judgements if and only if `iotaReductTyped` holds, which route (a) must prove
anyway (in strong form). The premise does not weaken the calculus; it relocates the regularity
obligation from the strong system's `IsDefEq.strong'` to the users of the `pat` rule.

## 4. Size estimates and the decision

Route (a), history induction (keep #43's rule):
* Done in the spike: 1,185 lines, two stubs.
* `uniqS` from `StrongHeadInversion`: 300–500 lines (port of the branch's `Uniqueness.lean` idea).
* `align`: strong spine inversion of recursor and constructor spines (600–900), alignment and
  field retyping through `former_args` and `instDF` (500–800), congruence for `type_eq` (300).
  Wave 1D total 2–3k lines, routine once `StrongHeadInversion` exists.
* `RulesGenericTyped` (installer, wave 1B): the branch's `EquationWF.lean` re-expressed, 1–2k;
  needed by both routes in some form.
* `Wave1C`, strong-conclusion head inversion: unknown. The model's conclusions are weak by
  construction; a strong-class redesign touches 3–4k lines of the 16k model and a strong
  substitution theorem, and may fail at class closure or collapse. This is research, with no
  existing proof anywhere to port. Risk: high; it is the critical path of the whole port.

Route (b), auxiliary calculus: route (a) plus 1–2k lines of calculus and lemma suite, same
research item. Not recommended.

Premise route:
* Calculus and plumbing: done (+90/-129, 12 files, in the diff), plus ~10 lines for
  `Params.pat_wf`'s context hypothesis.
* `iotaReductTyped`: 1–2k lines, weak system, after wave 1C's planned port (weak conclusions).
* Nothing else. `patsStrong` and the `OrderedStrong.pats` conditionality disappear; all of
  master's substitution theorems and the primitives layer are unconditional again.
* Risk: low (every ingredient exists on the branch in the required strength).

Facts for Kim, Mario and Alessandro to decide on:

1. **Strength of head inversion.** Route (a) needs head inversion with *strong* conclusions
   (`StrongHeadInversion`); the branch's model, master's `Injectivity.lean` and the thesis all
   state and (where proved) prove weak conclusions. No one has the strong form; obtaining it is
   a redesign of the observation model, not a port. If nobody wants to take that on, the premise
   is the only route with a known proof.
2. **Fidelity to the thesis's `pat` rule versus where regularity is proved.** #43 follows the
   thesis ("regularity taken as a rule"). The premise makes `IsDefEq.pat` carry the reduct's
   typing, like `extra` carries both sides through `df.WF` in `Ordered`; the two calculi agree
   on well-formed environments exactly when `iotaReductTyped` holds. The premise moves that
   theorem from the strong-system conversion (where it is hard) to the rule's users
   (`toParams.pat_wf`, `TrEnv.iota_rec`), where it is a weak-system lemma. This is a
   presentation choice for Mario; the diff shows its full cost on #43.
3. **The `PatsStrong` statement.** Independently of the route, #43's `PatsStrong` quantifies
   over `WFPrefix` prefixes that need not be well-formed (section 2, `ConstExt.lean`); if the
   theorem is kept, it should read `env₁.WF` (the `WFPrefix`/`≤ env` bounds are unused in
   `WF.strong`). Its remaining four hypotheses are exactly `ConstExt env₁ env₀`
   (`ConstExt.of_ordered`).
