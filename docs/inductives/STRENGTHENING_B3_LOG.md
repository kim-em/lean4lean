# Direction B3 log: eta postponement for the replay obligation

Branch `agent/verify-inductives-strengthening3-B3` (worktree `lean4lean-strength3-B3`), off
`agent/verify-inductives-strengthening3` at 81ee106e. Task: prove `EtaReplay` (`Exposure.lean`),
under the hypotheses of `etaReplay_empty_chain` (`TypedFront`, `CaseRedexDescends`,
`UnfoldingCheckDescends`), or give the checked failing case and a weakened variant that still gives
`PiExposureRedN`. Material: `Lean4Lean/Theory/Typing/Strengthening/EtaPostponement.lean`, zero
`sorry`; axiom audit `scratch/EtaPostponementAxioms.lean` (only `propext`, `Classical.choice`,
`Quot.sound`).

## Step 1: `EtaReplay` is false (checked, `not_etaReplay`)

The obligation asks for an eta chain `e'↑ ⇝η* Y` at the end. `EtaPar.funEta` annotates the new
binder with any type `A'` such that `e : Π A' B` above, and the typing is up to conversion, so `A'`
may mention the inserted variable. A beta step inside the expansion collapses it but keeps the
annotation:

* below: `Γ = []`, `e = λ (x : Prop). x : Prop → Prop` (`StrengtheningObstructions.idProp`);
* above: `Γ' = [Prop]`, annotation `A' = (λ (X : Prop). Prop) q` (`badDomain`, convertible to
  `Prop` by beta, `badDomain_defeq`), so `e↑ : Π (y : A'). Prop` (`idProp_hasType_bad`);
* eta step `e↑ ⇝η λ (y : A'). e↑ y` (`etaPar_counterexample`), then the parallel beta inside the
  body `⇝ λ (y : A'). y` (`parRed_counterexample`), an `UpStep`.

No lift reaches `λ (f q). q` by an eta chain: a chain into that shape (a lambda whose annotation
is an application to the first variable and whose body is the first variable) stays in that shape,
by inversion of `EtaPar` using only the typing `Prop → Prop` (`EtaPar.bvar_inv_r`,
`EtaPar.badShape_inv_r`, `EtaChain.badShape_inv_r`: the `structEta` case is excluded by
`type_not_structure`, the `funEta` case by the body shape), and no lift at `k = 0` has the first
variable as the argument of its annotation (`liftN_ne_badShape`). The instance uses no constant, so
`not_etaReplay : ¬ EtaReplay` holds in every parameter environment (`[Params]`).

Consequence for the design: the eta chain cannot be the whole invariant; binder annotations of
collapsed expansions must be compared up to conversion. Note that the counterexample is harmless
for the *goal*: `FullReduction` below includes eta, and the source itself is normally equal to the
reduct.

## Step 2: the weakened obligation `EtaReplay₀` and its consequences (checked)

```lean
def EtaReplay₀ : Prop :=
  ∀ ⦃k Γ Γ' e T X Y⦄, Ctx.LiftN 1 k Γ Γ' → OnCtx Γ _ → OnCtx Γ' _ → HasType Γ e T →
    EtaChain Γ' (e.liftN 1 k) X → UpStep Γ' X Y →
    ∃ e' Z, FullReduction Γ e e' ∧ EtaChain Γ' (e'.liftN 1 k) Z ∧ NormalEq₀ Γ' Z Y
```

The reduct is related to the lift by an eta chain followed by a normal equality *without eta*
(`NormalEq₀ = NormalEqF false`: structural congruence up to universe levels, proof irrelevance and
convertible binder annotations). Why this relation and not `NormalEq` (with eta): `NormalEq` has
function eta (`etaL/etaR/etaBoth`) but no structure eta, so an invariant "`NormalEq e'↑ X`" is not
preserved by a junk structure-eta step above (it would need structure eta below, whose structure
typing is not forced). The eta chain carries junk expansions of both kinds; `NormalEq₀` absorbs
the annotations.

* The counterexample is an instance: `Z = e↑`, `NormalEq₀ (λ (x : Prop). x) (λ (y : A'). y)` by
  `lamDF` (`counterexample_etaReplay₀`).
* Eta steps above are trivial (`etaReplay₀_eta`); the empty chain is the descent of `Replay.lean`
  (`etaReplay₀_of_descent`, `etaReplay₀_empty_chain`, same hypotheses as before).
* Path replay (`path_replay₀`): induction on the above `UpStep` path with the invariant
  `∃ Z, EtaChain e'↑ Z ∧ NormalEq₀ Z X`; each step is first mirrored through the normal equality
  by the library's `ParRed/DeltaPar/EtaPar.normalEq₀_mirror` (`UpStep.normalEq₀_mirror`), which
  keeps the kind of the step, then pushed through the chain by `EtaReplay₀`, and the normal
  equalities compose.
* End lemma: `NormalEq₀ Z (Π A B)` with `Z` a type forces `Z = Π` (`normalEq₀_forallE_inv`, from
  `normalEqN_forallE_inv_r`), then `EtaChain.forallE_inv` as before.
* `piExposureRed_of_etaReplay₀ : (∀ U, EtaReplay₀) → PiExposureRedN`;
  `cancel_of_typedFront_of₀`; `cancel_iff_typedFront_of₀ : Cancel env ↔ TypedFront env` given
  `∀ U, EtaReplay₀`, `ProjFrontN`, `ElimFrontN`.

So the exact remaining obligation is `EtaReplay₀`, and `Exposure.lean`'s `EtaReplay` is retired
as false.

## Step 3: the eta-normal relation `EtaNE` and the obligation `EtaReplayNE` (checked)

Why a single relation instead of "chain then normal equality": the proof of the replay
obligation must be an induction on the *structure* of the relation between the lift and the
reduct, with the eta-free step pushed into sub-derivations (a chain is not decomposable along
subterms: expansions inside earlier expansions are later chain steps). `EtaNE Γ s X`
(`Strengthening/EtaNormal.lean`) is the inductive relation generated by:

* the `NormalEq₀` congruences: `refl`, universe-equivalent `sort`/`const`/`elim`, `app`, `proj`,
  `lam`/`forallE` with convertible annotations (body in the source's binder context),
  `proofIrrel`;
* `funEta` (source not a lambda, body related to the source applied to the new variable),
  `structEta` (arguments related to the parameters and the projections of the source);
* `betaR`: the right side may carry `(λ A. b) a` applied to further arguments when the source is
  related to the contractum, the administrative redex left when a lambda-valued subterm (or a
  partial application) is junk-expanded and a later application consumes the expansion;
* `betaL`, `projIotaL`: the left side may carry a beta or projection redex whose contractum is
  related to the right side (real redexes of the term below in the replay).

Checked: soundness (`EtaNE.defeq`, `hasType`), weakening along any `Lift'` (`weak'`, `weakN`),
context conversion (`defeqDFC`), inversion of two related lambdas (`lam_inv`), the body lemma
for lambda sources (`lam_body`: `EtaNE (λ D. t) X → EtaNE t (X↑ 0)`, the `betaR` case extends
the argument spine), root expansions of the right side (`root_funEta`, `root_structEta`), the
decomposition of a parallel eta step into a congruence step and root expansions
(`EtaParC`, `RootStep`, `EtaPar.root_decomp`), spine decomposition with eta wrappers of partial
applications (`Wrap`, `EtaPar.spine_inv`) and their absorption (`wrap_r`, `rootChain_spine_r`),
and the closure theorem `EtaNE.etaPar_r : EtaNE Γ s X → EtaPar Γ X X' → EtaNE Γ s X'`
(induction on the `EtaNE` derivation; the `betaR` case transports the step to the contractum by
the two-sided `EtaPar.instN`). Hence `EtaNE.of_etaChain` (every eta chain of a typed term), and
the end lemma `EtaNE.forallE_inv_lift`: a lift related to a `Π` reduces *below* to a `Π` (the
`betaL`/`projIotaL` cases are redexes of the term below; the projection field is retyped below by
`TypedFrontN.retype`).

Obligation (`EtaPostponement.lean`):

```lean
def EtaReplayNE : Prop :=
  ∀ ⦃k Γ Γ' e T X Y⦄, Ctx.LiftN 1 k Γ Γ' → OnCtx Γ _ → OnCtx Γ' _ → HasType Γ e T →
    EtaNE Γ' (e.liftN 1 k) X → UpStep Γ' X Y →
    ∃ e', FullReduction Γ e e' ∧ EtaNE Γ' (e'.liftN 1 k) Y
```

Checked: eta steps are trivial (`etaReplayNE_eta`, by `etaPar_r`), the lift itself is the
descent (`etaReplayNE_of_descent`, `etaReplayNE_empty_chain`), `path_replayNE`,
`piExposureRed_of_etaReplayNE : TypedFront → (∀ U, EtaReplayNE) → PiExposureRedN`,
`cancel_iff_typedFront_ofNE : Cancel ↔ TypedFront` given `∀ U, EtaReplayNE`, `ProjFrontN`,
`ElimFrontN`. So the content of `EtaReplayNE` is exactly the eta-free step cases (`ParRed`,
`DeltaPar`) pushed through the `EtaNE` constructors; the next step is that induction.
