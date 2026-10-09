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

## Step 4 (in progress): the proof of `EtaReplayNE`

Design. The induction is on the `EtaNE` derivation `H : EtaNE Γ₁ S X` with the eta-free step
`UpStep Γ₁ X Y` as hypothesis, for sources `S` of the generalized form "a below term renamed into
`Γ₁` along a lift `l` (`Ctx.Lift' l Γ₀ Γ₁'`, `Γ₁'` convertible to `Γ₁`), then applied to eta
variables and projected" (an elimination spine); the conclusion is a reduction below and the
relation for the same spine over the reduct. Sub-derivations inside `funEta` apply the source to
the new variable, inside `structEta` project it, inside `app`/`proj` decompose the spine, and the
`betaL`/`projIotaL` cases dissolve the administrative redex (a below redex, reduced below; or a
lambda applied to an eta variable, which is a renaming of the body into an extended below context).

Changes to `EtaNE` for this: `funEta` for every source (the inner source may carry the
administrative redex), `betaL`/`projIotaL` on spines (`mkApps (redex) args`), untyped atoms and
untyped `lamC`/`forallEC` congruences (so that `EtaNE` is reflexive and a `CongrRel`, needed for
the rhs congruence of stored rules). New lemmas: `EtaNE.rfl`, `EtaNE.congrRel`, `EtaNE.inst_r`,
`EtaNE.instN` (two-sided substitution, the collapse of a junk expansion in function position).

`EtaReplay.lean`: descent of eta-free parallel steps along any lift (`ParRed.descend'`,
`DeltaPar.descend'`), peeling one insertion at a time (`Ctx.Lift'.peel` keeps the intermediate
context well-formed).

Hard cases identified (to be isolated as named obligations if not proved): (B) singleton or
quotient prefix unfolding on a spine applied to eta variables (mirrored below by eta expansions at
the recursor telescope and the unfolding below); (K) iota above whose major is a proof term
convertible by proof irrelevance to the source's major (mirrored below by singleton prefix
unfolding); (H) iota above whose major is the junk structure eta expansion of a neutral source
(mirrored below by structure eta at the major, `major_type`, then iota).

## Step 5: redesign, eta-free steps recorded on the source side (checked)

The lifted-source plan of step 4 has a fatal duplication problem: a structure eta expansion
above duplicates the source into one copy per field, and a parallel step may reduce the copies
differently; no single reduction below mirrors all copies (checked thought experiment: the iota
fired in one copy only has no mirror, since neither `EtaNE` nor its transposition can relate a
redex to its reduct). The fix is to record eta-free steps *above*, on the source side of the
relation, and to descend them only at the root of the lift at the very end:

* `EtaNE` (redefined, `EtaNormal.lean`): untyped congruences (`bvar`, `sort`, `const`, `elim`,
  `app`, `proj`, `lamC`, `forallEC`), `funEta` (any source of function type), `structEta`,
  `betaR` (administrative redex on the reduct side, for junk expansions of partial applications),
  and `redL : UpStepF Γ s c → EtaNE Γ c X → EtaNE Γ s X` (an eta-free parallel step on the
  source side). The typed annotation conversions, proof irrelevance and the left administrative
  redexes of the previous version are gone (`redL` subsumes the latter); the counterexample's
  annotation change is `funEta` followed by `redL` with the beta inside.
* Checked: `defeq`, `hasType`, `weakN`, `defeqDFC`, `rfl`, `congrRel`, `inst_r`, `instN`
  (two-sided), `of_etaPar`, `root_funEta`, `root_structEta`, `Wrap`, `spine_inv`, `wrap_r`,
  `root_decomp`, `rootChain_spine_r`, `etaPar_r` (closure under eta steps on the right),
  `of_etaChain`, and the end lemma `forallE_inv_lift`: a lift related to a `Π` reduces below to
  a `Π`, descending each `redL` step at the root by `ParRed.descend`/`DeltaPar.descend`
  (hypotheses `TypedFrontN`, `CaseRedexDescends`, `UnfoldingCheckDescends`, `CheckVars`); the
  root eta expansions are excluded by typing.
* `EtaPostponement.lean`: `UpStepFClosure` (closure of `EtaNE` under eta-free steps on the right,
  a statement purely above), `etaReplayNE_of_closure : UpStepFClosure → EtaReplayNE` (with no
  reduction below at all), `piExposureRed_of_etaReplayNE`, `cancel_iff_typedFront_ofNE`,
  `cancel_iff_typedFront_of_closure : Cancel ↔ TypedFront` given `∀ U, UpStepFClosure`,
  `CaseRedexDescends`, `UnfoldingCheckDescends`, `ProjFrontN`, `ElimFrontN`.

So the whole replay problem is now the single above-only statement `UpStepFClosure`: push one
eta-free parallel step through the `EtaNE` constructors. Its cases: congruences by induction;
`funEta`/`structEta` bodies by induction (the duplication is harmless since nothing moves below);
`betaR` by transporting the step to the contractum (`ParRed.instN`, `DeltaPar.instN`); `redL` by
passing through; the redex cases on the reduct: beta of a related lambda (two-sided `instN`;
the collapse of a junk expansion), iota and prefix unfolding on a spine whose source has the same
spine shape (fire the same redex on the source by `redL`, with the guards transported along
conversion), and iota whose major is a junk structure eta expansion of a neutral source (fire
structure eta then iota on the source: an eta step on the source side, so either a composite left
step is added to `redL` with its descent at the root isolated as an obligation, or it is the one
remaining obligation of the closure).

`EtaReplay.lean` keeps the general-lift descent and `Lift.insVar` (not used by this route).

## Step 6: the closure `UpStepFClosure` is proved (checked, `EtaClosure.lean`)

`Lean4Lean/Theory/Typing/Strengthening/EtaClosure.lean` (zero sorry; axioms `propext`,
`Classical.choice`, `Quot.sound` only):

* `EtaNE.parRed_r : EtaNE Γ s X → Γ ⊢ s : T → ParRed Γ X Y → EtaNE Γ s Y` and
  `EtaNE.deltaPar_r` (the same for `DeltaPar`), both by induction on the `EtaNE` derivation with
  the step generalized; `upStepFClosure : UpStepFClosure`.
* The spine of the source is exposed by `EtaNE.const_spine_inv` (a constant-headed reduct comes
  from a source that is, after recorded `LStep`s, the same spine argument-wise related, or a
  neutral of structure type whose junk expansion is the constructor spine) and
  `EtaNE.elim_spine_inv`.
* Redexes on the reduct are fired on the source as recorded steps: beta via `EtaNE.app_lam_inst`
  (the related lambda's body instantiated; a `funEta` source is handled by `instN`), stored rules
  via `Pattern.Matches.constVarN_transport` and `Check.OK.defeq_values`, case steps via
  `EtaNE.schema_fire` (`CaseRedex.transport` to the source spines, `capture_replace` for the
  captured positions), projections of constructor spines via `DeltaPar.projIota` at the source
  (the field is typed by uniqueness of the projection's type), and prefix unfoldings via
  `EtaNE.unfold_r`: the source spine unfolds at convertible arguments
  (`PrefixUnfold.congr_defeq`); the two right-hand sides differ by the related bodies and a change
  of the binder domains (`PrefixUnfold.congr_rel` with `EtaNE.argRel`), absorbed by `lamD`
  (`EtaNE.wrapLams_defeq`); `PrefixUnfold.unique` identifies the reduct. The quotient case is the
  same with `QuotPrefixUnfold`.
* When the reduct's major is the junk expansion of a neutral source (iota or case step), the
  source fires the composite step `MajorEtaIota` (`redL (.inr (.root _))`); when the major of a
  projection is such an expansion, the projection of the source is already the related field
  (`structArgs` at the field index, after `struct_family_eq`).
* The binder cases use `DeltaPar.lam_inv`/`forallE_inv`/`spine_lamHead`, `defeqDFC` for the
  context change, and `instN` for `betaR`; `structEta` re-chooses the parameters as the reduced
  parameter arguments (`EtaNE.structEta_args`, shared logic of the two closures).

End-to-end result: `cancel_iff_typedFront_B3 (henv : env.WF) (heq : env.HasCanonicalEq)
(hcase : ∀ U, CaseRedexDescends) (hunfold : ∀ U, UnfoldingCheckDescends)
(hmajor : ∀ U, MajorEtaDescends) (hProj : ProjFrontN env) (hElim : ElimFrontN env) :
Cancel env ↔ TypedFront env`. Compared with the brief, the only hypothesis outside the allowed
list is `MajorEtaDescends` (`EtaNormal.lean`): the descent at the root of the lift of the
composite step "structure eta at a neutral major, then one `ParRed` step", that is: if
`e.liftN 1 k = .app f m`, `m` typed above at a structure type with `params`, and
`ParRed Γ' (.app f (structExpand family info ls params m)) c`, then `c` is a lift of an `e'`
with `FullReduction Γ e e'`. Note that `params` are terms above, not necessarily lifts; the
descent needs the structure type of `m₀` below (a typing descent at a structure-typed term,
of the kind `ProjFrontN` gives for projections) and then `ParRed.descend` (B2).
