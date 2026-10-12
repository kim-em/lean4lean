# Route A (confluence-based) research log: strengthening under canonical `Eq`

Worktree `lean4lean-iota-strengthA`, branch `agent/iota-strengthA` off
`kim-em/agent/inductives-on-iota-work` (6f55d4da). Target: `IsDefEqU.weakN_iff`
(`Theory/Typing/UniqueTyping.lean`) under `env.HasCanonicalEq`. Brief:
`iota-port/briefs/strengthening.md`. Agent B (model route) is `abb59c622ac378134`, branch
`kim-em/agent/iota-strengthB`; B's Lean files that mine use were taken onto this branch
unchanged (0884ab44).

Not to be merged. Everything under `Lean4Lean/Theory/Typing/Strengthening/` is at zero
`sorry`; the only `sorryAx` reached is the inherited `VEnv.WF.patsStrong`
(`EnvLemmas.lean:381`), which every strong-system lemma depends on and which the pending
merge removes.

## 0. Reading (2026-10-12)

Read: the brief; PR #53's `STRENGTHENING_ATTEMPT_2026-10-09{,b}.md`, the direction logs B2,
B3, F and Astra's answers (attempts 1 to 6, round 7 A/B/C) and review 7; the predecessor's
`Strengthening/Cancel.lean`, `Final.lean`, `TypingFront.lean`, `Kripke.lean` (statements);
the present calculus: `Basic.lean` (`IsDefEq`; rules `pat`, `extra`, `projIota`,
`structEta`, `unitLike`; no `.elim`), `ChurchRosser.lean` (`Params`, `ParRed`, `NormalEqN`),
`FullReduction.lean` (`FullStep`), `PrefixUnfolding/Rule.lean` (`UnfoldingCheck`),
`FullChurchRosser.lean` (`FullCRDefEq`), `Confluence/WFParams.lean` (`WF.church_rosser`),
`Confluence/JoinableTyping.lean` (`HasTypeJ`, `church_rosserJ_of`), `Confluence/Patterns.lean`
(the concrete pattern table), `EqTyping.lean`, `CanonicalEq.lean`, `Injectivity.lean`,
`UniqueTyping.lean`.

Corrections to the brief established from the sources:

* `FullStep` is not context-free. `funEta` reads its domain annotation off a typing
  `Γ ⊢ e : Π domain body` in the current context, and the annotation need not be a lift
  (PR #53's `eta_does_not_preserve_support`); `structEta` reads its parameters off a typing;
  `projIota` carries two typings; `ParRed.extra` carries the pattern check
  `r.2.OK (IsDefEqU env univs Γ) m1 m2`; `delta`/`quotDelta` carry an `UnfoldingCheck`
  (typings and a `ConstSpineDefEq` in the opened telescope). What is context-free is the
  *syntax of the reduct* of every rule except the two eta rules.
* `NormalEqN` is not context-free either: `refl`, `appDF`, `projDF`, `etaL/R/Both`,
  `proofIrrel` carry `HasType` premises in `Γ` at types that need not be lifts;
  `lamDF` and `forallEDF` carry declarative `IsDefEq` comparisons of domains
  (`lamDF` compares its two displayed domains only declaratively: PR #53's
  `compress_domain_equality`).
* `HasTypeJ` is syntax-directed only at `const` and `app`; `other` is an arbitrary
  declarative typing of a `lam`/`forallE`/`proj`/`bvar`/`sort`. An induction on a `HasTypeJ`
  derivation therefore has no induction hypothesis under binders (the induction the brief
  suggested cannot be run); the right induction for typing descent is on the term
  (PR #53's `typingFrontN_iff_closures`, ported as `Closures.lean`).

## 1. Split with agent B (agreed, kept)

Shared base, ported by A: `Cancel.lean`, `TypingFront.lean` (B imports them). A: descent of the
Church-Rosser join (`NormalDescent.lean`, `CoreDescent.lean`). B: the observation model
(`Model.lean`, `ModelObstruction.lean`, `ModelBridge.lean`), `InhabitedProp.lean`,
`HeteroSubst.lean`, `ProofErasedSize.lean`. Neither edits `UniqueTyping.lean`.

## 2. What is proved (file, lines, statement)

All files in `Lean4Lean/Theory/Typing/Strengthening/`, namespace `Lean4Lean.VEnv` (Cancel)
or `Lean4Lean.VEnv.Strengthening`.

### 2.1 `Cancel.lean` (192 lines; PR #53's reduction, ported)

`Strengthening` (the open theorem as a predicate on `env`), `Front`, `Cancel`;
`strengthening_iff_cancel`, `strengthening_iff_front` (every WF env); `IsDefEqU.lam_body`,
`lam_domain`; the inhabited case `Cancel.inhabited` and the typed retraction `IsDefEqU.retract`
(substitution, no hypothesis); `IsDefEq.weakN_inv_of_down` (fixed-type descent from
existential descent, by unique typing).

### 2.2 `TypingFront.lean` (314 lines; PR #53's Eq encodings, ported; `PropFront` new)

`TypingFront`, `UninhabitedTypingFront`, `TypedFront` (fixed common type, both endpoints typed
below), `TypedFrontN`, `TypeFront`, `TypeFrontN`, `PropFront`. Under canonical `Eq`:
`canonicalEq_isPatCtor`, `canonicalEq_rigid` (from `WF.patCtor_resultRigid` at the registered
ι pattern of `Eq.rec`), `eqApp_injective`; `cancel_of_typingFront` (existential typing
descent gives `Cancel`: `Eq.refl a↑ : Eq A↑ a↑ b↑` above descends, `Eq` injectivity reads
`a ≡ b` back), `typingFront_iff_cancel`, `uninhabitedTypingFront_iff_cancel`,
`not_cancel_iff_typing_gap`; `typedFront_of_cancel`, `TypedFront.independent` (endpoints
typed below at any types); `typeFront_iff_typedFront`; **new**: `typeFront_iff_propFront`,
`typedFront_iff_propFront`:

```
PropFront env := ∀ U Γ Q P₁ P₂, OnCtx (Q :: Γ) → Γ ⊢ P₁ : Prop → Γ ⊢ P₂ : Prop →
  Q :: Γ ⊢ P₁↑ ≡ P₂↑ → Γ ⊢ P₁ ≡ P₂
```

(a comparison of types `A B : Sort u` is the comparison of the propositions `Eq (Sort u) A A`
and `Eq (Sort u) A B`; so the universe of the compared types is immaterial: the obstacle is
impredicativity of `Prop` with proof irrelevance, not universe bookkeeping). B added
`InhabitedProp.lean`: `InhabitedPropFront ↔ PropFront ↔ TypedFront` (encoding `P ↦ Π (h : P). P↑`,
inhabited by the identity), so restricting to inhabited propositions is no weakening.

### 2.3 `Closures.lean` (352 lines; PR #53's term induction, ported; no eliminator component)

`TypingFrontN`, `AppFrontN`, `ProjFrontN`, `PiExposureN`, `PiExposureRedN`;
`typingFrontN_iff_cancel`; **`typingFrontN_iff_closures : TypingFrontN ↔ AppFrontN ∧ TypeFrontN ∧
ProjFrontN`** (structural induction on the term; `ElimFrontN` and the case-schema rows of
PR #53 do not exist in this calculus); `typedFrontN_iff_typeFrontN` (under canonical `Eq`);
`AppFrontN.of_piExposure`, `AppFrontN.piExposure`; exposure through reduction:
`parRed_forallE_inv`, `fullStep_forallE_inv`, `fullReduction_forallE_inv`,
`normalEqN_forallE_inv_r`, `exposure_reduces` (a type convertible to a `Π` reduces to a `Π`, by
`WF.church_rosser`), `PiExposureN.of_red`, `cancel_of_piExposureRed`.

### 2.4 `NormalDescent.lean` (606 lines; new)

The descent of a normal equality between lifts, for an arbitrary renaming `Ctx.Lift' ρ Γ Γ'`.

* `IsLam`, `IsProof Γ e := ∃ P, Γ ⊢ e : P ∧ Γ ⊢ P : Prop`; shape inversions of `lift'`;
  `IsProof.of_lift`, `IsProof.lift'`, `IsProof.transfer` (proofness is read off the lift by
  unique typing and the context-freeness of sort levels), `IsProof.descend` (two proofs typed
  below at convertible types are convertible below), `IsProof.app_fn`, `not_isProof_fn`,
  `not_isProof_major` (by `proj_result_prop_of_major_proof`), `not_isLam_major`,
  `IsProof.of_etaBody` (the eta body of a proof is a proof, by `imax`).
* `NormalEqS`: `NormalEqN true` with `¬ IsLam f₁ → ¬ IsLam f₂ →` on `appDF` (strict: no lambda
  in function position of a congruence); `toNormalEqN`, `defeq`, `defeqDFC`.
* `varSpine`, `NormalEqS.spine_inv`: a strict normal equality between the same fresh-variable
  spines of two lifts, not a proof, peels to a strict normal equality of the further lifted
  pair at index `≤ n` in an extended context (`etaBoth` extends the spine and lowers the index;
  `appDF` shortens it).
* **`NormalEqS.descend`**: for `Ctx.Lift' ρ Γ Γ'`, `Γ ⊢ a : A`, `Γ ⊢ b : B`,
  `Γ' ⊢ a.lift' ρ ≡ₛ[n] b.lift' ρ`: (mode 2) `Γ ⊢ A ≡ B → Γ ⊢ a ≡ b`, and (mode 0)
  `¬ IsLam a → ¬ IsLam b → ¬ IsProof Γ a → Γ ⊢ a ≡ b`. **No hypothesis on the environment
  beyond `WF`**: no canonical `Eq`, no typed front. Strong induction on the comparison index.
  Proof pairs in mode 2 are discharged by proof irrelevance below (the common type is a
  proposition below); `appDF` descends the function pair in mode 0 and reads the agreement
  of the argument types below from unique typing; `lamDF`/`etaL`/`etaR` in mode 2 get their
  domains from `Π`-injectivity below; `etaBoth` is peeled by `spine_inv` (hence the arbitrary
  renaming); along mode-0 positions nothing is a proof (`imax`) and nothing is a lambda
  (strictness, or typing for projection majors).
* `StrictJoinRepair hE` (residual, named): the join of a lifted equation between terms typed
  below at a common type can be chosen with lifted reducts and a strict normal equality;
  `typedFront_of_strictJoinRepair : StrictJoinRepair hE → TypedFront E`.

### 2.5 `CoreDescent.lean` (new)

* `quot_check_of_typed`: the alignment checks of the quotient rule hold below whenever the
  instance is typed below (`QuotRegistered.major_type` types the major `Quot.mk α' r' a` at
  `Quot α r`; `Quot` is rigid; the universe guard is context-free). PR #53 discharged this
  check with the typed front; typing suffices.
* `CheckDescends` (under `[Params]`), `WF.checkDescends : @CheckDescends (henv.params U)`
  (definitions are unguarded, registered ι rules carry a context-free universe guard, the
  quotient rule by `quot_check_of_typed`).
* **`ParRed.descend`**: a core parallel step (β and the pattern rules) above on the lift of
  a term typed below is the lift of a step below, given `CheckDescends`. No other obligation.

### 2.6 Taken from B (0884ab44): `InhabitedProp.lean`, `HeteroSubst.lean` (`NormalEqF.instN_lr`,
`NormalEqF.contract_proofArgs`, `NormalEqF.contract`), `ProofErasedSize.lean` (`μ`, the
proof-erased size, with `μ_app/lam/forallE/proj`, `μ_defeqDFC`, `μ_inst_proof`,
`μ_instN_proof`, `μ_lift'`).

## 3. The chain, and where it stops

Under `WF` and canonical `Eq` (the `Eq` hypothesis is used only in the encodings of 2.2):

```
Strengthening ⇔ Front ⇔ Cancel ⇔ TypingFront ⇔ TypingFrontN
TypingFrontN ⇔ AppFrontN ∧ TypeFrontN ∧ ProjFrontN
AppFrontN   ⇐ PiExposureRedN ∧ TypeFrontN
TypeFrontN ⇔ TypedFrontN ⇔ TypedFront ⇔ TypeFront ⇔ PropFront ⇔ InhabitedPropFront
TypedFront  ⇐ StrictJoinRepair
```

Confluence (`WF.church_rosser`) gives, for `Q :: Γ ⊢ a↑ ≡ b↑ : T↑`, reductions
`a↑ ↠ n₁`, `b↑ ↠ n₂` and `NormalEq (Q :: Γ) n₁ n₂`. Route A splits the descent in two:

1. **Reductions.** `ParRed.descend`: core steps descend with no obligation. The remaining
   `FullStep` rules: `projIota` (free: both typings are read off the typed instance),
   `funEta`/`structEta` (reducts are not lifts; PR #53's `EtaNE` closure shows the eta
   junk is absorbed, 1100 lines on the old calculus, not ported), and `delta`/`quotDelta`
   (singleton prefix unfolding: its `UnfoldingCheck` aligns the recursor's indices with the
   constructor's, i.e. compares terms that the major, typed below, proves *propositionally*
   equal: `PropEqFront`, see 4.2).
2. **Normal equality.** `NormalEqS.descend`: strict normal equalities descend with no
   obligation. The non-strict nodes, lambdas in function position of a congruence, are
   exactly: a matched pair of head β-redexes `(λ h : A₁. s₁) x ≡ₚ (λ h : A₂. s₂) y`, or an
   eta node `λ h : A₁. s₁ ≡ₚ e'` in function position. Their descent needs `A₁ ≡ A₂` below
   (the domains are types below with convertible lifts, the declarative `lamDF` premise), and
   nothing in the derivation supplies it when the argument pair `(x, y)` carries no type
   information below: when `x, y` are *proofs* (`A₁ A₂ : Prop`, inhabited: B's
   `InhabitedPropFront`, which B's `μ`-contraction removes, 4.1) or when `x, y` are *lambdas*
   (`A_i ≡ Π C_i D_i` below; `C₁ ≡ C₂` is again a type comparison: B's `ArgLamFront`). When
   `(x, y)` is any other pair, mode 0 on it gives `x ≡ y` below, hence `A₁ ≡ A₂` by unique
   typing, and the pair closes.

So the one configuration a join can put in the way of descent is a β-redex (or eta-lambda)
pair in function position whose arguments are lambda pairs. Confluence does not produce
β-normal joins: the calculus does not normalise (Abel-Coquand: impredicative `Prop` with
proof irrelevance), and a matched β-pair can persist through every reduct (a looping term
`Ω_A` reduces only to itself, so `Ω_{A₁}↑ ≡ Ω_{A₂}↑` above has only the non-strict join, and
`Ω_{A₁} ≡ Ω_{A₂}` below is exactly `A₁ ≡ A₂` below). This is the precise form of PR #53's
"the calculus does not normalise": the eta and proof-irrelevance circularities they found are
not obstacles on the new calculus (eta is peeled, proofs are dispatched at their common type),
β-pairs with lambda arguments are.

## 4. The residual obligation

### 4.1 Statement

**`StrictJoinRepair`** (`NormalDescent.lean`) is the ONE named obligation of route A:

```
StrictJoinRepair hE := ∀ U Γ Q a b T, OnCtx Γ → IsType Γ Q → Γ ⊢ a : T → Γ ⊢ b : T →
  Q :: Γ ⊢ a↑ ≡ b↑ : T↑ →
  ∃ a' b', FullReduction Γ a a' ∧ FullReduction Γ b b' ∧ ∃ n, NormalEqS n (Q :: Γ) a'↑ b'↑
```

`typedFront_of_strictJoinRepair : StrictJoinRepair hE → TypedFront E`, hence `Cancel`, hence
`Strengthening`, through 2.1 to 2.3 and PR #53's replay (not ported: its K-guards are the
`PropEqFront` instances of 4.2). The statement bundles both halves (lifted reducts: the replay;
strict normal equality: the β-pair configuration). It is a localisation, not a weakening: the
β-pair configuration with lambda arguments is equivalent to `TypeFront` (B's `ArgLamFront`,
`λ (z : C). z` typed below for any type `C` below), hence to `TypedFront`.

### 4.2 What might be weaker

* `PropEqFront`: `Γ ⊢ e : Eq T a b`, `Q :: Γ ⊢ a↑ ≡ b↑ ⇒ Γ ⊢ a ≡ b`. The K/singleton guards of
  prefix unfolding are instances (the major is the witness). Neither B nor I see an encoding
  of `TypedFront` into it (one needs a proof of `a = b` below), so the *replay* half may be
  strictly easier than the *join* half. Not formalised.
* B's `(μ, n)` refinement (`ProofErasedSize.lean`, `HeteroSubst.lean`): contracting a β-pair
  with proof arguments is sound above (`NormalEqF.contract_proofArgs`) and drops the
  proof-erased size `μ` by at least 2 while the comparison index may grow; with the
  lexicographic `(μ Γ a + μ Γ b, n)` the proof-argument case closes, leaving lambda-argument
  pairs only. The obstacle to running it in `NormalEqS.descend` is that contraction yields a
  `NormalEqN` derivation, not a strict one (refl leaves over subterms containing the proof
  variable become congruences, including over β-redexes inside those subterms), so the
  strictness invariant is not preserved; and the analogous homogeneous instantiation for
  non-proof arguments (`NormalEqN.instN`, index-preserving) duplicates the argument and may
  increase `μ`. The two measures are incompatible.
* Planned (section 5): a descent **up to parallel substitutions** that needs neither measure:
  descend pairs `(a, b)` living in `Δ₁ ++ Γ`, `Δ₂ ++ Γ` with instantiations `σ, σ'` of the
  `Δ`s, convertible below at non-proof entries, concluding `a[σ] ≡ b[σ']`; a β-pair extends
  `σ, σ'` by `(x[σ], y[σ'])` and recurses on the *open* bodies with the sub-derivation (index
  only); proof variables are met only at mode-2 positions (their type agreement comes from the
  use site) and non-proof arguments are compared first in mode 0. Then the residue is exactly
  the lambda-argument pairs, with no `μ` and no strictness beyond them.

### 4.3 Judgment

Is `StrictJoinRepair` (equivalently `TypedFront`, `Cancel`, the theorem) provable?

* It is equivalent to the open theorem; no proof by route A. The route is now exhausted in
  the sense that every rule of the join has been descended except the β-pair configuration
  with lambda arguments, and that configuration *is* the theorem (it is `TypeFront` for the
  argument lambdas' domains). A proof would have to show that the two domains `C₁, C₂` of the
  argument lambdas agree below, from the fact that their lifts agree above; i.e. recursively
  the same problem, on types that are subterms of the join's reducts, with no measure
  (reducts are unbounded; PR #53's refutations of every syntactic rank apply unchanged).
* It is true in every normalising fragment: if the two sides have β-normal reducts the join
  is strict and `NormalEqS.descend` closes it (given replay). So a counterexample under
  canonical `Eq` must use non-normalising terms with persistent matched β-pairs whose domains
  agree only above; the Abel-Coquand loop lives in impredicative `Prop` and its annotations
  are propositions, which is exactly the inhabited-proposition instance of the residue. I
  found no such example; building one needs two propositions typed below, inhabited below,
  with lifts convertible above and not below, which is again the theorem.
* Canonical `Eq` enters only the encodings (2.2) and PR #53's coverage of the singleton
  rules in `WF.church_rosser`. Nothing in the descent uses it. So the hypothesis does not
  make the residue easier; it only removes PR #53's countermodel (which lives at a β-pair over
  a proof variable, the `K v q` conversion).
* Estimate: not provable by syntactic means available in this calculus. If it is provable at
  all, the argument must be semantic and must interpret the variable `q` of an uninhabited
  type `Q` non-trivially (B's model route shows that the observation model cannot: proofs and
  opaque constants have no observations, `extension_not_freshReflection`).

## 5. Designs examined for the next refinement (not mechanised)

Goal: relax `NormalEqS` so that the residue is exactly B's `LamDomainFront` (two lifted
abstractions typed below at unrelated types, equal above: `lamDomainFront_iff_typeFront`,
`InhabitedProp.lean`). Three designs, with the exact point where each needs more than I had
time to build:

1. **`(μ, n)` with heterogeneous contraction** (B's `HeteroSubst.lean`, `ProofErasedSize.lean`).
   A β-pair with proof arguments contracts above to `s₁[x] ≡ₚ s₂[y]`; `μ` drops by 2, the index
   may grow. Obstacle: the contracted derivation is a `NormalEqN`, and the refl leaves over
   subterms `t` containing the proof variable become congruences over `t[x]` vs `t[y]`; when `t`
   contains a β-redex with a lambda argument, `(λ k : C[x]. u[x]) (λ m. v[x]) ≡ₚ (λ k : C[y]. …)`
   is a lambda-argument β-pair whose domains differ by `x` vs `y` (`C = P h`), i.e. the residue
   configuration, although the instance is benign (both sides are instances of the same open
   term). So strictness is not preserved by contraction, and the information that makes the
   instance benign is lost. Also, the homogeneous instantiation that handles non-proof
   arguments (`NormalEqN.instN`, index-preserving) duplicates the argument, so `μ` may grow:
   the two measures are incompatible in one induction.
2. **Descent up to parallel substitutions.** Pairs `(a, b)` in contexts `Γ₁`, `Γ₂` with
   substitutions `σ, σ'` into `Γ`, convertible at non-proof entries; conclude `a[σ] ≡ b[σ']`.
   A β-pair extends `σ, σ'` by `(x[σ], y[σ'])` and recurses on the open bodies with the
   sub-derivation (index only). Proof variables are met only at mode-2 positions, where the use
   site supplies the agreement of the instantiated types; refl leaves become a structural
   congruence induction on the common subterm in the two modes, which never produces a residue
   (the two types of a proof variable in a common term are instances `D[σ]`, `D[σ']` of one
   open type `D`, compared by the same induction). Nested β-chains are fine because the
   conclusion is about the instantiated terms. Obstacle: the eta cases. The body of
   `etaL (λ C. e₀) b` is `(e₀, app b.lift (bvar 0))`, and `app b.lift (bvar 0)` is typed in a
   context `C' :: Γ₂` only if `b : Π C' _` in `Γ₂`, which does not follow from `b[σ'] : Π …` in
   `Γ` (`B = P h` with `P y ↠ Π …` by a `K`-reduction while `P h` is stuck): that would be a
   `Π`-exposure in `Γ₂`, a `TypedFront`-strength statement. Working with substituted typings
   only removes this, but the proofness bridge between the lifted term above and the
   substituted term below (needed at `proofIrrel` leaves in mode 0 and for the non-proofness
   of peeled spines) then has to be carried as an invariant and does not propagate to the
   arguments of applications without an open typing. A per-term "open typing or bridge"
   invariant with the eta right side treated specially is the way through; I did not build it.
3. **Head-redex contraction along spines** (index only, no `μ`, no `σ`). For a β-pair with
   non-proof non-lambda arguments in function position of a spine, mode 0 on the argument pair
   gives `x ≡ y` below, the body derivation instantiated at `x⇑` on both sides
   (`NormalEqN.instN`) rebuilds the spine derivation with index decreased by one (the `lamDF`
   node disappears), and `s₂[x] ≡ s₂[y]` closes below by congruence. This handles nested
   β-chains but not proof arguments (`x ≡ y` is unknown). Needs the `appDF` case to see the
   whole spine. Combined with 1 it would still leave both residues.

Also not done: `FullStep.projIota` descent (free: the field is typed below by
`HasType.projIota_field`, whose saturation hypothesis comes from
`VConstructorShape.saturated_of_hasType` through `Ordered.projectionShape` and
`RawCtorShape.constructorShape`; plumbing only), and the statement of the prefix-unfolding
descent as a `PropEqFront` consequence; the eta replay is PR #53's `EtaNE` and is not ported.
