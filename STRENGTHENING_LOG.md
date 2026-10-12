# Route B (model-based) research log: strengthening under canonical `Eq`

Branch `agent/iota-strengthB` (worktree `lean4lean-iota-strengthB`), off
`kim-em/agent/inductives-on-iota-work` at 6f55d4da, merged with agent A's shared base
`kim-em/agent/iota-strengthA` at d112421a. Target: `IsDefEqU.weakN_iff`
(`Theory/Typing/UniqueTyping.lean`) under `env.HasCanonicalEq`. Every file under
`Lean4Lean/Theory/Typing/Strengthening/` is at zero `sorry`; the only `sorryAx` any of them
reaches is the upstream `VEnv.WF.patsStrong` (through `WF.orderedStrong`, used by the model,
unique typing and confluence alike), which the pending reduct-typing merge removes. This file
is not to be merged.

## 1. Route and outcome in one paragraph

The observation model (`HeadInjectivity/Model`) interprets a term by its observations in a
*target* context under an anchor substitution and observation sets for the variables. It is
sound (`WF.soundEnv`). Route B asked whether soundness, applied to the lifted equation
`Q :: Γ ⊢ a↑ ≡ b↑`, descends to `Γ ⊢ a ≡ b`. Answer, checked in Lean on the ι pattern
calculus: the model never reads the source context, so the lifted equation says exactly that
`a` and `b` have the same observations *in every target in which `Q` is inhabited*
(`KEq.lift_iff`); the two further steps the route needs are the passage to all targets
(`ModelStrengthening`, the semantic form of the very statement) and reflection of observation
equality into definitional equality, and reflection is **false** in the new calculus as in the
old (`heterogeneous_reflection_false` for every WF environment; `extension_not_freshReflection`,
`extension_not_typedReflection` under canonical `Eq`, by two fresh axioms of a fresh type). The
model's own classes are declarative classes of the target, and descending them from `Q :: Γ`
to `Γ` is literally the fixed-type front `TypedFront` (`keyFaithful_iff_typedFront`). So route
B reproduces the predecessor's obstruction with no gain, and canonical `Eq` enters none of its
statements (the model is `Eq`-blind: proofs have no observations, `KEq.proofs`). The useful
output of the route is negative and exact (section 3), plus the analysis of section 4, which
localises the open statement to one configuration of a confluence join, shared with agent A.

## 2. What exists (files, line counts, all checked)

Mine (namespace `Lean4Lean.VEnv.StrengtheningModel` unless noted):

* `Strengthening/Model.lean` (215 lines). `KEq` (all-target observation equality), `KEqOn`
  (restricted to targets satisfying a predicate), `KEq.sound` (from `WF.soundEnv` through
  `IsDefEq.strong henv.orderedStrong`), symmetry and transitivity, `proof_no_observations`,
  `KEq.proofs` (two proofs of any two propositions are `KEq`), `substEq_cons`, `tv_cons_empty`,
  `tv_tail` (extending and restricting typed valuations across the removed binder),
  `Inhabits`, **`KEq.lift_iff`**: `KEq (Q :: Γ) a↑ b↑ ↔ KEqOn Γ (Inhabits Q) a b`,
  `ModelStrengthening` (the named passage from inhabited targets to all targets),
  `KEqOn.toKEq_of_inhabited` (the inhabited case is trivial, as everywhere).
* `Strengthening/ModelObstruction.lean` (557 lines). `KeyFaithful`, `TypedFront'` (inline copy of
  the shared statement), **`keyFaithful_iff_typedFront`**; `heterogeneous_reflection_false`;
  `FreshReflection`, `front_of_freshReflection`; `OpaqueHead`, `rigid_typed_wrap_absurd`,
  `opaque_no_observations` (with the new `Obs.pat` clause), `opaque_KEq`;
  `opaque_type_exclusions`, `NonFunctionNonProof`, `Stationary`, `normalEq_const_name`,
  `parRed_const_stable`, `fullStep_const_stable`, `stationary_of_step_stable`,
  `stationary_constants_not_defeq` (through `WF.church_rosser`), `recursorRegistry_eq_none_of_rigid`,
  `opaque_stationary`, `opaque_constants_not_defeq`, `opaque_not_freshReflection`;
  `addAxiom`, `addAxiom_installed`, `addAxiom_wf`, `addAxiom_le`, `extension`, `FreshNames`,
  `extension_properties` (WF and canonical `Eq` preserved), `OpaqueHead.of_eq`,
  `opaque_of_absent`, **`extension_not_freshReflection`**, `TypedReflection`,
  **`extension_not_typedReflection`**, `exists_not_freshReflection`.
* `Strengthening/ModelBridge.lean` (50 lines). Against agent A's shared statements:
  `keyFaithful_iff_typedFront'`, `keyFaithful_iff_propFront` (canonical `Eq`),
  `cancel_of_freshReflection`, `typedFront_of_modelRoute` (`ModelStrengthening` and
  `TypedReflection` give `TypedFront`; the second is false).
* `Strengthening/InhabitedProp.lean` (73 lines, namespace `Lean4Lean.VEnv.Strengthening`).
  `InhabitedPropFront` (descent of a conversion between propositions typed and inhabited below),
  `selfArrow`, **`inhabitedPropFront_iff_propFront`**, `inhabitedPropFront_iff_typedFront`.
  This kills the hope (mine and A's, independently) that the residue of the normal-equality
  descent is weaker than the open statement: `P ↦ (P → P)` is inhabited by the identity and
  `Π`-injective. Also `LamDomainFront` (two lifted abstractions typed below at unrelated types,
  convertible above, have convertible domains below: the mode-0 residue of the descent),
  `lamDomain_of_common_type` (with a common type below it is `Π`-injectivity, which is why the
  residue sits at positions without type information), **`lamDomainFront_iff_typeFront`**,
  `lamDomainFront_iff_typedFront`.

* `Strengthening/HeteroSubst.lean` (124 lines, namespace `Lean4Lean.VEnv.Strengthening`,
  `[Params]`). **`NormalEqF.instN_lr`**: heterogeneous substitution of two normally equal terms
  into the two sides of a normal equality, at any depth, in the left-instantiated context (the
  library had the homogeneous `NormalEqN.instN` and the one-term `NormalEqF.instN_r`; every
  right-hand typing premise is retyped by `retype_instN_r`). Corollaries
  `NormalEqF.contract_proofArgs` and `NormalEqF.contract`: a matched head β-redex pair with
  proof arguments, or with normally equal arguments, contracts to a normal equality of the
  contracta. This is the lemma that removes the proof-argument case from the residue of
  section 4.

* `Strengthening/ProofErasedSize.lean` (235 lines, namespace `Lean4Lean.VEnv.Strengthening`,
  `[Params]`, imports agent A's `NormalDescent.lean` for `IsProof`). **`μ`**, the proof-erased
  size (nodes inside proof subterms count `0`), with `μ_proof`, `μ_bvar`/`μ_sort`/`μ_const`,
  `μ_app`, `μ_lam`, `μ_forallE` (a `Π` is never a proof: `not_isProof_forallE`,
  `not_isProof_of_sort`), `μ_proj`, `μ_defeqDFC` (context conversion, with `IsDefEqCtx.symm'`
  and `IsProof.defeqDFC_iff`), `IsProof.instN_iff` (proofness is invariant under
  instantiation of typed terms), **`μ_instN_proof`**/`μ_inst_proof` (substituting a proof for
  a proof variable leaves `μ` unchanged, at any depth), `IsProof.lift'_iff`, `μ_lift'`
  (invariance under renaming). This is the outer component of the `(μ, n)` measure of
  section 4, requested by agent A for the relaxation of `NormalEqS` (section 7).

Agent A's shared base, used here: `Cancel.lean` (192), `TypingFront.lean` (314), `Closures.lean`
(352): `Strengthening ↔ Front ↔ Cancel`, `TypedFront ↔ TypeFront ↔ PropFront` under canonical
`Eq`, `TypingFrontN ↔ AppFrontN ∧ TypeFrontN ∧ ProjFrontN`.

## 3. The exact lemma chain of route B and where it fails

```
Q :: Γ ⊢ a↑ ≡ b↑
  ⇒ KEq (Q :: Γ) a↑ b↑                              KEq.sound          (every WF env)
  ⇔ KEqOn Γ (Inhabits Q) a b                        KEq.lift_iff       (every env)
  ⇒ KEq Γ a b                                       ModelStrengthening (OPEN, semantic form)
  ⇒ Γ ⊢ a ≡ b : T   (a b : T below)                 TypedReflection    (FALSE)
```

* `KEq.lift_iff` is the formal content of "the observations of a lifted term are those of the
  term": the model reads the source context only through the anchor and the observation sets
  (`Obs.lift_cons_iff`); an anchor for `Q :: Γ` is an anchor for `Γ` together with an inhabitant
  of `Q`; the observation set of the new variable can be taken empty. Consequently the lifted
  equation is silent about the target `Δ = Γ` with the identity anchor whenever `Q` has no
  inhabitant in `Γ`: soundness alone cannot reach the conclusion.
* `TypedReflection` and `FreshReflection` fail: in `extension env I a b` (fresh axioms
  `I : Type`, `a b : I`, WF and canonical `Eq` preserved) the constants `a`, `b` have no
  observation in any target (`opaque_no_observations`: a rigid constant's observations are typed
  at observations of its type, which must be a sort or a `Π`, and `I`'s observations are rigid
  spines), so `KEq` identifies them, while both are stationary under `FullReduction`
  (`fullStep_const_stable`: no rule, pattern, prefix unfolding or structure/function eta
  applies) and `NormalEq` compares constants by name, so `WF.church_rosser` separates them. The
  model loses the identity of value constants of opaque types; the predecessor's self-looping
  definitions give a second refutation, not ported.
* Descending the model's keys is the theorem: `KeyFaithful ↔ TypedFront` (`ElCls.collapse`).
  The observations in a target `Q[σ] :: Δ` carry classes of that target; translating them to
  `Δ` is class descent, i.e. `TypedFront`. This is the same circularity as the predecessor's
  `keyFaithful_iff_typedFront`, now on the ι pattern calculus.

Where canonical `Eq` is used on route B: nowhere in the model statements. It appears only in
the refutation (`WF.church_rosser` separates the two opaque constants) and, through agent A's
`TypingFront.lean`, in the equivalences `TypedFront ↔ TypeFront ↔ PropFront` and
`Cancel ↔ TypingFront`. A model-based proof cannot use the hypothesis because the model is
blind to proofs and to `Eq` (an `Eq` proof below carries no observation).

## 4. The analysis shared with agent A: where the open statement actually bites

Both routes end at `TypedFront` (`Γ ⊢ a b : T`, `Q :: Γ ⊢ a↑ ≡ b↑ : T↑` ⇒ `Γ ⊢ a ≡ b : T`).
By `WF.church_rosser` above, `a↑ ↠ n₁`, `b↑ ↠ n₂`, `NormalEqN n n₁ n₂`. Assume (agent A's
replay, the predecessor's `EtaNE` machinery) `n_i = m_i↑` with `m_i` typed below. Descend the
normal equality by induction on the lexicographic pair `(μ, n)`, `μ` the proof-erased size of
the pair below (nodes inside proof subterms count 0), with the claim: *`m₁ m₂` typed below, and
at a common type below whenever they are proofs or the node is eta-shaped, give `m₁ ≡ m₂`
below*. Positions are of two kinds: mode 2 (common type below: root, arguments once the
function pair is equal, bodies and domains of matched binders) and mode 1 (function position
of an application, data major of a projection). Checked case by case (prose; agent A is
mechanising it as `NormalEqN.descend_betaNormal`):

* proofs at mode 2 close by `proofIrrel` below, so **no proof-irrelevance leaf ever needs an
  obligation** (correcting the brief's expectation that the leaf needs typing strengthening);
* `refl`/`sortDF`/`constDF` are context-free; levels are context-free, so Prop-ness of a pair
  is decided below and agrees above;
* `appDF` at mode 2: the function pair is at mode 1 and is a non-proof; once equal below, the
  argument pair has a common type (`Π`-injectivity below);
* `lamDF` at mode 2: the declarative domain premise of `NormalEqN.lamDF` costs nothing, the
  domains agree below by `lam_inv` and `Π`-injectivity at the common type;
* `forallEDF`: sorts are common; domains are normally equal (unlike `lamDF`);
* `etaL`/`etaR` at mode 2: eta below, bodies by induction (`μ` non-increasing, `n` drops by 2);
  `etaBoth` with non-lambda sides is redundant (its body is a fresh-variable spine comparison
  `appDF (D, refl 0)`, nested `etaBoth`, or `proofIrrel`, the last making the pair proofs) and
  unlifts to a smaller `n`;
* `projDF`: a Prop-structure major makes the projection a proof (`projDF`'s level condition);
  data majors are spines, handled at mode 1;
* mode-1 spines with the same `bvar`/`const` head: equal below by induction along the spine,
  types agree by uniqueness; distinct heads are impossible for non-proofs in `NormalEqN`;
* **matched head β-redex pairs** `(λ (h : A₁). s₁) x ≡ₚ (λ (h : A₂). s₂) y` in mode 1 (the two
  lambdas have no common type; the lamDF domain premise is declarative):
  - `x y` proofs: contract below on both sides and compare `s₁[x] ≡ s₂[y]` at the common type;
    above, heterogeneous substitution of the `proofIrrel` leaf into `s₁ ≡ₚ s₂` is a `NormalEqN`
    derivation (refl leaves containing the proof variable become congruences ending in
    `proofIrrel`); `n` may grow, `μ` strictly drops (`μ (s[x]) = μ s`). **Not an obstruction.**
  - `x y` mode-1-resolvable non-proofs (spines, projections, sorts, `Π`): the argument pair is
    equal below by induction, so `A₁ ≡ A₂` below by uniqueness, and `lamDF` closes.
  - `x y` themselves a **lambda pair** (or a β-redex pair with a lambda head): the argument
    lambdas `λ C₁ t₁`, `λ C₂ t₂` sit at mode 1, their domains are only declaratively convertible
    above, nothing determines `C₁ ≡ C₂` or `A₁ ≡ A₂` below, and contraction duplicates the
    argument (`μ` can grow). **This is the single residual configuration.**

Refinement of the residual case, after `NormalEqF.contract`: contracting the β-pair is always
sound above, and the proof-erased size drops whenever the abstracted variable occurs at most
once in the body, or occurs at positions whose types are determined below (argument of a
common spine head, root, operand of a resolvable application): in all those cases the domains
`A₁ ≡ A₂` follow from the typing of the use sites below. What remains is an abstracted
variable that occurs several times and only at undetermined positions (as the argument of
another abstraction bound by a β-redex, or applied to abstractions), i.e. nested β-redexes with
abstraction arguments; eliminating them is β-normalisation restricted to such redexes.

The residual is equivalent to `TypeFront` (take `t_i := bvar 0`: `λ (z : C₁). z`,
`λ (z : C₂). z` are typed below and their lifts are `lamDF`-normally equal above), hence to
`TypedFront` and `PropFront`; agent A is recording it as `HeadRedexDomainFront` with the
equivalence. So nothing is weakened, but the localisation is sharp: the open statement is used
*only* to align the domains of two lifted abstractions that are arguments of a matched β-redex
pair in the confluence join. Removing such pairs from the join is β-contraction at those
positions; each contraction can create new such pairs (copies of the argument landing as
arguments of other redexes), and its termination is a normalisation statement about Lean's
own theory (with `VDecl.WF.mutualDef` admitting non-terminating definitions), which has no
proof here. Conversely the reason `NormalEqN.lamDF` compares domains declaratively is
`FullStep.funEta`'s free annotation, needed for confluence with eta as a reduction; a
confluence theorem with structurally compared lambda domains would close the descent, and its
transitivity-through-eta case is exactly a D-join of two types known only convertible, the
same circularity in reduction clothing (the predecessor's `eta_does_not_preserve_support`).

## 5. The remaining obligation (one theorem) and judgment

```lean
/-- Descent of conversions between propositions typed below: `Γ ⊢ P₁ P₂ : Prop`,
`Q :: Γ ⊢ P₁↑ ≡ P₂↑` give `Γ ⊢ P₁ ≡ P₂`. Equivalent under `WF` and canonical `Eq` to
`TypedFront`, `TypeFront`, `InhabitedPropFront`, `KeyFaithful`, and (given the replay of
reductions and the normal-equality descent of section 4) to `Cancel`, hence to
`IsDefEqU.weakN_iff`. What is missing is exactly the alignment below of the domains of two
lifted abstractions that are arguments of a matched head β-redex pair in a confluence join. -/
theorem propFront (henv : env.WF) (heq : env.HasCanonicalEq) : Strengthening.PropFront env
```

(`PropFront` is agent A's shared definition in `TypingFront.lean`; `InhabitedPropFront` and
`KeyFaithful` are mine.)

Judgment. The model route cannot prove it (section 3), and no model built as a least fixed
point of finite observations can, since any reflecting model must distinguish stuck constants
by name, i.e. be the term model. I believe the statement is true for the environments that
matter (the realizability of `HasCanonicalEq` by the prelude) and plausibly for every
well-formed canonical-`Eq` environment, because the only configuration that needs it (section
4) is one where a β-redex pair with abstraction arguments survives in the join, and in any
normalising fragment such joins can be replaced by head-normal ones, after which agent A's
`descend_betaNormal` gives `TypedFront` from replay alone, with no hypothesis on the
environment. I do not believe it is provable in Lean by the methods available here: the
remaining step is a normalisation-strength statement about Lean's own theory (or an equivalent
reorganisation of confluence with structurally compared lambda domains, whose
transitivity-through-eta case needs the same statement), and `VDecl.WF.mutualDef` admits
non-terminating definitions, so even weak head normalisation of the relevant redex pairs is
unavailable in general. A proof would have to avoid normalisation entirely, i.e. find an
invariant of the matched-redex-pair configuration not present in the derivation; none of the
candidates (sizes, indices, universe levels, erased sizes, inhabitation, propositional equality
below) survives: sizes and indices fail by duplication, universe levels by impredicativity and
the proof/type alternation, inhabitation by `P ↦ P → P`, and propositional equality below by
the absence of funext in a canonical-`Eq` environment (it is a genuine weakening,
`PropEqFront`, but it only covers the K/singleton guards of replay, not the residue).

No counterexample under canonical `Eq`: a counterexample would have to be a pair whose lifts
are convertible above through a join containing a matched β-redex pair with abstraction
arguments whose domains are not convertible below, i.e. it would contain a smaller
`TypeFront` failure in its join, and the predecessor's search (`Candidates.lean`, `Hunt.lean`)
found no mechanism producing one; the regress argument (the only root use of the removed
variable is proof irrelevance against it, which the mode-2 dispatch shows is never needed)
points the same way.

## 6. State of the joint reduction at the time of this report

Agent A's `NormalDescent.lean` (merged here at 6852afc3): `NormalEqS` (normal equality with no
lambda in function position of a congruence), `NormalEqS.descend` (descent of such an equality
between lifts of terms typed below, along any renaming, with no hypothesis on the environment
beyond `WF`), and the residual `StrictJoinRepair` (the join of a lifted equation can be chosen
with lifted reducts and a strict normal equality) with `typedFront_of_strictJoinRepair`. So:

```
weakN_iff ⇔ Strengthening ⇔ Front ⇔ Cancel                        (A, every WF env)
Cancel ⇔ TypingFront ⇔ ... ⇐ TypedFront ∧ PiExposureN ∧ ProjFrontN  (A, canonical Eq)
TypedFront ⇔ TypeFront ⇔ PropFront ⇔ InhabitedPropFront ⇔ KeyFaithful (A, B; canonical Eq)
TypedFront ⇐ StrictJoinRepair                                       (A, every WF env)
StrictJoinRepair ⇐ replay of the join (lifted reducts) ∧ head-redex-free normal equality
```

The replay part (reductions above from a lift are lifts of reductions below): agent A's
`CoreDescent.lean` (in progress) shows the core parallel steps and all concrete pattern checks
descend from typing alone, so the replay residue is the two eta rules (non-lift reducts, the
predecessor's eta-chain invariant) and singleton prefix unfolding (K-alignment of the indices
of a major typed below: `PropEqFront`, a conversion between propositionally equal terms, which
I could not reduce to `TypedFront` and which may be a genuine weakening). The join part: with
`HeteroSubst.lean` and `ProofErasedSize.lean`, agent A is relaxing `NormalEqS` to allow head
β-redex pairs with proof arguments (contracted, `μ` dropping by at least 2 per side), after
which the residue is exactly the β-redex pairs whose argument pair is a lambda pair
(`ArgLamFront`, equivalent to `TypeFront`).

## 7. Log

* Read the brief, the predecessor's `STRENGTHENING_ATTEMPT_2026-10-09{,b}.md`, logs A, B, B2,
  B3, C, E, F, Astra reviews 5 to 7 and round 4/7 answers, the predecessor's `Kripke.lean`,
  `Cancel.lean`, `TermModel.lean`, `TypingFront.lean`, `Final.lean`, and the model files
  (`Obs.lean`, `Interp.lean`, `Classes.lean`, `Sound.lean`, `EnvValid.lean`, `Separation.lean`).
  Agreed the split with agent A (A: `Cancel`, `TypingFront`, `Closures`, confluence descent;
  B: `Model*`).
* 45e1cbb5 `Model.lean`; f9c41403 `ModelObstruction.lean`; merged A's d112421a (061942a5);
  2cbd1dd5 `TypedReflection` refuted, `ModelBridge.lean`; aa42a92a `InhabitedProp.lean`;
  11b9c05c `HeteroSubst.lean`; merged A's 5a45e672 (`NormalDescent.lean`: `NormalEqS.descend`,
  `StrictJoinRepair`, `typedFront_of_strictJoinRepair`); `ProofErasedSize.lean`.
  Each pushed to `kim-em/agent/iota-strengthB` after a green build of the module.
* Messages to A: the split; the push SHAs; the `(μ, n)` descent analysis with the proof-argument
  β-pair closed by contraction and the lambda-argument β-pair as the residue; the equivalence
  `InhabitedPropFront ↔ PropFront` (A had conjectured a genuine weakening and retracted it).
  A reached the same two-mode dispatch independently and is mechanising
  `NormalEqN.descend_betaNormal` (descent of a normal equality between lifts free of head
  β-redexes, no environment hypothesis) and the residual `HeadRedexDomainFront`.
