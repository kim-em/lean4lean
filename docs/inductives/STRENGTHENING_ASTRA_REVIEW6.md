**B is equivalent to `Cancel`, checked in Lean. A’s universal rank obstruction is not established. C’s rigid-`Q` restriction does not justify the proposed induction or the two-base regress argument.**

I wrote only [round8/design_check/Round8.lean](/home/kim/worktrees/lean4lean/strengthening-context/round8/design_check/Round8.lean). It compiles with the requested `lake env lean` command. All exact statements, definitions, and proofs are there; the [axiom audit](/home/kim/worktrees/lean4lean/strengthening-context/round8/design_check/lean-check.log) contains no `sorryAx` or new axioms. The repository is untouched.

**A. No universal obstruction—and no justified terminating rank yet.**

I cannot exhibit the requested pair, but I also cannot assert that no such pair exists or supply a terminating rank. Those conclusions do not follow from the previous rank tests.

There are three quantifier problems with the proposed test:

- “Every composition” needs a specified calculus of composition procedures and recursive calls. `Pilot.lean` defines certificates, not such procedures.
- Well-founded recursion ordinarily requires the **recursive call’s complete argument tuple** to decrease. Requiring its cut to be below **both individual input certificates** is stronger.
- The round-7 phase obstruction concerns a particular dependency order. The same file explicitly supplies decreasing occurrence-dependent stages for its example, while disclaiming a substitution bound. See [Round7:259](/home/kim/worktrees/lean4lean/strengthening-context/round7/proof_aware/Round7.lean:259) and [Round7:269](/home/kim/worktrees/lean4lean/strengthening-context/round7/proof_aware/Round7.lean:269).

There is also an implementation issue: [`Cert` is `Prop`-valued](/home/kim/worktrees/lean4lean/lean4lean-strength3/Lean4Lean/Theory/Typing/Strengthening/Pilot.lean:45). I checked:

```lean
theorem proof_rank_constant {k : CKind} {a b : VExpr}
    (rank : Cert env U k Γ a b → Nat)
    (d₁ d₂ : Cert env U k Γ a b) :
    rank d₁ = rank d₂
```

Thus certificate-size/depth ranks need reified derivations or explicit size/depth indices; a function on the present proof objects cannot distinguish their representations. [Checked statement](/home/kim/worktrees/lean4lean/strengthening-context/round8/design_check/Round8.lean:246).

For a concrete pilot test, let

```text
I = λ x : Prop. x
F = (λ z : Type. I) Prop
E(e) = λ x : Prop. e x
```

I checked both synthesis certificates and the complete peak:

```lean
theorem pilot_eta_beta_peak :
    CStep env U Γ pilotBeta (expand (.sort .zero) pilotBeta) ∧
    CStep env U Γ pilotBeta pilotId ∧
    CStep env U Γ (expand (.sort .zero) pilotBeta)
      (expand (.sort .zero) pilotId) ∧
    CStep env U Γ pilotId (expand (.sort .zero) pilotId)
```

Both residuals are single certified steps. This example is **not** a global termination argument; it prevents treating beta/eta overlap itself as an unavoidable rank failure. [Definitions and checks](/home/kim/worktrees/lean4lean/strengthening-context/round8/design_check/Round8.lean:218).

**Common-type indexing does help the local eta diagram.** With a fixed `Π A B`, subject reduction retains that type, so both branches expand using `A`. I checked:

```lean
theorem fixed_type_eta_peak
    (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hf : Params.env.HasType univs Γ f (.forallE A B))
    (hs : FullStep Γ f g) :
    FullStep Γ g (.lam A (.app g.lift (.bvar 0))) ∧
    FullStep Γ (.lam A (.app f.lift (.bvar 0)))
      (.lam A (.app g.lift (.bvar 0)))
```

This is a **declarative `FullStep` result**, not certified subject reduction. [Proof](/home/kim/worktrees/lean4lean/strengthening-context/round8/design_check/Round8.lean:204).

In the pilot, eta specifically demands synthesis plus exposure, rather than arbitrary typing at the common type. [Pilot:70](/home/kim/worktrees/lean4lean/lean4lean-strength3/Lean4Lean/Theory/Typing/Strengthening/Pilot.lean:70). Merely adding `: T` to conversion does not produce those certificates for the reduct. Allowing arbitrary declarative typing instead loses the structural support discipline.

My recommendation is to require A to specify the mutual obligations and recursive-call relation before selecting a rank. Include context transport: lambda normal equality compares bodies under the **left** domain, so even symmetry needs more than swapping witnesses. [Pilot:82](/home/kim/worktrees/lean4lean/lean4lean-strength3/Lean4Lean/Theory/Typing/Strengthening/Pilot.lean:82). The K-based depth argument in [plan:66](/home/kim/worktrees/lean4lean/lean4lean-strength3/docs/inductives/STRENGTHENING_ATTEMPT_2026-10-09b.md:66) does not establish failure for this pilot.

**B. The proposed stepping stone is the whole theorem under canonical `Eq`.**

The exact checked definition and equivalence are:

```lean
def UninhabitedTypingFront (env : VEnv) : Prop :=
  ∀ ⦃U Γ Q e A⦄, OnCtx (Q :: Γ) (env.IsType U) →
    (∀ q, ¬ env.HasType U Γ q Q) →
    env.HasType U (Q :: Γ) e.lift A →
    ∃ B, env.HasType U Γ e B

theorem uninhabitedTypingFront_iff_cancel
    (henv : env.WF) (heq : env.HasCanonicalEq) :
    UninhabitedTypingFront env ↔ Cancel env
```

[Definition](/home/kim/worktrees/lean4lean/strengthening-context/round8/design_check/Round8.lean:14), [equivalence](/home/kim/worktrees/lean4lean/strengthening-context/round8/design_check/Round8.lean:94).

The argument is short:

1. Handle inhabited `Q` by substitution, obtaining unrestricted existential typing descent.
2. Encode an annotation as `ascribe e A := (λ x : A. x) e`. Typability of this expression **at any type** implies `e : A`, by application/lambda inversion and Π-injectivity. Thus existential typing descent implies fixed-type typing descent. [Checks](/home/kim/worktrees/lean4lean/strengthening-context/round8/design_check/Round8.lean:29).
3. Given `a↑ ≡ b↑`, descend a typing of `a`, obtaining `a : A` below. Above, check `Eq.refl a↑` at `Eq A↑ a↑ b↑`.
4. Descend that fixed typing. Below, `Eq.refl a` also has its ordinary type `Eq A a a`. Unique typing and rigid-head injectivity yield `a ≡ b`.

I also proved that canonical `Eq` is rigid from the installed canonical recursor rule; no additional rigidity assumption was smuggled in. [Check](/home/kim/worktrees/lean4lean/strengthening-context/round8/design_check/Round8.lean:51), using the repository’s [constructor-result rigidity theorem](/home/kim/worktrees/lean4lean/lean4lean-strength3/Lean4Lean/Theory/Typing/ConstructorRigidity.lean:600).

Consequently, the expectation at [plan:100](/home/kim/worktrees/lean4lean/lean4lean-strength3/docs/inductives/STRENGTHENING_ATTEMPT_2026-10-09b.md:100) is incorrect: **join repair is not an additional obligation after proving this typing front.**

For head exposure, distinguish two statements:

- **Descent preserving the given Π endpoint:** false.
- **Existence of some Π exposure below:** I have neither proved nor refuted it. It is recorded explicitly as an [open proposition](/home/kim/worktrees/lean4lean/strengthening-context/round8/design_check/Round8.lean:307), not a theorem.

The checked counterexample to the first statement uses

```text
Dq = (λ z : Q↑. Prop) q
Iq = λ x : Dq. I x
T  = Π x : ((λ f : Prop → Prop. Prop) I). Prop
S  = (λ X : Type. X) T
```

`S` is typed below. Above, eta-expand `I` to `Iq` inside the argument, then contract the outer beta redex. The resulting Π contains `q` in its domain:

```lean
theorem headSource_typed :
    Params.env.HasType univs Γ headSource (.sort (.succ .zero))

theorem headSource_bad_path :
    FullReduction (Q :: Γ) headSource.lift (headTypeBad Q)

theorem headType_bad_reduct :
    FullStep (Q :: Γ) headType.lift (headTypeBad Q) ∧
    ¬ (headTypeBad Q).Skips 1 0
```

[Checks](/home/kim/worktrees/lean4lean/strengthening-context/round8/design_check/Round8.lean:180). This works for arbitrary `Q`; imposing uninhabitedness does not repair the invariant. The example also has a good exposure below, so it does **not** refute existential exposure.

Induction on path length fails precisely when descending a step’s guard:

- Its typing derivation is not a shorter head-reduction path.
- Even a subterm of a reduct need not be a smaller subterm of the original term.
- The claimed premise shape does not hold for `FullReduction`: eta chooses a typing annotation; unfolding includes typing of the whole source, generated captures, and an equality alignment guard. [FullStep:47](/home/kim/worktrees/lean4lean/lean4lean-strength3/Lean4Lean/Theory/Typing/FullReduction.lean:47), [UnfoldingCheck:25](/home/kim/worktrees/lean4lean/lean4lean-strength3/Lean4Lean/Theory/Typing/PrefixUnfolding/Rule.lean:25).

Even granting existential Π exposure, the application case still needs the descended argument’s type to agree with the exposed domain. Head shape alone supplies no such conversion. The checked `ascribe_inv` makes this obligation explicit.

**C. Rigidity excludes operations on bare `q`, not dependence on `q`.**

The round-7 exclusion lemma establishes the useful local fact that an inhabitant of an opaque non-structure `Type` cannot also be a function, proof, or structure inhabitant. [TermModel:388](/home/kim/worktrees/lean4lean/strengthening-context/round7/term-model/TermModel.lean:388). I checked the bare-variable non-proof conclusion for arbitrary `u` with `¬ u ≈ 0`. [Round8:123](/home/kim/worktrees/lean4lean/strengthening-context/round8/design_check/Round8.lean:123).

But with `f : Q → P` and `h : P` below, where `P : Prop`, proof irrelevance applies to **`f q`**:

```lean
theorem derived_proof_irrel (henv : env.Ordered)
    (hP : env.HasType U Γ P (.sort .zero))
    (hf : env.HasType U Γ f (.forallE Q P.lift))
    (hh : env.HasType U Γ h P) :
    env.IsDefEq U (Q :: Γ)
      (.app f.lift (.bvar 0)) h.lift P.lift
```

The left expression mentions `q`; the right does not. This requires neither that `q` itself be a proof nor a `q`-free inhabitant of `Q` above. [Checked equation and support failure](/home/kim/worktrees/lean4lean/strengthening-context/round8/design_check/Round8.lean:110).

Likewise, the eta example above works for rigid `Q`:

```lean
theorem arbitrary_Q_eta :
    FullStep (Q :: Γ) StrengtheningObstructions.idProp.lift (badEta Q) ∧
    ¬ (badEta Q).Skips 1 0
```

It also has a checked supported repair. [Counterexample](/home/kim/worktrees/lean4lean/strengthening-context/round8/design_check/Round8.lean:143), [repair](/home/kim/worktrees/lean4lean/strengthening-context/round8/design_check/Round8.lean:199).

These refute the proposed **induction invariants**, not rigid-`Q` `Cancel`. I do not have a proof or counterexample for that partial theorem. Direct equality induction still encounters arbitrary intermediates at `trans`, and reduction induction still encounters the guard problem. [`IsDefEq.trans`](/home/kim/worktrees/lean4lean/lean4lean-strength3/Lean4Lean/Theory/Typing/Basic.lean:21).

Therefore the two-base regress classification at [plan:70](/home/kim/worktrees/lean4lean/lean4lean-strength3/docs/inductives/STRENGTHENING_ATTEMPT_2026-10-09b.md:70) is not exhaustive **as stated**. Derived proofs such as `f q`, beta-erased occurrences, and q-dependent eta annotations need treatment. None of my examples is a new counterexample to `Cancel`.

The provably complete search target is broader than “a gap at `Q↑`.” I checked:

```lean
theorem not_cancel_iff_typing_gap
    (henv : env.WF) (heq : env.HasCanonicalEq) :
    ¬ Cancel env ↔
      ∃ (U : Nat) (Γ : List VExpr) (Q e A : VExpr),
        OnCtx (Q :: Γ) (env.IsType U) ∧
        (∀ q, ¬ env.HasType U Γ q Q) ∧
        env.HasType U (Q :: Γ) e.lift A ∧
        ∀ B, ¬ env.HasType U Γ e B
```

[Proof](/home/kim/worktrees/lean4lean/strengthening-context/round8/design_check/Round8.lean:289). Restricting `A` to `Q.lift` requires another theorem.

Finally, the universe condition needs precision: I checked `¬ (param 0 ≈ 0)` together with `¬ (param 0).IsNeverZero`. [Check](/home/kim/worktrees/lean4lean/strengthening-context/round8/design_check/Round8.lean:250). Non-equivalence to zero is not positivity at every specialization, which is what [`IsNeverZero`](/home/kim/worktrees/lean4lean/lean4lean-strength3/Lean4Lean/Theory/VLevel.lean:113) means.
