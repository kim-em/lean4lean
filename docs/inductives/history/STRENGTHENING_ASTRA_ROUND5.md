**I did not complete the requested substitution-aware rank or step (4). `Cert.trans` and `Cancel` remain unproved.** I obtained a checked obstruction to a narrower, current-binder-depth rank, plus weakening for the entire pilot.

The new development imports the actual `Pilot.lean`:

- [Round5.lean](/home/kim/worktrees/lean4lean/strengthening-context/round5/Round5.lean)
- [Report with verbatim definitions and explicit limitations](/home/kim/worktrees/lean4lean/strengthening-context/round5/REPORT.txt)
- [All 43 `#print axioms` results](/home/kim/worktrees/lean4lean/strengthening-context/round5/axioms.txt)

This command succeeds from the mainline worktree, with no warnings or `sorryAx`:

```bash
lake env lean /home/kim/worktrees/lean4lean/strengthening-context/round5/Round5.lean
```

The repository itself is unchanged.

The status against your four requests is:

| Request | Checked result |
|---|---|
| Rank covering the pilot’s hidden certificates | **Not achieved.** The constructed rank measures syntactic beta cuts, not every hidden conversion premise. |
| Weakening and substitution bounds | Full pilot weakening proved. Explicit **expression-substitution** bounds proved; ranked certified substitution remains unproved. |
| Both previous examples decrease | **Proved**, for both the lexicographic rank and multiset replacement order. Actual pilot `CStep` witnesses supplied. |
| Transitivity or exact composition obstruction | **Neither achieved.** The new obstruction concerns beta contraction, not composition of two conversion certificates. |

The new obstruction is **argument duplication beneath a binder**. Write
```text
a = (λ x : Type. x) Prop
```
Then
```text
(λ X : Type. X → X) a  →β  a → a
```
has these beta-cut profiles, recording `(current binder depth, binder-type size)`:

```text
source:     [(0, 1), (0, 1)]
contractum: [(0, 1), (1, 1)]
```

The argument’s second copy moves beneath the Pi binder. Thus the contractum introduces a cut strictly above every source cut in the depth-first order. `multiset_duplication_failure` checks that **the contractum profile is not smaller by multiset replacement**. This failure persists when all cuts are retained; it is not an artifact of taking their maximum.

`duplication_pilot` supplies actual `CTy` certificates for both endpoints at
```lean
.sort (.imax (.succ .zero) (.succ .zero))
```
and an actual `CConv` certificate for the contraction, in every well-formed environment.

Here are the multiset definitions verbatim:

```lean
abbrev Label := Nat × Nat
def LabelLT : Label → Label → Prop := Prod.Lex (· < ·) (· < ·)
def profile (d : Nat) : VExpr → List Label
  | .app (.lam A b) a => (d, nodes A) ::
      (profile d A ++ profile (d+1) b ++ profile d a)
  | .app f a => profile d f ++ profile d a
  | .lam A b | .forallE A b => profile d A ++ profile (d+1) b
  | .proj _ _ e => profile d e
  | _ => []

/-- Standard strict multiset replacement, represented by lists modulo permutation. -/
def MultiLT (xs ys : List Label) : Prop :=
  ∃ keep removed added, ys.Perm (keep ++ removed) ∧ xs.Perm (keep ++ added) ∧
    removed ≠ [] ∧ ∀ x ∈ added, ∃ y ∈ removed, LabelLT x y
```

Here `nodes` is exactly:

```lean
def nodes : VExpr → Nat
  | .app a b | .lam a b | .forallE a b => nodes a + nodes b + 1
  | .proj _ _ e => nodes e + 1
  | _ => 1
```

**The type label above is the beta binder type. It is not the common comparison type requested in your proposed rank.** The pilot’s conversion judgment does not contain that type. I did not construct the additional indexed annotation needed to supply it and count every hidden premise.

The separately checked well-founded rank is:

```lean
abbrev Rank := Nat × (Nat × Nat)
def LT : Rank → Rank → Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))
def rank (e : VExpr) : Rank :=
  (cutDepth e, cutTypeSize e, nodes e)
```

`cutDepth` counts one plus the maximum current binder depth of a beta redex; `cutTypeSize` takes the maximum beta binder-type size. Their complete definitions are reproduced verbatim in the [report](/home/kim/worktrees/lean4lean/strengthening-context/round5/REPORT.txt). Only this lexicographic rank’s well-foundedness is proved; I did not separately formalize well-foundedness of `MultiLT`.

Both old tests decrease:

```lean
twice_tower_decreases
nested_decreases
multiset_old_tests
```

The substitution budget and checked growth bound are:

```lean
def SubBudget (D S : Nat) (σ : Subst) : Prop :=
  1 ≤ S ∧ ∀ i, binders (σ i) ≤ D ∧ nodes (σ i) ≤ S

theorem rank_subst_bound (h : SubBudget D S σ) :
    (rank (e.subst σ)).1 ≤ binders e + D + 1 ∧
    (rank (e.subst σ)).2.1 ≤ nodes e * S ∧
    (rank (e.subst σ)).2.2 ≤ nodes e * S
```

This explicitly accounts for argument depth and size, but **it is a growth bound on expressions, not certified substitution or principal-cut decrease**.

Full weakening uses the actual pilot:

```lean
theorem pilot_weakN (henv : env.WF) (h : Cert env U j Γ a b)
    (W : Ctx.LiftN n k Γ Δ) :
    Cert env U j Δ (a.liftN n k) (b.liftN n k)
```

It covers every constructor, including closed equations, synthesized eta, and proof irrelevance. `pilot_weakN_rank` proves preservation of the endpoint rank.

I also checked `exact_synthesis_substitution_false`: substituting `∀ _:Prop, Prop` for a variable synthesized at `Type` produces synthesis at `Sort (imax 1 1)`, not syntactically `Type`. A certified conversion between those types exists. This confirms that substitution must return a **certified check**, rather than preserve the synthesis type literally; it does not refute the correct substitution theorem.

Selected axiom output:

| Theorem | Axioms |
|---|---|
| `rank_wf` | `[]` |
| `pilot_weakN`, `rank_subst_bound` | `[propext, Quot.sound]` |
| `multiset_old_tests`, `multiset_duplication_failure` | `[propext, Quot.sound]` |
| `duplication_pilot` | `[propext, Quot.sound]` |
| `exact_synthesis_substitution_false` | `[propext]` |
| `nested_decreases` | `[propext, Classical.choice, Quot.sound]` |

For this depth-first design, the input budget would need to count each argument copy **at its future occurrence depth**—depths zero and one for `twice`—and account for substituted cut types. Those repairs are necessary for this design, but I have not shown they control the output compositions in the diagram proof.

I therefore have **no checked composition obstruction satisfying your alternative (4)**, and no basis for extending a successful transitivity proof to prefix unfolding, projections, structure/unit eta, or quotient.
