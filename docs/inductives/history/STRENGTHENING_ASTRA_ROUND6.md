**The proposed subformula property is false for this pilot.** I checked counterexamples to it and to the claimed automatic rank decreases. `Cert.trans` and `Cancel` remain unproved.

All work is under `round6/`:

- [Checked Lean source](/home/kim/worktrees/lean4lean/strengthening-context/round6/Round6.lean)
- [Report containing all definitions verbatim and precise limitations](/home/kim/worktrees/lean4lean/strengthening-context/round6/REPORT.txt)
- [All 59 `#print axioms` results](/home/kim/worktrees/lean4lean/strengthening-context/round6/axioms.txt)
- [Compiler log](/home/kim/worktrees/lean4lean/strengthening-context/round6/check.log)

This command succeeds without warnings or errors:

```bash
lake env lean /home/kim/worktrees/lean4lean/strengthening-context/round6/Round6.lean
```

No repository source files were changed.

1. **The annotated rank is defined.** `DCert` reifies all 28 pilot constructors and erases to an actual `Cert`. Every conversion and beta-step node records its common type; the profile recursively counts hidden certificates beneath every constructor.

   The central definitions are verbatim:

   ```lean
   def complexity (ρ : List Nat) (u : VLevel) (T : VExpr) : Complexity :=
     (u.eval ρ, nodes T)

   abbrev Rank := Complexity × (List Complexity × Nat)

   def DCert.rank (ρ : List Nat) (h : DCert env U j Γ a b) : Rank :=
     (maxComplexity (h.cuts ρ), h.cuts ρ, h.size)
   ```

   Comparison uses maximum complexity, strict multiset replacement, then size. This is an annotated presentation: raw `Cert` is proof-irrelevant and does not carry common types. I have not proved every raw certificate admits annotations, or well-foundedness of the complete rank.

2. **Proof irrelevance refutes the requested subformula property.** In a well-formed context containing `P : Prop` and `h₀ h₁ : P`:

   | Comparison | Common type | Complexity |
   |---|---|---|
   | Enclosing `h₀ ~ h₁` | `P` | `(0, 1)` |
   | Hidden premise `P ~ P` | `Prop` | `(1, 1)` |

   `proofIrrel_subformula_false` proves the hidden complexity is **not ≤** the enclosing complexity. Taking whole-certificate maxima instead gives equal maxima, so `proofIrrel_principal_not_strict` also refutes the requested strict decrease.

   The round-5 synthesis correction likewise compares `Sort (imax 1 1)` and `Type` **at `Sort 2`**. Its common-type complexity is `(3,1)`, greater than `Type`’s `(2,1)` under this convention.

3. **The two older tests decrease; binder duplication does not automatically decrease.**

   `twice_tower_decreases` and `nested_decreases` hold for every `N`. For the displayed annotated typing certificates:

   | Duplication argument | Source rank | Contractum rank |
   |---|---|---|
   | `nested 1` | maximum `(3,1)`, two cuts, size `25` | identical |
   | `nested 2` | maximum `(3,1)`, three cuts, size `35` | maximum `(3,1)`, four cuts, size `45` |

   Actual pilot beta steps are checked. These results concern the displayed certificate transformation; they do not establish a lower bound for every alternative contractum certificate.

4. **Full rank-preserving weakening is proved. General ranked substitution is not.** `DCert.weakN_rank_eq` covers every constructor.

   `budget_does_not_imply_rank_nonincrease` supplies an actual substitution whose replacement has **no cuts** and synthesizes exactly the required type. Nevertheless, instantiating the dependent common type increases its complexity from `(1,1)` to `(1,3)`. This disproves nonincrease from that budget, not every possible substitution-aware growth bound.

5. **The literal composition lower-bound alternative is proved.** Take the certificates
   ```text
   h₀ ~ h₁
   h₁ ~ h₂
   ```
   for three distinct proof variables of the same fresh proposition. Both input maxima are `(1,1)`. `exact_pair_composition_lower_bound` proves that **every decorated composition** contains a cut of complexity at least `(1,1)`, allowing arbitrary reduction witnesses and common-type annotations.

   **A composition exists and has the same rank as either input.** Consequently, this satisfies the stated `≥` alternative but does not refute transitivity or an induction comparing against the combined inputs.

All 59 axiom reports exclude `sorryAx`. They use only `propext`, `Classical.choice`, and `Quot.sound`, or no axioms. The report records the full output verbatim.

There is no successful transitivity proof to extend to unfolding, projections, structure/unit eta, or quotient; those obligations remain unproved.
