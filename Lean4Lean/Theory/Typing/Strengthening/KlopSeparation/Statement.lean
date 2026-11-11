import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.MinimalEnv
import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.Interp

/-! # Given a universe tower, strengthening of definitional equality is false

Target of this directory: `not_weakN_iff_of_tower`, the negation of the statement of
`IsDefEqU.weakN_iff` from a set-theoretic universe tower (`UniverseTower`, in `Tower.lean`:
an applicative set theory with dependent products, separation, pairing, an embedding of small
Lean types, and a universe closed under these for every natural number).

The proof is assembled here from the machine-checked half of the Klop example
(`KlopEnv.above`, `KlopEnv.not_strengthening`), the minimal environment
(`exists_minimalKlopEnv`, proved in `MinimalEnv.lean`: canonical `Eq` installed as a
hand-built inductive declaration, then the six declarations, with an exact inventory), and
the interpretation of terms in the tower (`Interp.lean`, where `⟦C E⟧ = 1` and `⟦E⟧ = 0` is
proved), and one obligation that is **not yet proved**, a named theorem with `sorry`:

* `KlopInventory.den_sound`: in an environment with that inventory, definitionally equal
  closed terms have equal denotations (the model of `FIRST_PRINCIPLES.md` §28, §29).

Nothing outside this directory depends on these files.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

/-- **Open obligation: soundness of the model.** In an environment with the Klop inventory,
definitionally equal closed terms have the same denotation in the model built in a universe
tower (`UniverseTower.den`, `Interp.lean`).

Missing: the lemmas about semantic types (the coarse relation is a partial equivalence,
coarsely related types have the same elements, data types are inhabited, universe
membership); substitution and weakening for `den`; and the induction over every rule of
`IsDefEq` for the full statement of `FIRST_PRINCIPLES.md` §28, §29 (denotations are equal
elements of the denotation of the type, values of proofs realize their propositions,
coarse relatedness, and the head invariant on application spines), with the projection rules
vacuous by the inventory. -/
theorem KlopInventory.den_sound (𝕋 : UniverseTower) {env : VEnv}
    (henv : env.WF) (heq : env.HasCanonicalEq) (K : KlopInventory env)
    {a b A : VExpr} (H : env.IsDefEq 0 [] a b A) (ρ : Nat → 𝕋.S) :
    𝕋.den ρ a = 𝕋.den ρ b := by
  sorry

/-- In an environment with the Klop inventory, `C E ≡ E` is not derivable in the empty
context, given a universe tower: the two terms denote `1` and `0`. Depends on
`KlopInventory.den_sound`. -/
theorem KlopInventory.separated (tower : UniverseTower) {env : VEnv}
    (henv : env.WF) (heq : env.HasCanonicalEq) (K : KlopInventory env) :
    K.toKlopEnv.Separated 0 := by
  rintro ⟨A, H⟩
  exact tower.den_CE_ne_E (fun _ => tower.star) (K.den_sound tower henv heq H _)

/-- **Given a universe tower, the statement of `IsDefEqU.weakN_iff` is false.**
Depends on the open obligation `KlopInventory.den_sound`. -/
theorem not_weakN_iff_of_tower (tower : UniverseTower) :
    ¬ ∀ {env : VEnv} {U n k : Nat} {Γ Γ' : List VExpr} {e1 e2 : VExpr},
      env.WF → OnCtx Γ' (env.IsType U) → Ctx.LiftN n k Γ Γ' →
      (env.IsDefEqU U Γ' (e1.liftN n k) (e2.liftN n k) ↔ env.IsDefEqU U Γ e1 e2) := by
  intro H
  obtain ⟨env, henv, heq, K⟩ := exists_minimalKlopEnv
  exact K.toKlopEnv.not_strengthening henv heq (K.separated tower henv heq)
    (fun hΓ W => H henv hΓ W)

end VEnv.Strengthening
end Lean4Lean
