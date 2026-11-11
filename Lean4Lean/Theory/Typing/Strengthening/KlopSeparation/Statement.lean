import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.MinimalEnv

/-! # Given a universe tower, strengthening of definitional equality is false

Target of this directory: `not_weakN_iff_of_tower`, the negation of the statement of
`IsDefEqU.weakN_iff` from a set-theoretic universe tower (`UniverseTower`: a well-founded
extensional membership structure with separation and replacement for arbitrary Lean
predicates and functions, and a Grothendieck universe for every natural number).

The proof is assembled here from the machine-checked half of the Klop example
(`KlopEnv.above`, `KlopEnv.not_strengthening`), the minimal environment
(`exists_minimalKlopEnv`, proved in `MinimalEnv.lean`: canonical `Eq` installed as a
hand-built inductive declaration, then the six declarations, with an exact inventory), and
one obligation that is **not yet proved**, a named theorem with `sorry`:

* `KlopInventory.separated`: in an environment with that inventory, `[] ⊢ C E ≡ E` is not
  derivable, by the model of `FIRST_PRINCIPLES.md` §22 to §27 built in the tower.

Nothing outside this directory depends on these files.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

/-- A set-theoretic universe tower: a model of second-order set theory (extensionality,
foundation, pairing, union, power set, infinity, separation and replacement for arbitrary
Lean predicates and functions) with a Grothendieck universe `U n` for every `n`, each a
member of the next. Such a structure exists in ZFC with countably many inaccessible
cardinals; Lean cannot construct one for all `n` at once, which is why it is a hypothesis. -/
structure UniverseTower where
  /-- The sets. -/
  S : Type
  mem : S → S → Prop
  ext : ∀ x y, (∀ z, mem z x ↔ mem z y) → x = y
  wf : WellFounded mem
  empty : S
  mem_empty : ∀ z, ¬ mem z empty
  pair : S → S → S
  mem_pair : ∀ x y z, mem z (pair x y) ↔ z = x ∨ z = y
  sUnion : S → S
  mem_sUnion : ∀ x z, mem z (sUnion x) ↔ ∃ y, mem y x ∧ mem z y
  powerset : S → S
  mem_powerset : ∀ x z, mem z (powerset x) ↔ ∀ w, mem w z → mem w x
  sep : S → (S → Prop) → S
  mem_sep : ∀ x p z, mem z (sep x p) ↔ mem z x ∧ p z
  image : S → (S → S) → S
  mem_image : ∀ x f z, mem z (image x f) ↔ ∃ w, mem w x ∧ z = f w
  omega : S
  empty_mem_omega : mem empty omega
  succ_mem_omega : ∀ x, mem x omega → mem (sUnion (pair x (pair x x))) omega
  /-- The universes. -/
  U : Nat → S
  U_trans : ∀ n x y, mem x (U n) → mem y x → mem y (U n)
  U_pair : ∀ n x y, mem x (U n) → mem y (U n) → mem (pair x y) (U n)
  U_sUnion : ∀ n x, mem x (U n) → mem (sUnion x) (U n)
  U_powerset : ∀ n x, mem x (U n) → mem (powerset x) (U n)
  U_image : ∀ n x f, mem x (U n) → (∀ w, mem w x → mem (f w) (U n)) → mem (image x f) (U n)
  omega_mem_U : mem omega (U 0)
  U_mem_U : ∀ n, mem (U n) (U (n + 1))

/-- **Open obligation.** In an environment with the Klop inventory, `C E ≡ E` is not
derivable in the empty context, given a universe tower.

Missing: the model of `FIRST_PRINCIPLES.md` §28 with the amendments of §29, built in the
tower: untyped proof values with tokens `r`, `⊥` and candidates (sets of values closed under
weak head reduction and expansion, containing `⊥` when non-empty); a proposition denotes its
candidate; `T = ℤ/3` with the total coarse relation, `C = (+1)`, `P = ∅`; `Eq.rec` a function
of its endpoints; the substitution and weakening lemmas; and the soundness induction over
every rule of `IsDefEq` with the head invariant. Then `⟦C E⟧ = 1 ≠ 0 = ⟦E⟧`. -/
theorem KlopInventory.separated (tower : UniverseTower) {env : VEnv}
    (henv : env.WF) (heq : env.HasCanonicalEq) (K : KlopInventory env) :
    K.toKlopEnv.Separated 0 := by
  sorry

/-- **Given a universe tower, the statement of `IsDefEqU.weakN_iff` is false.**
Depends on the open obligation `KlopInventory.separated`. -/
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
