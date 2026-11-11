import Lean4Lean.Theory.Typing.Strengthening.KlopCounterexample

/-! # Given a universe tower, strengthening of definitional equality is false

Target of this directory: `not_weakN_iff_of_tower`, the negation of the statement of
`IsDefEqU.weakN_iff` from a set-theoretic universe tower (`UniverseTower`: a well-founded
extensional membership structure with separation and replacement for arbitrary Lean
predicates and functions, and a Grothendieck universe for every natural number).

The proof is assembled here from the machine-checked half of the Klop example
(`KlopEnv.above`, `KlopEnv.not_strengthening`) and two obligations that are **not yet
proved**; each is a named theorem with `sorry`:

* `exists_minimalKlopEnv`: the minimal environment exists (canonical `Eq` installed as an
  inductive declaration, then the six declarations), is well formed, and has the stated
  inventory;
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

/-- The inventory of the minimal Klop environment: besides the declarations of `KlopEnv`,
its constants are exactly `Eq`, `Eq.refl`, `Eq.rec` and the six Klop constants, its
definitional equations are exactly those of `C` and `Fix`, its only registered pattern is
the ι rule of `Eq.rec`, and its only projection metadata is that of `Eq` (one index, no
field). -/
structure KlopInventory (env : VEnv) : Prop extends KlopEnv env where
  constants_only : ∀ n ci, env.constants n = some ci →
    n = ``Eq ∨ n = ``Eq.refl ∨ n = ``Eq.rec ∨ n = `Klop.T ∨ n = `Klop.E ∨ n = `Klop.P ∨
    n = `Klop.H ∨ n = `Klop.C ∨ n = `Klop.Fix
  defeqs_only : ∀ df, env.defeqs df →
    df = ⟨0, klopC, klopCBody, .forallE klopT klopT⟩ ∨
    df = ⟨0, klopFix, klopFixBody, .forallE klopP klopT⟩
  pats_only : ∀ p r, env.pats p r → p = canonicalEqRecPattern
  projections_only : ∀ n info, env.projections n info →
    n = ``Eq ∧ info.nindices = 1 ∧ info.numFields = 0

/-- **Open obligation 1.** The minimal Klop environment exists.

Missing: a hand construction of the inductive declaration of `Eq` satisfying
`VInductDecl.WF` in the empty environment (the pattern of `Tests/InductiveTheory.lean`, for
a family with two parameters, one index and large elimination), its installation by
`VEnv.addInduct`, the read-off of `HasCanonicalEq` and of the inventory, and then the six
declarations as in `exists_klopEnv`. The repository's existing route to canonical `Eq` goes
through the checker verification, which depends on `IsDefEqU.weakN_iff`, and cannot be used
here. -/
theorem exists_minimalKlopEnv :
    ∃ env : VEnv, env.WF ∧ env.HasCanonicalEq ∧ KlopInventory env := by
  sorry

/-- **Open obligation 2.** In an environment with the Klop inventory, `C E ≡ E` is not
derivable in the empty context, given a universe tower.

Missing: the model of `FIRST_PRINCIPLES.md` §22 to §27 built in the tower (data
denotations with `Prop = {0, 1}`, `T = ℤ/3` with the total relation, `C = (+1)`; untyped
proof values with tokens `r`, `⊥`; realizer sets and codes), its substitution lemmas, and
the soundness induction over every rule of `IsDefEq` with the head invariant. Then
`⟦C E⟧ = 1 ≠ 0 = ⟦E⟧`. -/
theorem KlopInventory.separated (tower : UniverseTower) {env : VEnv}
    (henv : env.WF) (heq : env.HasCanonicalEq) (K : KlopInventory env) :
    K.toKlopEnv.Separated 0 := by
  sorry

/-- **Given a universe tower, the statement of `IsDefEqU.weakN_iff` is false.**
Depends on the two open obligations above. -/
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
