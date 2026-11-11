import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.DenSubst
import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.MinimalEnv

/-! # Soundness of the Klop model: statement

The semantic judgment `Sem` that every derivable judgment of an environment with the Klop
inventory is to satisfy (`FIRST_PRINCIPLES.md` §28, §29), and the reduction of
`KlopInventory.den_sound` to it. The fundamental theorem `KlopInventory.sound` is the one
remaining open obligation of `not_weakN_iff_of_tower`.

The head invariant on application spines (§26) is not yet part of `Sem`; it has to be added
for the `pat` case, and is noted in the docstring of `KlopInventory.sound`.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

namespace PVal

/-- Lift a simultaneous substitution under a binder. -/
def up (σ : Nat → PVal) : Nat → PVal
  | 0 => .var 0
  | i + 1 => (σ i).liftN 1

/-- Simultaneous substitution of values for variables. -/
def subst : PVal → (Nat → PVal) → PVal
  | .var i, σ => σ i
  | .lam b, σ => .lam (b.subst (up σ))
  | .app f a, σ => .app (f.subst σ) (a.subst σ)
  | .r, _ => .r
  | .bot, _ => .bot
  | .case s u v, σ => .case (s.subst σ) (u.subst σ) (v.subst σ)

end PVal

namespace UniverseTower
variable (𝕋 : UniverseTower)

/-- A semantic type of some level: a good candidate or a valid data type. -/
def IsSemTy (x : 𝕋.S) : Prop := ∃ n, 𝕋.ValidAny (𝕋.univList n) x

/-- A valuation of a context: every variable denotes an element of the denotation of its
type, and its value realizes that type when it is a proposition. -/
def ValOK (Γ : List VExpr) (ρ : Nat → 𝕋.S) (w : Nat → PVal) : Prop :=
  ∀ i A, Lookup Γ i A →
    𝕋.mem (ρ i) (𝕋.El (𝕋.den ρ A)) ∧
    (𝕋.IsCand (𝕋.den ρ A) → (𝕋.candOf (𝕋.den ρ A)).mem (w i))

/-- Two valuations of a context are coarsely related pointwise. -/
def CoRel (Γ : List VExpr) (ρ ρ' : Nat → 𝕋.S) : Prop :=
  ∀ i A, Lookup Γ i A → 𝕋.Rel (𝕋.den ρ A) (ρ i) (ρ' i)

/-- **The semantic judgment.** At every valuation of the context: the type denotes a
semantic type; the two sides have the same denotation, an element of it; if the type is a
proposition, the values of both sides realize it; and denotations at coarsely related
valuations are coarsely related. -/
def Sem (Γ : List VExpr) (a b A : VExpr) : Prop :=
  ∀ ρ w, 𝕋.ValOK Γ ρ w →
    𝕋.IsSemTy (𝕋.den ρ A) ∧
    𝕋.den ρ a = 𝕋.den ρ b ∧
    𝕋.mem (𝕋.den ρ a) (𝕋.El (𝕋.den ρ A)) ∧
    (𝕋.IsCand (𝕋.den ρ A) →
      (𝕋.candOf (𝕋.den ρ A)).mem ((pval a).subst w) ∧
      (𝕋.candOf (𝕋.den ρ A)).mem ((pval b).subst w)) ∧
    ∀ ρ' w', 𝕋.ValOK Γ ρ' w' → 𝕋.CoRel Γ ρ ρ' →
      𝕋.TyRel (𝕋.den ρ A) (𝕋.den ρ' A) ∧ 𝕋.Rel (𝕋.den ρ A) (𝕋.den ρ a) (𝕋.den ρ' a)

theorem valOK_nil (ρ : Nat → 𝕋.S) (w : Nat → PVal) : 𝕋.ValOK [] ρ w := by
  intro i A h
  cases h

end UniverseTower

/-- **Open obligation: the fundamental theorem of the model.** In an environment with the
Klop inventory, every derivable judgment (at universe-parameter count `0`) satisfies the
semantic judgment.

Missing: the lemmas about semantic types (the coarse relation is a partial equivalence,
coarsely related types have the same elements, data types are inhabited, universe
membership, validity of `mkPi`); the commutation of `pval` and `PVal.subst` with
instantiation; and the induction over the rules of `IsDefEq`. `Sem` has to be strengthened
with the head invariant on application spines (`FIRST_PRINCIPLES.md` §26) for the `pat` case
of `Eq.rec` over `T`, and the projection rules are to be shown vacuous from the inventory
(`eqProjInfo` has one index and no field; no side of a derivable judgment is a `.proj`). -/
theorem KlopInventory.sound (𝕋 : UniverseTower) {env : VEnv}
    (henv : env.WF) (heq : env.HasCanonicalEq) (K : KlopInventory env)
    {Γ : List VExpr} {a b A : VExpr} (H : env.IsDefEq 0 Γ a b A) : 𝕋.Sem Γ a b A := by
  sorry

/-- Definitionally equal closed terms have equal denotations. Depends on
`KlopInventory.sound`. -/
theorem KlopInventory.den_sound (𝕋 : UniverseTower) {env : VEnv}
    (henv : env.WF) (heq : env.HasCanonicalEq) (K : KlopInventory env)
    {a b A : VExpr} (H : env.IsDefEq 0 [] a b A) (ρ : Nat → 𝕋.S) :
    𝕋.den ρ a = 𝕋.den ρ b :=
  (K.sound 𝕋 henv heq H ρ (fun _ => .bot) (𝕋.valOK_nil ρ _)).2.1

end VEnv.Strengthening
end Lean4Lean
