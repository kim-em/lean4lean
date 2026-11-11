import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.DenSubst
import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.Univ
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

/-- A valuation of a context: the type of every variable denotes a semantic type, the
variable denotes an element of it, and its value realizes it when it is a proposition. -/
def ValOK (Γ : List VExpr) (ρ : Nat → 𝕋.S) (w : Nat → PVal) : Prop :=
  ∀ i A, Lookup Γ i A →
    𝕋.IsSemTy (𝕋.den ρ A) ∧
    𝕋.mem (ρ i) (𝕋.El (𝕋.den ρ A)) ∧
    (𝕋.IsCand (𝕋.den ρ A) → (𝕋.candOf (𝕋.den ρ A)).mem (w i))

/-- Two valuations of a context are coarsely related pointwise. -/
def CoRel (Γ : List VExpr) (ρ ρ' : Nat → 𝕋.S) : Prop :=
  ∀ i A, Lookup Γ i A →
    𝕋.TyRel (𝕋.den ρ A) (𝕋.den ρ' A) ∧ 𝕋.Rel (𝕋.den ρ A) (ρ i) (ρ' i)

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

variable {𝕋}

/-- The variable rule. -/
theorem sem_bvar {Γ : List VExpr} {i : Nat} {A : VExpr} (h : Lookup Γ i A) :
    𝕋.Sem Γ (.bvar i) (.bvar i) A := by
  intro ρ w hρ
  obtain ⟨hty, hmem, hval⟩ := hρ i A h
  exact ⟨hty, rfl, hmem, fun hc => ⟨hval hc, hval hc⟩, fun ρ' w' _ hrel => hrel i A h⟩

/-- Symmetry. -/
theorem Sem.symm {Γ : List VExpr} {a b A : VExpr} (H : 𝕋.Sem Γ a b A) : 𝕋.Sem Γ b a A := by
  intro ρ w hρ
  obtain ⟨hty, heq, hmem, hval, hrel⟩ := H ρ w hρ
  refine ⟨hty, heq.symm, heq ▸ hmem, fun hc => ⟨(hval hc).2, (hval hc).1⟩, fun ρ' w' hρ' hr => ?_⟩
  obtain ⟨-, heq', -⟩ := H ρ' w' hρ'
  obtain ⟨h1, h2⟩ := hrel ρ' w' hρ' hr
  exact ⟨h1, heq ▸ heq' ▸ h2⟩

/-- Transitivity. -/
theorem Sem.trans {Γ : List VExpr} {a b c A : VExpr} (H1 : 𝕋.Sem Γ a b A)
    (H2 : 𝕋.Sem Γ b c A) : 𝕋.Sem Γ a c A := by
  intro ρ w hρ
  obtain ⟨hty, heq, hmem, hval, hrel⟩ := H1 ρ w hρ
  obtain ⟨-, heq2, -, hval2, -⟩ := H2 ρ w hρ
  exact ⟨hty, heq.trans heq2, hmem, fun hc => ⟨(hval hc).1, (hval2 hc).2⟩, hrel⟩

/-- `𝒰ₙ` is a semantic type. -/
theorem isSemTy_univ (n : Nat) : 𝕋.IsSemTy (𝕋.univ n) :=
  ⟨n + 1, .univ (univ_mem_univList n)⟩

/-- The sort rule. -/
theorem sem_sort {Γ : List VExpr} {l l' : VLevel} (h : l ≈ l') :
    𝕋.Sem Γ (.sort l) (.sort l') (.sort (.succ l)) := by
  intro ρ w _
  have hm : 𝕋.mem (𝕋.sortDen l) (𝕋.El (𝕋.univ (l.eval []))) := sortDen_mem l
  refine ⟨isSemTy_univ _, sortDen_congr h, hm,
    fun hc => (not_isCand_univ _ hc).elim, fun ρ' w' _ _ => ⟨rfl, rel_univ_refl hm⟩⟩

/-- Conversion: the stated type may be replaced by a type with the same denotation. -/
theorem Sem.defeq {Γ : List VExpr} {a b A B S : VExpr} (HT : 𝕋.Sem Γ A B S)
    (H : 𝕋.Sem Γ a b A) : 𝕋.Sem Γ a b B := by
  intro ρ w hρ
  obtain ⟨-, hAB, -⟩ := HT ρ w hρ
  have h := H ρ w hρ
  rw [hAB] at h
  obtain ⟨hty, heq, hmem, hval, hrel⟩ := h
  refine ⟨hty, heq, hmem, hval, fun ρ' w' hρ' hr => ?_⟩
  obtain ⟨-, hAB', -⟩ := HT ρ' w' hρ'
  have := hrel ρ' w' hρ' hr
  rwa [hAB'] at this

end UniverseTower

/-- **Open obligation: the fundamental theorem of the model.** In an environment with the
Klop inventory, every derivable judgment (at universe-parameter count `0`) satisfies the
semantic judgment. The induction is over the strong judgment `IsDefEqStrong`, whose rules
carry the typing premises the semantic argument needs (for instance the type of an
application is a type), and every derivation has a strong form (`IsDefEq.strong`).

Missing: the lemmas about semantic types (the coarse relation is a partial equivalence,
coarsely related types have the same elements, data types are inhabited, universe
membership, validity of `mkPi`); the commutation of `pval` and `PVal.subst` with
instantiation; and the induction over the rules of `IsDefEq`. `Sem` has to be strengthened
with the head invariant on application spines (`FIRST_PRINCIPLES.md` §26) for the `pat` case
of `Eq.rec` over `T`, and the projection rules are to be shown vacuous from the inventory
(`eqProjInfo` has one index and no field; no side of a derivable judgment is a `.proj`). -/
theorem KlopInventory.sound (𝕋 : UniverseTower) {env : VEnv}
    (henv : env.WF) (heq : env.HasCanonicalEq) (K : KlopInventory env)
    {Γ : List VExpr} {a b A : VExpr} (H : env.IsDefEqStrong 0 Γ a b A) : 𝕋.Sem Γ a b A := by
  sorry

/-- Definitionally equal closed terms have equal denotations. Depends on
`KlopInventory.sound`. -/
theorem KlopInventory.den_sound (𝕋 : UniverseTower) {env : VEnv}
    (henv : env.WF) (heq : env.HasCanonicalEq) (K : KlopInventory env)
    {a b A : VExpr} (H : env.IsDefEq 0 [] a b A) (ρ : Nat → 𝕋.S) :
    𝕋.den ρ a = 𝕋.den ρ b :=
  (K.sound 𝕋 henv heq (H.strong henv.orderedStrong (Γ := []) trivial) ρ (fun _ => .bot)
    (𝕋.valOK_nil ρ _)).2.1

end VEnv.Strengthening
end Lean4Lean
