import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.SemType
import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.Translate

/-! # The interpretation of terms in the Klop model

Third layer of the model for `KlopInventory.separated` (`FIRST_PRINCIPLES.md` §28, §29):
valid semantic types by level, the universes, and the denotation `den ρ e` of a raw term at
a valuation `ρ : Nat → S` of its de Bruijn variables. Universe levels are evaluated at the
empty assignment (the theorem is proved at universe-parameter count `0`).

Definitions only. The lemmas (validity, substitution, weakening) and the soundness theorem
are still to be written.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace UniverseTower
variable (𝕋 : UniverseTower)

local infix:50 " ∈ₛ " => 𝕋.mem

/-- Valid semantic types, given the universes of lower level: good candidates and data
types. -/
inductive ValidAny (lower : List 𝕋.S) : 𝕋.S → Prop where
  | prop {c : Candidate} : c.Good → ValidAny lower (𝕋.cand c)
  | tT : ValidAny lower 𝕋.tT
  | tProp : ValidAny lower 𝕋.tProp
  | univ {u : 𝕋.S} : u ∈ lower → ValidAny lower u
  | pi {D : 𝕋.S} {F : 𝕋.S → 𝕋.S} : ValidAny lower D → ¬ 𝕋.IsCand D →
      (∀ d, 𝕋.mem d (𝕋.El D) → ValidAny lower (F d)) →
      (∀ d, 𝕋.mem d (𝕋.El D) → 𝕋.IsCand (F d) → F d = 𝕋.cand Candidate.full) →
      (∀ d d', 𝕋.mem d (𝕋.El D) → 𝕋.Rel D d d' → 𝕋.TyRel (F d) (F d')) →
      (¬ ∀ d, 𝕋.mem d (𝕋.El D) → 𝕋.IsCand (F d)) →
      ValidAny lower (𝕋.tPi D F)
  | piP {c : Candidate} {B : 𝕋.S} : c.Good → (∃ v, c.mem v) → ValidAny lower B →
      ¬ 𝕋.IsCand B → ValidAny lower (𝕋.tPiP c B)

/-- The members of a data universe: valid data types and the full candidate. -/
def ValidTy (lower : List 𝕋.S) (x : 𝕋.S) : Prop :=
  𝕋.ValidAny lower x ∧ (𝕋.IsCand x → x = 𝕋.cand Candidate.full)

/-- The universes below level `n`: `univList n = [𝒰₀, …, 𝒰ₙ₋₁]`. -/
noncomputable def univList : Nat → List 𝕋.S
  | 0 => []
  | n + 1 => univList n ++
      [𝕋.tU n (𝕋.sep (𝕋.U (n + 1)) (𝕋.ValidTy (univList n)))]

/-- The universe `𝒰ₙ`, the denotation of `Sort (n + 1)`. -/
noncomputable def univ (n : Nat) : 𝕋.S :=
  𝕋.tU n (𝕋.sep (𝕋.U (n + 1)) (𝕋.ValidTy (𝕋.univList n)))

/-- The denotation of `Sort ℓ` at the empty level assignment. -/
noncomputable def sortDen (l : VLevel) : 𝕋.S :=
  match l.eval [] with
  | 0 => 𝕋.tProp
  | n + 1 => 𝕋.univ n

/-- The candidate of `@Eq α a b`: `r` is allowed exactly when the endpoints are identical. -/
noncomputable def eqCand (α a b : 𝕋.S) : Candidate :=
  if a ∈ₛ 𝕋.El α ∧ a = b then Candidate.rOrBot
  else if a ∈ₛ 𝕋.El α ∧ 𝕋.Rel α a b then Candidate.botOnly
  else Candidate.empty

/-- The successor on the elements of `T`. -/
noncomputable def tsucc (x : 𝕋.S) : 𝕋.S :=
  if h : ∃ i : Fin 3, x = 𝕋.tval i then 𝕋.tval (h.choose + 1) else x

/-- `Eq.{u}` as a curried function. -/
noncomputable def eqDen (u : VLevel) : 𝕋.S :=
  𝕋.mkLam (𝕋.sortDen u) fun α => 𝕋.mkLam α fun a => 𝕋.mkLam α fun b => 𝕋.cand (𝕋.eqCand α a b)

/-- The motive type of `Eq.rec.{v, u}` at `α`, `a`. -/
noncomputable def motiveTy (v : VLevel) (α a : 𝕋.S) : 𝕋.S :=
  𝕋.mkPi α fun b => 𝕋.mkPi (𝕋.cand (𝕋.eqCand α a b)) fun _ => 𝕋.sortDen v

/-- The result of `Eq.rec` at data: a function of the endpoints only. -/
noncomputable def recBody (α a M m b : 𝕋.S) : 𝕋.S :=
  if 𝕋.IsCand (𝕋.mkApp (𝕋.mkApp M b) 𝕋.star) then 𝕋.star
  else if α = 𝕋.tT ∧ 𝕋.mkApp (𝕋.mkApp M b) 𝕋.star = 𝕋.tT ∧ a ≠ b then 𝕋.tsucc a
  else m

/-- `Eq.rec.{v, u}` as a curried function. -/
noncomputable def recDen (v u : VLevel) : 𝕋.S :=
  𝕋.mkLam (𝕋.sortDen u) fun α => 𝕋.mkLam α fun a =>
    𝕋.mkLam (𝕋.motiveTy v α a) fun M =>
      𝕋.mkLam (𝕋.mkApp (𝕋.mkApp M a) 𝕋.star) fun m =>
        𝕋.mkLam α fun b => 𝕋.mkLam (𝕋.cand (𝕋.eqCand α a b)) fun _ => 𝕋.recBody α a M m b

/-- The denotation of a constant of the minimal Klop environment. -/
noncomputable def constDen (c : Name) (ls : List VLevel) : 𝕋.S :=
  if c = ``Eq then 𝕋.eqDen (ls.getD 0 .zero)
  else if c = ``Eq.rec then 𝕋.recDen (ls.getD 0 .zero) (ls.getD 1 .zero)
  else if c = `Klop.T then 𝕋.tT
  else if c = `Klop.E then 𝕋.tval 0
  else if c = `Klop.P then 𝕋.cand Candidate.empty
  else if c = `Klop.C then 𝕋.mkLam 𝕋.tT 𝕋.tsucc
  else 𝕋.star

/-- Extend a valuation by a value for variable `0`. -/
def cons (d : 𝕋.S) (ρ : Nat → 𝕋.S) : Nat → 𝕋.S
  | 0 => d
  | i + 1 => ρ i

/-- **The denotation of a term** at a valuation of its variables. -/
noncomputable def den : (Nat → 𝕋.S) → VExpr → 𝕋.S
  | ρ, .bvar i => ρ i
  | _, .sort l => 𝕋.sortDen l
  | _, .const c ls => 𝕋.constDen c ls
  | ρ, .app f a => 𝕋.mkApp (den ρ f) (den ρ a)
  | _, .proj _ _ _ => 𝕋.star
  | ρ, .lam A b => 𝕋.mkLam (den ρ A) fun d => den (𝕋.cons d ρ) b
  | ρ, .forallE A B => 𝕋.mkPi (den ρ A) fun d => den (𝕋.cons d ρ) B

theorem tsucc_tval (i : Fin 3) : 𝕋.tsucc (𝕋.tval i) = 𝕋.tval (i + 1) := by
  have h : ∃ j : Fin 3, 𝕋.tval i = 𝕋.tval j := ⟨i, rfl⟩
  rw [tsucc, dif_pos h, ← 𝕋.tval_inj h.choose_spec]

theorem tsucc_ne (i : Fin 3) : 𝕋.tsucc (𝕋.tval i) ≠ 𝕋.tval i := by
  rw [tsucc_tval]
  intro h
  have key : ∀ j : Fin 3, j + 1 ≠ j := by decide
  exact key i (𝕋.tval_inj h)

theorem tval_ne_star (i : Fin 3) : 𝕋.tval i ≠ 𝕋.star := fun h => by
  have := 𝕋.tagN_inj (𝕋.pair_inj h).1
  omega

/-- `⟦C⟧` is the successor function on `T`. -/
theorem den_C_app (i : Fin 3) :
    𝕋.mkApp (𝕋.constDen `Klop.C []) (𝕋.tval i) = 𝕋.tval (i + 1) := by
  have hC : 𝕋.constDen `Klop.C [] = 𝕋.mkLam 𝕋.tT 𝕋.tsucc := by
    simp [constDen]
  rw [hC, 𝕋.mkApp_mkLam (𝕋.mem_El_tT.2 ⟨i, rfl⟩), tsucc_tval]

/-- **The two closed terms of the counterexample have different denotations**:
`⟦C E⟧ = 1` and `⟦E⟧ = 0`. -/
theorem den_CE_ne_E (ρ : Nat → 𝕋.S) :
    𝕋.den ρ (.app (.const `Klop.C []) (.const `Klop.E [])) ≠ 𝕋.den ρ (.const `Klop.E []) := by
  have hE : 𝕋.den ρ (.const `Klop.E []) = 𝕋.tval 0 := by simp [den, constDen]
  have hCE : 𝕋.den ρ (.app (.const `Klop.C []) (.const `Klop.E [])) = 𝕋.tval 1 := by
    show 𝕋.mkApp (𝕋.constDen `Klop.C []) (𝕋.den ρ (.const `Klop.E [])) = _
    rw [hE]
    exact 𝕋.den_C_app 0
  rw [hE, hCE]
  intro h
  exact absurd (𝕋.tval_inj h) (by decide)

end UniverseTower

end VEnv.Strengthening
end Lean4Lean
