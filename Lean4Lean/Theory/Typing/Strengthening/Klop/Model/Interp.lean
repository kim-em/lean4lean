import Lean4Lean.Theory.Typing.Strengthening.Klop.Model.Bound
import Lean4Lean.Theory.Typing.Strengthening.Klop.Model.Translate

/-! # The interpretation of terms

Valid semantic types by level (`ValidAny`), the universes (`univ`), the denotations of the
constants, and the denotation `den ρ e` of a raw term at a valuation `ρ : Nat → S` of its de
Bruijn variables. Universe levels are evaluated at the empty assignment, since the
fundamental theorem is proved at universe-parameter count `0`.

`den_CE_ne_E`: the two closed terms of the counterexample have different denotations.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace SetModel
variable (𝕊 : SetModel)

local infix:50 " ∈ₛ " => 𝕊.mem

/-- The family `F` over `D` is uniform as a function into a universe: at every level `m`, it
sends a uniform section of `D` to a family of bounded depth. -/
def FamUnif (D : 𝕊.S) (F : 𝕊.S → 𝕊.S) : Prop :=
  ∀ (m : Nat) (I : World) (a : I → 𝕊.S), (∀ i, 𝕊.mem (a i) (𝕊.El D)) →
    𝕊.Unif m I (fun _ => D) a → ∃ k, ∀ i, 𝕊.LvLe m (F (a i)) → 𝕊.DpLe m (F (a i)) k

/-- Valid semantic types, given the universes of lower level: good candidates and data
types. -/
inductive ValidAny (lower : List 𝕊.S) : 𝕊.S → Prop where
  | prop {c : Candidate} : c.Good → ValidAny lower (𝕊.cand c)
  | tT : ValidAny lower 𝕊.tT
  | tProp : ValidAny lower 𝕊.tProp
  | univ {u : 𝕊.S} : u ∈ lower → ValidAny lower u
  | pi {D : 𝕊.S} {F : 𝕊.S → 𝕊.S} : ValidAny lower D → ¬ 𝕊.IsCand D →
      (∀ d, 𝕊.mem d (𝕊.El D) → ValidAny lower (F d)) →
      (∀ d, 𝕊.mem d (𝕊.El D) → 𝕊.IsCand (F d) → F d = 𝕊.cand Candidate.full) →
      (∀ d d', 𝕊.mem d (𝕊.El D) → 𝕊.Rel D d d' → 𝕊.TyRel (F d) (F d')) →
      (¬ ∀ d, 𝕊.mem d (𝕊.El D) → 𝕊.IsCand (F d)) →
      𝕊.FamUnif D F →
      ValidAny lower (𝕊.tPi D F)
  | piP {c : Candidate} {B : 𝕊.S} : c.Good → (∃ v, c.mem v) → ValidAny lower B →
      ¬ 𝕊.IsCand B → ValidAny lower (𝕊.tPiP c B)

/-- The members of a data universe: valid data types and the full candidate. -/
def ValidTy (lower : List 𝕊.S) (x : 𝕊.S) : Prop :=
  𝕊.ValidAny lower x ∧ (𝕊.IsCand x → x = 𝕊.cand Candidate.full)

/-- The universes below level `n`: `univList n = [𝒰₀, …, 𝒰ₙ₋₁]`. -/
noncomputable def univList : Nat → List 𝕊.S
  | 0 => []
  | n + 1 => univList n ++
      [𝕊.tU n (𝕊.sep (𝕊.bset (𝕊.baseOf (univList n))) (𝕊.ValidTy (univList n)))]

/-- The universe `𝒰ₙ`, the denotation of `Sort (n + 1)`. -/
noncomputable def univ (n : Nat) : 𝕊.S :=
  𝕊.tU n (𝕊.sep (𝕊.bset (𝕊.baseOf (𝕊.univList n))) (𝕊.ValidTy (𝕊.univList n)))

/-- The denotation of `Sort ℓ` at the empty level assignment. -/
noncomputable def sortDen (l : VLevel) : 𝕊.S :=
  match l.eval [] with
  | 0 => 𝕊.tProp
  | n + 1 => 𝕊.univ n

/-- The candidate of `@Eq α a b`: `r` is allowed exactly when the endpoints are identical. -/
noncomputable def eqCand (α a b : 𝕊.S) : Candidate :=
  if a ∈ₛ 𝕊.El α ∧ a = b then Candidate.rOrBot
  else if a ∈ₛ 𝕊.El α ∧ 𝕊.Rel α a b then Candidate.botOnly
  else Candidate.empty

/-- The successor on the elements of `T`. -/
noncomputable def tsucc (x : 𝕊.S) : 𝕊.S :=
  if h : ∃ i : Fin 3, x = 𝕊.tval i then 𝕊.tval (h.choose + 1) else x

/-- `Eq.{u}` as a curried function. -/
noncomputable def eqDen (u : VLevel) : 𝕊.S :=
  𝕊.mkLam (𝕊.sortDen u) fun α => 𝕊.mkLam α fun a => 𝕊.mkLam α fun b => 𝕊.cand (𝕊.eqCand α a b)

/-- The motive type of `Eq.rec.{v, u}` at `α`, `a`. -/
noncomputable def motiveTy (v : VLevel) (α a : 𝕊.S) : 𝕊.S :=
  𝕊.mkPi α fun b => 𝕊.mkPi (𝕊.cand (𝕊.eqCand α a b)) fun _ => 𝕊.sortDen v

/-- The result of `Eq.rec` at data: a function of the endpoints only. -/
noncomputable def recBody (α a M m b : 𝕊.S) : 𝕊.S :=
  if 𝕊.IsCand (𝕊.mkApp (𝕊.mkApp M b) 𝕊.star) then 𝕊.star
  else if α = 𝕊.tT ∧ 𝕊.mkApp (𝕊.mkApp M b) 𝕊.star = 𝕊.tT ∧ a ≠ b then 𝕊.tsucc a
  else m

/-- `Eq.rec.{v, u}` as a curried function. -/
noncomputable def recDen (v u : VLevel) : 𝕊.S :=
  𝕊.mkLam (𝕊.sortDen u) fun α => 𝕊.mkLam α fun a =>
    𝕊.mkLam (𝕊.motiveTy v α a) fun M =>
      𝕊.mkLam (𝕊.mkApp (𝕊.mkApp M a) 𝕊.star) fun m =>
        𝕊.mkLam α fun b => 𝕊.mkLam (𝕊.cand (𝕊.eqCand α a b)) fun _ => 𝕊.recBody α a M m b

/-- The denotation of a constant of the minimal Klop environment. -/
noncomputable def constDen (c : Name) (ls : List VLevel) : 𝕊.S :=
  if c = ``Eq then 𝕊.eqDen (ls.getD 0 .zero)
  else if c = ``Eq.rec then 𝕊.recDen (ls.getD 0 .zero) (ls.getD 1 .zero)
  else if c = `Klop.T then 𝕊.tT
  else if c = `Klop.E then 𝕊.tval 0
  else if c = `Klop.P then 𝕊.cand Candidate.empty
  else if c = `Klop.C then 𝕊.mkLam 𝕊.tT 𝕊.tsucc
  else 𝕊.star

/-- Extend a valuation by a value for variable `0`. -/
def cons (d : 𝕊.S) (ρ : Nat → 𝕊.S) : Nat → 𝕊.S
  | 0 => d
  | i + 1 => ρ i

/-- **The denotation of a term** at a valuation of its variables. -/
noncomputable def den : (Nat → 𝕊.S) → VExpr → 𝕊.S
  | ρ, .bvar i => ρ i
  | _, .sort l => 𝕊.sortDen l
  | _, .const c ls => 𝕊.constDen c ls
  | ρ, .app f a => 𝕊.mkApp (den ρ f) (den ρ a)
  | _, .proj _ _ _ => 𝕊.star
  | ρ, .lam A b => 𝕊.mkLam (den ρ A) fun d => den (𝕊.cons d ρ) b
  | ρ, .forallE A B => 𝕊.mkPi (den ρ A) fun d => den (𝕊.cons d ρ) B

theorem tsucc_tval (i : Fin 3) : 𝕊.tsucc (𝕊.tval i) = 𝕊.tval (i + 1) := by
  have h : ∃ j : Fin 3, 𝕊.tval i = 𝕊.tval j := ⟨i, rfl⟩
  rw [tsucc, dif_pos h, ← 𝕊.tval_inj h.choose_spec]

theorem tsucc_ne (i : Fin 3) : 𝕊.tsucc (𝕊.tval i) ≠ 𝕊.tval i := by
  rw [tsucc_tval]
  intro h
  have key : ∀ j : Fin 3, j + 1 ≠ j := by decide
  exact key i (𝕊.tval_inj h)

theorem tval_ne_star (i : Fin 3) : 𝕊.tval i ≠ 𝕊.star := fun h => by
  have := 𝕊.tagN_inj (𝕊.pair_inj h).1
  omega

/-- `⟦C⟧` is the successor function on `T`. -/
theorem den_C_app (i : Fin 3) :
    𝕊.mkApp (𝕊.constDen `Klop.C []) (𝕊.tval i) = 𝕊.tval (i + 1) := by
  have hC : 𝕊.constDen `Klop.C [] = 𝕊.mkLam 𝕊.tT 𝕊.tsucc := by
    simp [constDen]
  rw [hC, 𝕊.mkApp_mkLam (𝕊.mem_El_tT.2 ⟨i, rfl⟩), tsucc_tval]

/-- **The two closed terms of the counterexample have different denotations**:
`⟦C E⟧ = 1` and `⟦E⟧ = 0`. -/
theorem den_CE_ne_E (ρ : Nat → 𝕊.S) :
    𝕊.den ρ (.app (.const `Klop.C []) (.const `Klop.E [])) ≠ 𝕊.den ρ (.const `Klop.E []) := by
  have hE : 𝕊.den ρ (.const `Klop.E []) = 𝕊.tval 0 := by simp [den, constDen]
  have hCE : 𝕊.den ρ (.app (.const `Klop.C []) (.const `Klop.E [])) = 𝕊.tval 1 := by
    show 𝕊.mkApp (𝕊.constDen `Klop.C []) (𝕊.den ρ (.const `Klop.E [])) = _
    rw [hE]
    exact 𝕊.den_C_app 0
  rw [hE, hCE]
  intro h
  exact absurd (𝕊.tval_inj h) (by decide)

end SetModel

end VEnv.Strengthening
end Lean4Lean
