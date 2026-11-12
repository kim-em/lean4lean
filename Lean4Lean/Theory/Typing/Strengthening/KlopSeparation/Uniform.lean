import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.Records

/-! # Uniform sections

The invariant that replaces the universe tower (`FIRST_PRINCIPLES.md` §30.6, §30.7). Function
spaces are restricted to functions that send bounded families of arguments to bounded families
of results, level by level. Everything here is defined on raw records, through the accessors
`kind`, `argsOf` and `El`, so that the constructors of semantic types can refer to it.

* `LvLe N X`: every universe occurring in `X` is `𝒰ⱼ` with `j < N`.
* `Small m X`: `X` is a base type, or `m = m' + 1` and `LvLe m' X`.
* `DpLe m X k`: the Π-depth of `X` above its `m`-small parts is at most `k`.
* `Tame m H`, `FamLe m H b`: a family of types has bounded level and, at each level `≥ m`,
  bounded depth; `b = (N, k)` bounds it lexicographically.
* `Lf b m I H s`: the section `s` of the family `H` over the world `I` is uniform at level
  `m`, with `b` as recursion measure.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace SetModel
universe u
variable (𝕋 : SetModel.{u})

local infix:50 " ∈ₛ " => 𝕋.mem

/-- The domain of a Π record. -/
noncomputable def dom (X : 𝕋.S) : 𝕋.S := 𝕋.fst (𝕋.argsOf X)
/-- The fibre of a Π record over an element of its domain. -/
noncomputable def fib (X d : 𝕋.S) : 𝕋.S := 𝕋.app (𝕋.snd (𝕋.argsOf X)) d
/-- The codomain of a record of a function type out of a proposition. -/
noncomputable def cod (X : 𝕋.S) : 𝕋.S := 𝕋.snd (𝕋.argsOf X)

/-- Propositions, `T` and `Prop`. -/
def IsBase (X : 𝕋.S) : Prop :=
  𝕋.kind X = 𝕋.tagN 0 ∨ 𝕋.kind X = 𝕋.tagN 1 ∨ 𝕋.kind X = 𝕋.tagN 2

/-- Every universe occurring in `X` is `𝒰ⱼ` with `j < N`. -/
inductive LvLe (N : Nat) : 𝕋.S → Prop where
  | base {X} : 𝕋.IsBase X → LvLe N X
  | univ {X} {j : Nat} : 𝕋.kind X = 𝕋.tagN 3 → 𝕋.argsOf X = 𝕋.enc j → j < N → LvLe N X
  | pi {X} : 𝕋.kind X = 𝕋.tagN 4 → LvLe N (𝕋.dom X) →
      (∀ d, 𝕋.mem d (𝕋.El (𝕋.dom X)) → LvLe N (𝕋.fib X d)) → LvLe N X
  | piP {X} : 𝕋.kind X = 𝕋.tagN 5 → LvLe N (𝕋.cod X) → LvLe N X

/-- `X` has no structure visible at level `m`. -/
def Small (m : Nat) (X : 𝕋.S) : Prop := 𝕋.IsBase X ∨ ∃ m', m = m' + 1 ∧ 𝕋.LvLe m' X

/-- The Π-depth of `X` above its `m`-small parts is at most `k`. -/
inductive DpLe (m : Nat) : 𝕋.S → Nat → Prop where
  | small {X k} : 𝕋.Small m X → DpLe m X k
  | univ {X k} : 𝕋.kind X = 𝕋.tagN 3 → DpLe m X k
  | pi {X k} : 𝕋.kind X = 𝕋.tagN 4 → DpLe m (𝕋.dom X) k →
      (∀ d, 𝕋.mem d (𝕋.El (𝕋.dom X)) → DpLe m (𝕋.fib X d) k) → DpLe m X (k + 1)
  | piP {X k} : 𝕋.kind X = 𝕋.tagN 5 → DpLe m (𝕋.cod X) k → DpLe m X (k + 1)

/-- A world: an index type for families. -/
abbrev World := Type (u + 1)

/-- The family `H` has bounded level, and bounded depth at every level from `m` on. -/
def Tame (m : Nat) {I : World.{u}} (H : I → 𝕋.S) : Prop :=
  (∃ N, ∀ i, 𝕋.LvLe N (H i)) ∧
  ∀ m', m ≤ m' → ∃ k, ∀ i, 𝕋.LvLe m' (H i) → 𝕋.DpLe m' (H i) k

/-- `(N, k)` bounds the family `H` above `m`: its fibres that are not `m`-small have level at
most `N` and, at level `N`, depth at most `k`. -/
def FamLe (m : Nat) {I : World.{u}} (H : I → 𝕋.S) (b : Nat × Nat) : Prop :=
  ∀ i, ¬ 𝕋.Small m (H i) → 𝕋.LvLe b.1 (H i) ∧ 𝕋.DpLe b.1 (H i) b.2

/-- **Uniformity at level `m`** of the section `s` of the family `H` over the world `I`, by
recursion on a bound `b` of the family. -/
def Lf (b : Nat × Nat) (m : Nat) (I : World.{u}) (H s : I → 𝕋.S) : Prop :=
  𝕋.Tame m H ∧ 𝕋.FamLe m H b ∧
  (∃ k, ∀ i, 𝕋.kind (H i) = 𝕋.tagN 3 → ¬ 𝕋.Small m (H i) → 𝕋.LvLe m (s i) → 𝕋.DpLe m (s i) k) ∧
  (∀ b', Prod.Lex (· < ·) (· < ·) b' b → ∀ (I' : World.{u}) (φ : I' → I) (a : I' → 𝕋.S),
    (∀ i', 𝕋.kind (H (φ i')) = 𝕋.tagN 4 ∧ ¬ 𝕋.Small m (H (φ i'))) →
    (∀ i', 𝕋.mem (a i') (𝕋.El (𝕋.dom (H (φ i'))))) →
    (∀ m', m ≤ m' → Lf b' m' I' (fun i' => 𝕋.dom (H (φ i'))) a) →
    𝕋.Tame m (fun i' => 𝕋.fib (H (φ i')) (a i')) →
    𝕋.FamLe m (fun i' => 𝕋.fib (H (φ i')) (a i')) b' →
    Lf b' m I' (fun i' => 𝕋.fib (H (φ i')) (a i')) (fun i' => 𝕋.ap (s (φ i')) (a i'))) ∧
  (∀ b', Prod.Lex (· < ·) (· < ·) b' b → ∀ (I' : World.{u}) (φ : I' → I),
    (∀ i', 𝕋.kind (H (φ i')) = 𝕋.tagN 5 ∧ ¬ 𝕋.Small m (H (φ i'))) →
    𝕋.Tame m (fun i' => 𝕋.cod (H (φ i'))) →
    𝕋.FamLe m (fun i' => 𝕋.cod (H (φ i'))) b' →
    Lf b' m I' (fun i' => 𝕋.cod (H (φ i'))) (fun i' => 𝕋.ap (s (φ i')) 𝕋.star))
termination_by b
decreasing_by all_goals assumption

/-- The section `s` of `H` is uniform at every level from `m` on. -/
def Unif (m : Nat) (I : World.{u}) (H s : I → 𝕋.S) : Prop :=
  ∀ m', m ≤ m' → ∃ b, 𝕋.Lf b m' I H s

end SetModel

end VEnv.Strengthening
end Lean4Lean
