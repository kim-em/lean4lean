import Lean4Lean.Theory.Typing.Strengthening.Klop.Model.Records

/-! # Uniform sections

The invariant that lets the semantic universes be sets with no universe of sets in the
metatheory. Function spaces are restricted to functions that send bounded families of
arguments to bounded families of results, level by level. Everything here is defined on raw
records, through the accessors `kind`, `argsOf` and `El`, so that the constructors of
semantic types can refer to it.

* `LvLe N X`: every universe occurring in `X` is `𝒰ⱼ` with `j < N`.
* `Small m X`: `X` is a base type, or `m = m' + 1` and `LvLe m' X`.
* `DpLe m X k`: the Π-depth of `X` above its `m`-small parts is at most `k`.
* `Tame m H`, `FamLe m H b`: a family of types has bounded level and, at each level `≥ m`,
  bounded depth; `b = (N, k)` bounds it lexicographically.
* `Lf b m I H s`: the section `s` of the family `H` over the world `I` is uniform at level
  `m`, with `b` as recursion measure. At a family of Π-types, `s` sends uniform sections of
  the domains to uniform sections of the fibres.
* `Unif m I H s`: `s` is uniform at every level from `m` on.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace SetModel
universe u
variable (𝕊 : SetModel.{u})

local infix:50 " ∈ₛ " => 𝕊.mem

/-- The domain of a Π record. -/
noncomputable def dom (X : 𝕊.S) : 𝕊.S := 𝕊.fst (𝕊.argsOf X)
/-- The fibre of a Π record over an element of its domain. -/
noncomputable def fib (X d : 𝕊.S) : 𝕊.S := 𝕊.app (𝕊.snd (𝕊.argsOf X)) d
/-- The codomain of a record of a function type out of a proposition. -/
noncomputable def cod (X : 𝕊.S) : 𝕊.S := 𝕊.snd (𝕊.argsOf X)

/-- Propositions, `T` and `Prop`. -/
def IsBase (X : 𝕊.S) : Prop :=
  𝕊.kind X = 𝕊.tagN 0 ∨ 𝕊.kind X = 𝕊.tagN 1 ∨ 𝕊.kind X = 𝕊.tagN 2

/-- Every universe occurring in `X` is `𝒰ⱼ` with `j < N`. -/
inductive LvLe (N : Nat) : 𝕊.S → Prop where
  | base {X} : 𝕊.IsBase X → LvLe N X
  | univ {X} {j : Nat} : 𝕊.kind X = 𝕊.tagN 3 → 𝕊.argsOf X = 𝕊.enc j → j < N → LvLe N X
  | pi {X} : 𝕊.kind X = 𝕊.tagN 4 → LvLe N (𝕊.dom X) →
      (∀ d, 𝕊.mem d (𝕊.El (𝕊.dom X)) → LvLe N (𝕊.fib X d)) → LvLe N X
  | piP {X} : 𝕊.kind X = 𝕊.tagN 5 → LvLe N (𝕊.cod X) → LvLe N X

/-- `X` has no structure visible at level `m`. -/
def Small (m : Nat) (X : 𝕊.S) : Prop := 𝕊.IsBase X ∨ ∃ m', m = m' + 1 ∧ 𝕊.LvLe m' X

/-- The Π-depth of `X` above its `m`-small parts is at most `k`. -/
inductive DpLe (m : Nat) : 𝕊.S → Nat → Prop where
  | small {X k} : 𝕊.Small m X → DpLe m X k
  | univ {X k} : 𝕊.kind X = 𝕊.tagN 3 → DpLe m X k
  | pi {X k} : 𝕊.kind X = 𝕊.tagN 4 → DpLe m (𝕊.dom X) k →
      (∀ d, 𝕊.mem d (𝕊.El (𝕊.dom X)) → DpLe m (𝕊.fib X d) k) → DpLe m X (k + 1)
  | piP {X k} : 𝕊.kind X = 𝕊.tagN 5 → DpLe m (𝕊.cod X) k → DpLe m X (k + 1)

/-- A world: an index type for families. -/
abbrev World := Type (u + 1)

/-- The family `H` has bounded level, and bounded depth at every level from `m` on. -/
def Tame (m : Nat) {I : World.{u}} (H : I → 𝕊.S) : Prop :=
  (∃ N, ∀ i, 𝕊.LvLe N (H i)) ∧
  ∀ m', m ≤ m' → ∃ k, ∀ i, 𝕊.LvLe m' (H i) → 𝕊.DpLe m' (H i) k

/-- `(N, k)` bounds the family `H` above `m`: its fibres that are not `m`-small have level at
most `N` and, at level `N`, depth at most `k`. -/
def FamLe (m : Nat) {I : World.{u}} (H : I → 𝕊.S) (b : Nat × Nat) : Prop :=
  ∀ i, ¬ 𝕊.Small m (H i) → 𝕊.LvLe b.1 (H i) ∧ 𝕊.DpLe b.1 (H i) b.2

/-- **Uniformity at level `m`** of the section `s` of the family `H` over the world `I`, by
recursion on a bound `b` of the family. -/
def Lf (b : Nat × Nat) (m : Nat) (I : World.{u}) (H s : I → 𝕊.S) : Prop :=
  𝕊.Tame m H ∧ 𝕊.FamLe m H b ∧
  (∃ k, ∀ i, 𝕊.kind (H i) = 𝕊.tagN 3 → ¬ 𝕊.Small m (H i) → 𝕊.LvLe m (s i) → 𝕊.DpLe m (s i) k) ∧
  (∀ b', Prod.Lex (· < ·) (· < ·) b' b → ∀ (I' : World.{u}) (φ : I' → I) (a : I' → 𝕊.S),
    (∀ i', 𝕊.kind (H (φ i')) = 𝕊.tagN 4 ∧ ¬ 𝕊.Small m (H (φ i'))) →
    (∀ i', 𝕊.mem (a i') (𝕊.El (𝕊.dom (H (φ i'))))) →
    (∀ m', m ≤ m' → Lf b' m' I' (fun i' => 𝕊.dom (H (φ i'))) a) →
    𝕊.Tame m (fun i' => 𝕊.fib (H (φ i')) (a i')) →
    𝕊.FamLe m (fun i' => 𝕊.fib (H (φ i')) (a i')) b' →
    Lf b' m I' (fun i' => 𝕊.fib (H (φ i')) (a i')) (fun i' => 𝕊.ap (s (φ i')) (a i'))) ∧
  (∀ b', Prod.Lex (· < ·) (· < ·) b' b → ∀ (I' : World.{u}) (φ : I' → I),
    (∀ i', 𝕊.kind (H (φ i')) = 𝕊.tagN 5 ∧ ¬ 𝕊.Small m (H (φ i'))) →
    𝕊.Tame m (fun i' => 𝕊.cod (H (φ i'))) →
    𝕊.FamLe m (fun i' => 𝕊.cod (H (φ i'))) b' →
    Lf b' m I' (fun i' => 𝕊.cod (H (φ i'))) (fun i' => 𝕊.ap (s (φ i')) 𝕊.star))
termination_by b
decreasing_by all_goals assumption

/-- The section `s` of `H` is uniform at every level from `m` on. -/
def Unif (m : Nat) (I : World.{u}) (H s : I → 𝕊.S) : Prop :=
  ∀ m', m ≤ m' → ∃ b, 𝕊.Lf b m' I H s

end SetModel

end VEnv.Strengthening
end Lean4Lean
