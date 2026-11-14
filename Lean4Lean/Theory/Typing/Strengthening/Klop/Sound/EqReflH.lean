import Lean4Lean.Theory.Typing.Strengthening.Klop.Sound.Consts

/-! # Soundness: the constants `Eq.refl` and `H`

The denotation of an equation `@Eq α a b` is the proposition of the candidate `eqCand α a b`
(`den_eqApp`). `Eq.refl` and `H` are proofs of Π-propositions: they denote `•`, and their
values `λλ. r` and `bot` realize the propositions.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace SetModel
variable {𝕊 : SetModel}

local infix:50 " ∈ₛ " => 𝕊.mem

/-- The denotation of `@Eq.{l} A x y`. -/
theorem den_eqApp {ρ : Nat → 𝕊.S} {l : VLevel} {A x y : VExpr}
    (hA : 𝕊.den ρ A ∈ₛ 𝕊.El (𝕊.sortDen l)) (hx : 𝕊.den ρ x ∈ₛ 𝕊.El (𝕊.den ρ A))
    (hy : 𝕊.den ρ y ∈ₛ 𝕊.El (𝕊.den ρ A)) :
    𝕊.den ρ (.app (.app (.app (.const ``Eq [l]) A) x) y) =
      𝕊.cand (𝕊.eqCand (𝕊.den ρ A) (𝕊.den ρ x) (𝕊.den ρ y)) := by
  have hc : 𝕊.den ρ (.const ``Eq [l]) = 𝕊.eqDen l := by simp [den, constDen]
  show 𝕊.mkApp (𝕊.mkApp (𝕊.mkApp (𝕊.den ρ (.const ``Eq [l])) _) _) _ = _
  rw [hc, eqDen, 𝕊.mkApp_mkLam hA, 𝕊.mkApp_mkLam hx, 𝕊.mkApp_mkLam hy]

/-- A proof constant denoting `•` satisfies `ConstOK` when its type is a proposition
realized by its value. -/
theorem constOK_of_cand {c : Name} {ls : List VLevel} {ty : VExpr}
    (hden : 𝕊.constDen c ls = 𝕊.star) (hc : ∀ ρ : Nat → 𝕊.S, 𝕊.IsCand (𝕊.den ρ ty))
    (hv : ∀ ρ : Nat → 𝕊.S, (𝕊.candOf (𝕊.den ρ ty)).mem (constVal c)) : 𝕊.ConstOK c ls ty := by
  intro ρ
  refine ⟨?_, fun _ => hv ρ⟩
  rw [hden, isCand_eq (hc ρ)]
  exact star_mem_cand ⟨_, hv ρ⟩

/-- Values reducing to `r` realize an equation with identical endpoints. -/
theorem eqCand_mem_of_toR {α a : 𝕊.S} {v : PVal} (ha : a ∈ₛ 𝕊.El α) (hv : PVal.ToR v) :
    (𝕊.eqCand α a a).mem v := by
  rw [eqCand, if_pos ⟨ha, rfl⟩]
  exact .inl hv

/-- Values reducing to `bot` realize an equation with coarsely related endpoints. -/
theorem eqCand_mem_of_toBot {α a b : 𝕊.S} {v : PVal} (ha : a ∈ₛ 𝕊.El α) (hab : 𝕊.Rel α a b)
    (hv : PVal.ToBot v) : (𝕊.eqCand α a b).mem v := by
  unfold eqCand
  by_cases h : a ∈ₛ 𝕊.El α ∧ a = b
  · rw [if_pos h]; exact .inr hv
  · rw [if_neg h, if_pos ⟨ha, hab⟩]; exact hv

theorem tT_mem_sort1 : 𝕊.tT ∈ₛ 𝕊.El (𝕊.sortDen (.succ .zero)) :=
  (ValidAny.tT (lower := 𝕊.univList 0)).mem_univ fun hc => (not_isCand_tT hc).elim

/-- `H : ∀ x y : T, x = y`. -/
theorem constOK_H (ls : List VLevel) :
    𝕊.ConstOK `Klop.H ls
      (.forallE (.const `Klop.T []) (.forallE (.const `Klop.T [])
        (.app (.app (.app (.const ``Eq [.succ .zero]) (.const `Klop.T [])) (.bvar 1))
          (.bvar 0)))) := by
  have hfib : ∀ (ρ : Nat → 𝕊.S) (x y : 𝕊.S), x ∈ₛ 𝕊.El 𝕊.tT → y ∈ₛ 𝕊.El 𝕊.tT →
      𝕊.den (𝕊.cons y (𝕊.cons x ρ))
        (.app (.app (.app (.const ``Eq [.succ .zero]) (.const `Klop.T [])) (.bvar 1)) (.bvar 0)) =
      𝕊.cand (𝕊.eqCand 𝕊.tT x y) := by
    intro ρ x y hx hy
    rw [den_eqApp (by rw [den_klopT]; exact tT_mem_sort1) (by rw [den_klopT]; exact hx)
      (by rw [den_klopT]; exact hy), den_klopT]
    rfl
  refine constOK_of_cand (by simp [constDen]) (fun ρ => ?_) (fun ρ => ?_)
  · show 𝕊.IsCand (𝕊.mkPi _ _)
    refine mkPi_isCand fun x hx => ?_
    rw [den_klopT] at hx
    show 𝕊.IsCand (𝕊.mkPi _ _)
    refine mkPi_isCand fun y hy => ?_
    rw [den_klopT] at hy
    exact ⟨_, hfib ρ x y hx hy⟩
  · have hcv : constVal `Klop.H = .bot := by simp [constVal]
    rw [hcv]
    show (𝕊.candOf (𝕊.mkPi _ _)).mem _
    refine lam_val_mem (mkPi_isCand fun x hx => mkPi_isCand fun y hy => ?_) fun x hx u _ _ => ?_
    · rw [den_klopT] at hx hy; exact ⟨_, hfib ρ x y hx hy⟩
    · rw [den_klopT] at hx
      show (𝕊.candOf (𝕊.mkPi _ _)).mem _
      refine lam_val_mem (mkPi_isCand fun y hy => ?_) fun y hy u' _ _ => ?_
      · rw [den_klopT] at hy; exact ⟨_, hfib ρ x y hx hy⟩
      · rw [den_klopT] at hy
        rw [hfib ρ x y hx hy, 𝕊.candOf_cand]
        refine eqCand_mem_of_toBot hx (𝕊.rel_tT hx hy) ?_
        exact .head (.appL .botApp) (.head .botApp .rfl)

/-- `Eq.refl : ∀ {α : Sort u} (a : α), a = a`. -/
theorem constOK_EqRefl (ls : List VLevel) :
    𝕊.ConstOK ``Eq.refl ls (canonicalEqReflType.instL ls) := by
  have hty : canonicalEqReflType.instL ls =
      .forallE (.sort ((VLevel.param 0).inst ls)) (.forallE (.bvar 0)
        (.app (.app (.app (.const ``Eq [(VLevel.param 0).inst ls]) (.bvar 1)) (.bvar 0))
          (.bvar 0))) := by
    simp [canonicalEqReflType, VExpr.instL]
  rw [hty]
  generalize (VLevel.param 0).inst ls = l
  have hfib : ∀ (ρ : Nat → 𝕊.S) (α a : 𝕊.S), α ∈ₛ 𝕊.El (𝕊.sortDen l) → a ∈ₛ 𝕊.El α →
      𝕊.den (𝕊.cons a (𝕊.cons α ρ))
        (.app (.app (.app (.const ``Eq [l]) (.bvar 1)) (.bvar 0)) (.bvar 0)) =
      𝕊.cand (𝕊.eqCand α a a) := fun ρ α a hα ha => den_eqApp (A := .bvar 1) hα ha ha
  have hcand : ∀ ρ : Nat → 𝕊.S, 𝕊.IsCand (𝕊.den ρ
      (.forallE (.sort l) (.forallE (.bvar 0)
        (.app (.app (.app (.const ``Eq [l]) (.bvar 1)) (.bvar 0)) (.bvar 0))))) := by
    intro ρ
    show 𝕊.IsCand (𝕊.mkPi _ _)
    refine mkPi_isCand fun α hα => ?_
    show 𝕊.IsCand (𝕊.mkPi _ _)
    exact mkPi_isCand fun a ha => ⟨_, hfib ρ α a hα ha⟩
  refine constOK_of_cand (by simp [constDen]) hcand (fun ρ => ?_)
  have hcv : constVal ``Eq.refl = reflVal := by simp [constVal]
  rw [hcv]
  show (𝕊.candOf (𝕊.mkPi _ _)).mem _
  refine lam_val_mem (hcand ρ) fun α hα u _ _ => ?_
  show (𝕊.candOf (𝕊.mkPi _ _)).mem _
  refine lam_val_mem (mkPi_isCand fun a ha => ⟨_, hfib ρ α a hα ha⟩) fun a ha u' _ _ => ?_
  rw [hfib ρ α a hα ha, 𝕊.candOf_cand]
  refine eqCand_mem_of_toR ha ?_
  exact .head (.appL .beta) (.head .beta .rfl)

end SetModel
end VEnv.Strengthening
end Lean4Lean
