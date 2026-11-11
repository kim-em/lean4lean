import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.RecBody

/-! # Derived rules for the type of `Eq.rec`

The syntactic motive type `motiveOf v u α a := ∀ b : α, @Eq α a b → Sort v` denotes
`motiveTy v ⟦α⟧ ⟦a⟧` (`den_motiveOf`); `Eq.refl α x : @Eq α x x` (`Sem.reflApp`); and a
motive applied to an endpoint and a proof of the equation is a type (`Sem.fibApp`).
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

/-- `@Eq.{u} A x y`. -/
def eqS (u : VLevel) (A x y : VExpr) : VExpr := .app (.app (.app (.const ``Eq [u]) A) x) y

/-- `@Eq.refl.{u} A x`. -/
def reflS (u : VLevel) (A x : VExpr) : VExpr := .app (.app (.const ``Eq.refl [u]) A) x

/-- `∀ b : α, @Eq α a b → Sort v`. -/
def motiveOf (v u : VLevel) (α a : VExpr) : VExpr :=
  .forallE α (.forallE (eqS u α.lift a.lift (.bvar 0)) (.sort v))

namespace UniverseTower
variable {𝕋 : UniverseTower}

local infix:50 " ∈ₛ " => 𝕋.mem

/-- The denotation of the syntactic motive type. -/
theorem den_motiveOf {ρ : Nat → 𝕋.S} {v u : VLevel} {α a : VExpr}
    (hα : 𝕋.den ρ α ∈ₛ 𝕋.El (𝕋.sortDen u)) (ha : 𝕋.den ρ a ∈ₛ 𝕋.El (𝕋.den ρ α)) :
    𝕋.den ρ (motiveOf v u α a) = 𝕋.motiveTy v (𝕋.den ρ α) (𝕋.den ρ a) := by
  show 𝕋.mkPi _ _ = 𝕋.mkPi _ _
  refine mkPi_congr fun b hb => ?_
  show 𝕋.mkPi _ _ = 𝕋.mkPi _ _
  have h : 𝕋.den (𝕋.cons b ρ) (eqS u α.lift a.lift (.bvar 0)) =
      𝕋.cand (𝕋.eqCand (𝕋.den ρ α) (𝕋.den ρ a) b) := by
    have := den_eqApp (𝕋 := 𝕋) (ρ := 𝕋.cons b ρ) (l := u) (A := α.lift) (x := a.lift)
      (y := .bvar 0) (by rw [𝕋.den_lift]; exact hα) (by rw [𝕋.den_lift, 𝕋.den_lift]; exact ha)
      (by rw [𝕋.den_lift]; exact hb)
    rw [𝕋.den_lift, 𝕋.den_lift] at this
    exact this
  rw [h]
  rfl

/-- The denotation of a reflexivity proof is `•`. -/
theorem den_reflS (ρ : Nat → 𝕋.S) (u : VLevel) (A x : VExpr) :
    𝕋.den ρ (reflS u A x) = 𝕋.star := by
  have hc : 𝕋.den ρ (.const ``Eq.refl [u]) = 𝕋.star := by simp [den, constDen]
  show 𝕋.mkApp (𝕋.mkApp (𝕋.den ρ (.const ``Eq.refl [u])) _) _ = _
  rw [hc]; simp [mkApp]

/-- `Eq.refl A x : @Eq A x x`. -/
theorem Sem.reflApp {Γ : List VExpr} {A x : VExpr} {u : VLevel}
    (HA : 𝕋.Sem Γ A A (.sort u)) (Hx : 𝕋.Sem Γ x x A) :
    𝕋.Sem Γ (reflS u A x) (reflS u A x) (eqS u A x x) := by
  have HE := Sem.eqApp HA Hx Hx
  intro ρ w hρ
  obtain ⟨-, -, hEm, -, hEr⟩ := HE ρ w hρ
  obtain ⟨-, -, hAm, -, -⟩ := HA ρ w hρ
  obtain ⟨-, -, hxm, -, -⟩ := Hx ρ w hρ
  have hden : 𝕋.den ρ (eqS u A x x) = 𝕋.cand (𝕋.eqCand (𝕋.den ρ A) (𝕋.den ρ x) (𝕋.den ρ x)) :=
    den_eqApp hAm hxm hxm
  have hval : PVal.ToR ((pval (reflS u A x)).subst w) := by
    show PVal.ToR (.app (.app ((constVal ``Eq.refl).subst w) _) _)
    rw [constVal_subst]
    have : constVal ``Eq.refl = reflVal := by simp [constVal]
    rw [this]
    exact .head (.appL .beta) (.head .beta .rfl)
  have hmem : 𝕋.mem (𝕋.den ρ (reflS u A x)) (𝕋.El (𝕋.den ρ (eqS u A x x))) := by
    rw [den_reflS, hden]
    exact star_mem_cand ⟨_, eqCand_mem_of_toR hxm hval⟩
  refine ⟨isSemTy_of_mem_sortDen hEm, rfl, hmem, fun _ => ?_, fun ρ' w' hρ' hr => ?_⟩
  · rw [hden, 𝕋.candOf_cand]
    exact ⟨eqCand_mem_of_toR hxm hval, eqCand_mem_of_toR hxm hval⟩
  · refine ⟨(tyRel_of_rel_sortDen hEm (hEr ρ' w' hρ' hr).2).2, ?_⟩
    rw [den_reflS, den_reflS]
    rw [den_reflS] at hmem
    rw [hden] at hmem ⊢
    exact (rel_cand hmem).2 hmem

/-- A motive applied to an endpoint and a proof of the equation is a type. -/
theorem Sem.fibApp {Γ : List VExpr} {α a M b t : VExpr} {u v : VLevel}
    (Hα : 𝕋.Sem Γ α α (.sort u)) (Ha : 𝕋.Sem Γ a a α)
    (HM : 𝕋.Sem Γ M M (motiveOf v u α a)) (Hb : 𝕋.Sem Γ b b α)
    (Ht : 𝕋.Sem Γ t t (eqS u α a b)) :
    𝕋.Sem Γ (.app (.app M b) t) (.app (.app M b) t) (.sort v) := by
  have facts : ∀ ρ w, 𝕋.ValOK Γ ρ w →
      𝕋.den ρ (.app (.app M b) t) = 𝕋.Fib (𝕋.den ρ M) (𝕋.den ρ b) ∧
      𝕋.ValidAny (𝕋.univList (recLv u v)) (𝕋.den ρ α) ∧
      𝕋.mem (𝕋.den ρ a) (𝕋.El (𝕋.den ρ α)) ∧
      𝕋.mem (𝕋.den ρ M) (𝕋.El (𝕋.motiveTy v (𝕋.den ρ α) (𝕋.den ρ a))) ∧
      𝕋.mem (𝕋.den ρ b) (𝕋.El (𝕋.den ρ α)) ∧
      𝕋.Rel (𝕋.den ρ α) (𝕋.den ρ a) (𝕋.den ρ b) := by
    intro ρ w hρ
    obtain ⟨-, -, hαm, -, -⟩ := Hα ρ w hρ
    obtain ⟨-, -, ham, -, -⟩ := Ha ρ w hρ
    obtain ⟨-, -, hMm, -, -⟩ := HM ρ w hρ
    obtain ⟨-, -, hbm, -, -⟩ := Hb ρ w hρ
    obtain ⟨-, -, htm, -, -⟩ := Ht ρ w hρ
    have hαv : 𝕋.ValidAny (𝕋.univList (recLv u v)) (𝕋.den ρ α) :=
      (mem_sortDen hαm).1.mono (Nat.le_max_left ..)
    rw [den_motiveOf hαm ham] at hMm
    have hE : 𝕋.den ρ (eqS u α a b) =
        𝕋.cand (𝕋.eqCand (𝕋.den ρ α) (𝕋.den ρ a) (𝕋.den ρ b)) := den_eqApp hαm ham hbm
    rw [hE] at htm
    obtain ⟨hts, hne⟩ := 𝕋.mem_El_cand.1 htm
    refine ⟨?_, hαv, ham, hMm, hbm, ((eqCand_nonempty_iff hαv.isPER).1 hne).2⟩
    show 𝕋.mkApp (𝕋.mkApp _ _) (𝕋.den ρ t) = _
    rw [hts]; rfl
  intro ρ w hρ
  obtain ⟨hden, hαv, ham, hMm, hbm, hab⟩ := facts ρ w hρ
  have hrefl : 𝕋.Rel (𝕋.motiveTy v (𝕋.den ρ α) (𝕋.den ρ a)) (𝕋.den ρ M) (𝕋.den ρ M) :=
    (motiveTy_valid (Nat.le_max_right ..) hαv _).isPER.refl _ hMm
  have hm := (fib_rel (Nat.le_max_right ..) hαv ham hMm hrefl hbm hab
    (hαv.isPER.refl _ hbm)).1
  refine ⟨isSemTy_sortDen _, rfl, by rw [hden]; exact hm,
    fun hc => (not_isCand_sortDen _ hc).elim, fun ρ' w' hρ' hr => ⟨rfl, ?_⟩⟩
  obtain ⟨hden', -⟩ := facts ρ' w' hρ'
  obtain ⟨-, -, hαm, -, -⟩ := Hα ρ w hρ
  have hMM' := ((HM ρ w hρ).2.2.2.2 ρ' w' hρ' hr).2
  rw [den_motiveOf hαm ham] at hMM'
  have hbb' := ((Hb ρ w hρ).2.2.2.2 ρ' w' hρ' hr).2
  show 𝕋.Rel (𝕋.sortDen v) _ _
  rw [hden, hden']
  exact (fib_rel (Nat.le_max_right ..) hαv ham hMm hMM' hbm hab hbb').2

end UniverseTower
end VEnv.Strengthening
end Lean4Lean
