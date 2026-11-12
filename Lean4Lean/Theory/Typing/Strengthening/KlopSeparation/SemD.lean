import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.EqConst

/-! # Semantic terms in a syntactic context

`SemD Γ d A`: a *semantic* term `d`, a function of the valuation, is an element of the
denotation of the syntactic type `A` at every valuation of `Γ`, and respects coarse
relatedness of valuations. It lets the abstraction lemma be used for terms that are not
syntax, such as the body of `Eq.rec` (`SemD.lam`), while the contexts, valuations and types
are those of the syntactic judgment `Sem`.

Also `Sem.eqApp`, the derived rule for an equation `@Eq A x y`.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace SetModel
variable {𝕋 : SetModel}

local infix:50 " ∈ₛ " => 𝕋.mem

/-- A semantic term in context: membership and coarse relatedness. -/
def SemD (𝕋 : SetModel) (Γ : List VExpr) (d : (Nat → 𝕋.S) → 𝕋.S) (A : VExpr) : Prop :=
  ∀ ρ w, 𝕋.ValOK Γ ρ w →
    𝕋.mem (d ρ) (𝕋.El (𝕋.den ρ A)) ∧
    ∀ ρ' w', 𝕋.ValOK Γ ρ' w' → 𝕋.CoRel Γ ρ ρ' → 𝕋.Rel (𝕋.den ρ A) (d ρ) (d ρ')

/-- Abstraction of a semantic term. -/
theorem SemD.lam {Γ : List VExpr} {A B : VExpr} {u v : VLevel} {d : (Nat → 𝕋.S) → 𝕋.S}
    (HA : 𝕋.Sem Γ A A (.sort u)) (HB : 𝕋.Sem (A :: Γ) B B (.sort v))
    (Hd : 𝕋.SemD (A :: Γ) d B)
    (HAU : 𝕋.SemU Γ A (.sort u)) (HBU : 𝕋.SemU (A :: Γ) B (.sort v))
    (HdU : 𝕋.SemDU (A :: Γ) d B) :
    𝕋.SemD Γ (fun ρ => 𝕋.mkLam (𝕋.den ρ A) fun x => d (𝕋.cons x ρ)) (.forallE A B) := by
  have HPi : 𝕋.Sem Γ (.forallE A B) (.forallE A B) (.sort (.imax u v)) := Sem.forallE HA HB HBU
  have HlamU := SemDU.lam HA HB (fun ρ w hρ => (Hd ρ w hρ).1) HAU HBU HdU
  have key : ∀ ρ w, 𝕋.ValOK Γ ρ w →
      𝕋.mem (𝕋.mkLam (𝕋.den ρ A) fun x => d (𝕋.cons x ρ)) (𝕋.El (𝕋.den ρ (.forallE A B))) := by
    intro ρ w hρ
    obtain ⟨-, -, hAm, -, -⟩ := HA ρ w hρ
    have hAty : 𝕋.IsSemTy (𝕋.den ρ A) := isSemTy_of_mem_sortDen hAm
    obtain ⟨n, hAv⟩ := hAty
    obtain ⟨hfib, -⟩ := HB.fibres hρ ⟨n, hAv⟩
    refine mkLam_mem_mkPi (n := sortLv v) (fun d hd => (mem_sortDen (hfib d hd).1).1)
      (fun x hx => ?_) (fun x x' hx hxx' => hAv.isPER.mem _ _ hx hxx') (fun x x' hx hxx' => ?_)
      (fun hDc hall => SemDU.piUnif HlamU hρ
        (fun x hx => ⟨_, (mem_sortDen (hfib x hx).1).1⟩) (fun x hx => ?_) hDc hall)
    · obtain ⟨u', hu'⟩ := exists_valOK_cons hρ ⟨n, hAv⟩ hx
      exact (Hd _ _ hu').1
    · have hx' := hAv.isPER.mem _ _ hx hxx'
      obtain ⟨u₁, h₁⟩ := exists_valOK_cons hρ ⟨n, hAv⟩ hx
      obtain ⟨u₂, h₂⟩ := exists_valOK_cons hρ ⟨n, hAv⟩ hx'
      exact (Hd _ _ h₁).2 _ _ h₂ (coRel_cons (coRel_refl hρ) rfl hxx')
    · obtain ⟨u', hu'⟩ := exists_valOK_cons hρ ⟨n, hAv⟩ hx
      exact (Hd _ _ hu').1
  intro ρ w hρ
  refine ⟨key ρ w hρ, fun ρ' w' hρ' hr => ?_⟩
  obtain ⟨-, -, hAm, -, hAr⟩ := HA ρ w hρ
  have hAty : 𝕋.IsSemTy (𝕋.den ρ A) := isSemTy_of_mem_sortDen hAm
  obtain ⟨-, -, hPim, -, hPir⟩ := HPi ρ w hρ
  obtain ⟨-, -, hAm', -, -⟩ := HA ρ' w' hρ'
  have hAty' : 𝕋.IsSemTy (𝕋.den ρ' A) := isSemTy_of_mem_sortDen hAm'
  obtain ⟨-, -, hPim', -, -⟩ := HPi ρ' w' hρ'
  have hTP := (tyRel_of_rel_sortDen hPim (hPir ρ' w' hρ' hr).2).2
  have hTA : 𝕋.TyRel (𝕋.den ρ A) (𝕋.den ρ' A) :=
    (tyRel_of_rel_sortDen hAm (hAr ρ' w' hρ' hr).2).2
  have hsameP := (mem_sortDen hPim).1.tyRel_same (mem_sortDen hPim').1 hTP
  have hsameA := (mem_sortDen hAm).1.tyRel_same (mem_sortDen hAm').1 hTA
  have hg' : 𝕋.mem (𝕋.mkLam (𝕋.den ρ' A) fun x => d (𝕋.cons x ρ'))
      (𝕋.El (𝕋.den ρ (.forallE A B))) := by
    rw [hsameP.1]; exact key ρ' w' hρ'
  refine rel_mkPi_of_pointwise (key ρ w hρ) hg' fun x hx => ?_
  have hx' : 𝕋.mem x (𝕋.El (𝕋.den ρ' A)) := hsameA.1 ▸ hx
  rw [𝕋.mkApp_mkLam hx, 𝕋.mkApp_mkLam hx']
  obtain ⟨u₁, h₁⟩ := exists_valOK_cons hρ hAty hx
  obtain ⟨u₂, h₂⟩ := exists_valOK_cons hρ' hAty' hx'
  obtain ⟨n, hAv⟩ := hAty
  exact (Hd _ _ h₁).2 _ _ h₂ (coRel_cons hr hTA (hAv.isPER.refl _ hx))

/-- The derived rule for an equation: `@Eq.{l} A x y : Prop`. -/
theorem Sem.eqApp {Γ : List VExpr} {A x y : VExpr} {l : VLevel}
    (HA : 𝕋.Sem Γ A A (.sort l)) (Hx : 𝕋.Sem Γ x x A) (Hy : 𝕋.Sem Γ y y A) :
    𝕋.Sem Γ (.app (.app (.app (.const ``Eq [l]) A) x) y)
      (.app (.app (.app (.const ``Eq [l]) A) x) y) (.sort .zero) := by
  have hden : ∀ ρ w, 𝕋.ValOK Γ ρ w →
      𝕋.den ρ (.app (.app (.app (.const ``Eq [l]) A) x) y) =
        𝕋.cand (𝕋.eqCand (𝕋.den ρ A) (𝕋.den ρ x) (𝕋.den ρ y)) := fun ρ w hρ =>
    den_eqApp (HA ρ w hρ).2.2.1 (Hx ρ w hρ).2.2.1 (Hy ρ w hρ).2.2.1
  intro ρ w hρ
  have hm : 𝕋.mem (𝕋.den ρ (.app (.app (.app (.const ``Eq [l]) A) x) y)) (𝕋.El 𝕋.tProp) := by
    rw [hden ρ w hρ]; exact cand_mem_tProp (good_eqCand ..)
  refine ⟨isSemTy_sortDen _, rfl, hm, fun hc => (not_isCand_sortDen _ hc).elim,
    fun ρ' w' hρ' hr => ⟨rfl, ?_⟩⟩
  show 𝕋.Rel 𝕋.tProp _ _
  rw [hden ρ w hρ, hden ρ' w' hρ']
  obtain ⟨-, -, hAm, -, hAr⟩ := HA ρ w hρ
  obtain ⟨-, -, hAm', -, -⟩ := HA ρ' w' hρ'
  obtain ⟨-, -, hxm, -, hxr⟩ := Hx ρ w hρ
  obtain ⟨-, -, hym, -, hyr⟩ := Hy ρ w hρ
  have hv := (mem_sortDen hAm).1
  have hv' := (mem_sortDen hAm').1
  have hT : 𝕋.TyRel (𝕋.den ρ A) (𝕋.den ρ' A) :=
    (tyRel_of_rel_sortDen hAm (hAr ρ' w' hρ' hr).2).2
  have same := hv.tyRel_same hv' hT
  have per := hv.isPER
  have hxx := (hxr ρ' w' hρ' hr).2
  have hyy := (hyr ρ' w' hρ' hr).2
  have hx' := per.mem _ _ hxm hxx
  have hy' := per.mem _ _ hym hyy
  refine rel_tProp_eqCand ?_
  rw [eqCand_nonempty_iff per, eqCand_nonempty_iff hv'.isPER, ← same.1, ← same.2 _ _ hx']
  exact ⟨fun ⟨_, h⟩ => ⟨hx', per.trans _ _ _ hx' (per.symm _ _ hxm hxx)
      (per.trans _ _ _ hxm h hyy)⟩,
    fun ⟨_, h⟩ => ⟨hxm, per.trans _ _ _ hxm hxx (per.trans _ _ _ hx' h (per.symm _ _ hym hyy))⟩⟩

end SetModel
end VEnv.Strengthening
end Lean4Lean
