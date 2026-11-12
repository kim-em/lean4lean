import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.SoundLam

/-! # Soundness: β and proof irrelevance -/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace SetModel
variable {𝕋 : SetModel}

/-- The β rule (`IsDefEqStrong.beta`). -/
theorem Sem.beta {Γ : List VExpr} {A B e e' : VExpr} {u : VLevel}
    (HA : 𝕋.Sem Γ A A (.sort u)) (He : 𝕋.Sem (A :: Γ) e e B) (He' : 𝕋.Sem Γ e' e' A)
    (Hr : 𝕋.Sem Γ (e.inst e') (e.inst e') (B.inst e')) :
    𝕋.Sem Γ (.app (.lam A e) e') (e.inst e') (B.inst e') := by
  have hβ : ∀ ρ w, 𝕋.ValOK Γ ρ w →
      𝕋.den ρ (.app (.lam A e) e') = 𝕋.den ρ (e.inst e') := fun ρ w hρ =>
    𝕋.den_beta A e e' ρ (He' ρ w hρ).2.2.1
  intro ρ w hρ
  obtain ⟨hty, -, hm, hv, hr⟩ := Hr ρ w hρ
  obtain ⟨-, -, hAm, -, -⟩ := HA ρ w hρ
  have hAty : 𝕋.IsSemTy (𝕋.den ρ A) := isSemTy_of_mem_sortDen hAm
  obtain ⟨-, -, he'm, he'v, -⟩ := He' ρ w hρ
  refine ⟨hty, hβ ρ w hρ, (hβ ρ w hρ) ▸ hm, fun hc => ⟨?_, (hv hc).2⟩, fun ρ' w' hρ' hrr => ?_⟩
  · -- the value of the redex expands the value of the body at the extended valuation
    have hval := valOK_cons hρ hAty he'm fun h => (he'v h).1
    have hc' : 𝕋.IsCand (𝕋.den (𝕋.cons (𝕋.den ρ e') ρ) B) := by rw [← 𝕋.den_inst0]; exact hc
    have hb := ((He _ _ hval).2.2.2.1 hc').1
    rw [𝕋.den_inst0]
    exact ((𝕋.candOf _).step (PVal.step_lam_app e A w _)).2 hb
  · obtain ⟨h1, h2⟩ := hr ρ' w' hρ' hrr
    refine ⟨h1, ?_⟩
    rw [hβ ρ w hρ, hβ ρ' w' hρ']
    exact h2

/-- Proof irrelevance (`IsDefEqStrong.proofIrrel`). -/
theorem Sem.proofIrrel {Γ : List VExpr} {p h h' : VExpr}
    (Hp : 𝕋.Sem Γ p p (.sort .zero)) (Hh : 𝕋.Sem Γ h h p) (Hh' : 𝕋.Sem Γ h' h' p) :
    𝕋.Sem Γ h h' p := by
  intro ρ w hρ
  obtain ⟨-, -, hpm, -, -⟩ := Hp ρ w hρ
  obtain ⟨c, -, hc⟩ := mem_El_tProp.1 (show 𝕋.mem (𝕋.den ρ p) (𝕋.El 𝕋.tProp) from hpm)
  obtain ⟨hty, -, hm, hv, hr⟩ := Hh ρ w hρ
  obtain ⟨-, -, hm', hv', -⟩ := Hh' ρ w hρ
  refine ⟨hty, ?_, hm, fun hcd => ⟨(hv hcd).1, (hv' hcd).1⟩, hr⟩
  rw [hc] at hm hm'
  rw [(𝕋.mem_El_cand.1 hm).1, (𝕋.mem_El_cand.1 hm').1]

end SetModel
end VEnv.Strengthening
end Lean4Lean
