import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.Extra

/-! # Soundness: the value of `Eq.rec`

`recVal = λ α a M m b h. case h m bot` realizes the declared type of `Eq.rec` whenever that
type denotes a proposition. Applied to six values it reduces to `case h m bot`; if the major
`h` reduces to `r` it realizes `eqCand α a b` only when the endpoints are identical, so the
minor's value realizes the fibre; otherwise the result is `bot`, which realizes the inhabited
fibre.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

/-- `recVal` applied to six values reduces to the case on the major. -/
theorem recVal_steps (u1 u2 u3 u4 u5 u6 : PVal) :
    PVal.Steps (.app (.app (.app (.app (.app (.app recVal u1) u2) u3) u4) u5) u6)
      (.case u6 u4 .bot) := by
  simp only [recVal]
  refine .head (.appL (.appL (.appL (.appL (.appL .beta))))) ?_
  refine .head (.appL (.appL (.appL (.appL .beta)))) ?_
  refine .head (.appL (.appL (.appL .beta))) ?_
  refine .head (.appL (.appL .beta)) ?_
  refine .head (.appL .beta) ?_
  refine .head .beta ?_
  simp [PVal.inst, PVal.liftN_zero, PVal.inst_liftN]
  exact .rfl

namespace SetModel
variable {𝕋 : SetModel}

local infix:50 " ∈ₛ " => 𝕋.mem

/-- The case on the major realizes the fibre over `b`. -/
theorem case_realizes {u v : VLevel} {α a M m b : 𝕋.S} (H : 𝕋.RecArgs u v α a M m b)
    {u4 u6 : PVal} (hc : 𝕋.IsCand (𝕋.Fib M b))
    (hu4 : 𝕋.IsCand (𝕋.Fib M a) → (𝕋.candOf (𝕋.Fib M a)).mem u4)
    (hu6 : (𝕋.eqCand α a b).mem u6) :
    (𝕋.candOf (𝕋.Fib M b)).mem (.case u6 u4 .bot) := by
  have hbot : (𝕋.candOf (𝕋.Fib M b)).mem .bot := by
    have hm := H.minor_mem
    have hv := H.fib_b_valid
    rw [isCand_eq hc] at hm hv
    exact good_bot_mem hv.good (𝕋.mem_El_cand.1 hm).2
  have toBot : PVal.ToBot u6 → (𝕋.candOf (𝕋.Fib M b)).mem (.case u6 u4 .bot) := fun h =>
    ((𝕋.candOf _).steps ((PVal.Steps.caseS h).trans (.single .caseBot))).2 hbot
  unfold eqCand at hu6
  by_cases h1 : a ∈ₛ 𝕋.El α ∧ a = b
  · rw [if_pos h1] at hu6
    rcases hu6 with hr | hb
    · obtain ⟨-, rfl⟩ := h1
      exact ((𝕋.candOf _).steps ((PVal.Steps.caseS hr).trans (.single .caseR))).2 (hu4 hc)
    · exact toBot hb
  · rw [if_neg h1] at hu6
    by_cases h2 : a ∈ₛ 𝕋.El α ∧ 𝕋.Rel α a b
    · rw [if_pos h2] at hu6; exact toBot hu6
    · rw [if_neg h2] at hu6; exact hu6.elim

/-- **The value of `Eq.rec` realizes its declared type.** -/
theorem recVal_realizes (v u : VLevel) (ρ : Nat → 𝕋.S)
    (hc : 𝕋.IsCand (𝕋.den ρ (recTy v u))) :
    (𝕋.candOf (𝕋.den ρ (recTy v u))).mem recVal := by
  have hc1 : 𝕋.IsCand (𝕋.mkPi (𝕋.den ρ (rA1 u)) fun x1 => 𝕋.den (𝕋.cons x1 ρ)
      (.forallE rA2 (.forallE (rA3 v u) (.forallE (rA4 u) (.forallE rA5
        (.forallE (rA6 u) rR)))))) := hc
  show (𝕋.candOf (𝕋.mkPi _ _)).mem _
  refine lam_val_mem hc1 fun α hα u1 _ hc2 => ?_
  show (𝕋.candOf (𝕋.mkPi _ _)).mem _
  refine lam_val_mem hc2 fun a ha u2 _ hc3 => ?_
  show (𝕋.candOf (𝕋.mkPi _ _)).mem _
  refine lam_val_mem hc3 fun M hM u3 _ hc4 => ?_
  show (𝕋.candOf (𝕋.mkPi _ _)).mem _
  refine lam_val_mem hc4 fun m hm u4 hu4 hc5 => ?_
  show (𝕋.candOf (𝕋.mkPi _ _)).mem _
  refine lam_val_mem hc5 fun b hb u5 _ hc6 => ?_
  show (𝕋.candOf (𝕋.mkPi _ _)).mem _
  refine lam_val_mem hc6 fun t ht u6 hu6 hc7 => ?_
  -- the semantic facts about the six arguments
  have hα' : α ∈ₛ 𝕋.El (𝕋.sortDen u) := hα
  have ha' : a ∈ₛ 𝕋.El α := ha
  have h3 : 𝕋.den (𝕋.cons a (𝕋.cons α ρ)) (rA3 v u) = 𝕋.motiveTy v α a :=
    den_motiveOf (ρ := 𝕋.cons a (𝕋.cons α ρ)) (α := .bvar 1) (a := .bvar 0) hα' ha'
  rw [h3] at hM
  have h4 : 𝕋.den (𝕋.cons M (𝕋.cons a (𝕋.cons α ρ))) (rA4 u) = 𝕋.Fib M a := by
    show 𝕋.mkApp (𝕋.mkApp M a) (𝕋.den _ (reflS u (.bvar 2) (.bvar 1))) = _
    rw [den_reflS]; rfl
  rw [h4] at hm hu4
  have hb' : b ∈ₛ 𝕋.El α := hb
  have h6 : 𝕋.den (𝕋.cons b (𝕋.cons m (𝕋.cons M (𝕋.cons a (𝕋.cons α ρ))))) (rA6 u) =
      𝕋.cand (𝕋.eqCand α a b) :=
    den_eqApp (ρ := 𝕋.cons b (𝕋.cons m (𝕋.cons M (𝕋.cons a (𝕋.cons α ρ)))))
      (A := .bvar 4) (x := .bvar 3) (y := .bvar 0) hα' ha' hb'
  rw [h6] at ht hu6
  obtain ⟨hts, hne⟩ := 𝕋.mem_El_cand.1 ht
  have hαv := (mem_sortDen hα').1
  have H : 𝕋.RecArgs u v α a M m b :=
    ⟨hα', ha', hM, hm, hb', ((eqCand_nonempty_iff hαv.isPER).1 hne).2⟩
  have hR : 𝕋.den (𝕋.cons t (𝕋.cons b (𝕋.cons m (𝕋.cons M (𝕋.cons a (𝕋.cons α ρ)))))) rR =
      𝕋.Fib M b := by
    show 𝕋.mkApp (𝕋.mkApp M b) t = _
    rw [hts]; rfl
  rw [hR] at hc7 ⊢
  have hu6' : (𝕋.eqCand α a b).mem u6 := by
    have := hu6 ⟨_, rfl⟩
    rwa [𝕋.candOf_cand] at this
  exact ((𝕋.candOf _).steps (recVal_steps u1 u2 u3 u4 u5 u6)).2 (case_realizes H hc7 hu4 hu6')

end SetModel
end VEnv.Strengthening
end Lean4Lean
