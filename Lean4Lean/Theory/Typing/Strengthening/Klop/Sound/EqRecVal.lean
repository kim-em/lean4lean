import Lean4Lean.Theory.Typing.Strengthening.Klop.Sound.KlopDefs

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
variable {𝕊 : SetModel}

local infix:50 " ∈ₛ " => 𝕊.mem

/-- The case on the major realizes the fibre over `b`. -/
theorem case_realizes {u v : VLevel} {α a M m b : 𝕊.S} (H : 𝕊.RecArgs u v α a M m b)
    {u4 u6 : PVal} (hc : 𝕊.IsCand (𝕊.Fib M b))
    (hu4 : 𝕊.IsCand (𝕊.Fib M a) → (𝕊.candOf (𝕊.Fib M a)).mem u4)
    (hu6 : (𝕊.eqCand α a b).mem u6) :
    (𝕊.candOf (𝕊.Fib M b)).mem (.case u6 u4 .bot) := by
  have hbot : (𝕊.candOf (𝕊.Fib M b)).mem .bot := by
    have hm := H.minor_mem
    have hv := H.fib_b_valid
    rw [isCand_eq hc] at hm hv
    exact good_bot_mem hv.good (𝕊.mem_El_cand.1 hm).2
  have toBot : PVal.ToBot u6 → (𝕊.candOf (𝕊.Fib M b)).mem (.case u6 u4 .bot) := fun h =>
    ((𝕊.candOf _).steps ((PVal.Steps.caseS h).trans (.single .caseBot))).2 hbot
  unfold eqCand at hu6
  by_cases h1 : a ∈ₛ 𝕊.El α ∧ a = b
  · rw [if_pos h1] at hu6
    rcases hu6 with hr | hb
    · obtain ⟨-, rfl⟩ := h1
      exact ((𝕊.candOf _).steps ((PVal.Steps.caseS hr).trans (.single .caseR))).2 (hu4 hc)
    · exact toBot hb
  · rw [if_neg h1] at hu6
    by_cases h2 : a ∈ₛ 𝕊.El α ∧ 𝕊.Rel α a b
    · rw [if_pos h2] at hu6; exact toBot hu6
    · rw [if_neg h2] at hu6; exact hu6.elim

/-- **The value of `Eq.rec` realizes its declared type.** -/
theorem recVal_realizes (v u : VLevel) (ρ : Nat → 𝕊.S)
    (hc : 𝕊.IsCand (𝕊.den ρ (recTy v u))) :
    (𝕊.candOf (𝕊.den ρ (recTy v u))).mem recVal := by
  have hc1 : 𝕊.IsCand (𝕊.mkPi (𝕊.den ρ (rA1 u)) fun x1 => 𝕊.den (𝕊.cons x1 ρ)
      (.forallE rA2 (.forallE (rA3 v u) (.forallE (rA4 u) (.forallE rA5
        (.forallE (rA6 u) rR)))))) := hc
  show (𝕊.candOf (𝕊.mkPi _ _)).mem _
  refine lam_val_mem hc1 fun α hα u1 _ hc2 => ?_
  show (𝕊.candOf (𝕊.mkPi _ _)).mem _
  refine lam_val_mem hc2 fun a ha u2 _ hc3 => ?_
  show (𝕊.candOf (𝕊.mkPi _ _)).mem _
  refine lam_val_mem hc3 fun M hM u3 _ hc4 => ?_
  show (𝕊.candOf (𝕊.mkPi _ _)).mem _
  refine lam_val_mem hc4 fun m hm u4 hu4 hc5 => ?_
  show (𝕊.candOf (𝕊.mkPi _ _)).mem _
  refine lam_val_mem hc5 fun b hb u5 _ hc6 => ?_
  show (𝕊.candOf (𝕊.mkPi _ _)).mem _
  refine lam_val_mem hc6 fun t ht u6 hu6 hc7 => ?_
  -- the semantic facts about the six arguments
  have hα' : α ∈ₛ 𝕊.El (𝕊.sortDen u) := hα
  have ha' : a ∈ₛ 𝕊.El α := ha
  have h3 : 𝕊.den (𝕊.cons a (𝕊.cons α ρ)) (rA3 v u) = 𝕊.motiveTy v α a :=
    den_motiveOf (ρ := 𝕊.cons a (𝕊.cons α ρ)) (α := .bvar 1) (a := .bvar 0) hα' ha'
  rw [h3] at hM
  have h4 : 𝕊.den (𝕊.cons M (𝕊.cons a (𝕊.cons α ρ))) (rA4 u) = 𝕊.Fib M a := by
    show 𝕊.mkApp (𝕊.mkApp M a) (𝕊.den _ (reflS u (.bvar 2) (.bvar 1))) = _
    rw [den_reflS]; rfl
  rw [h4] at hm hu4
  have hb' : b ∈ₛ 𝕊.El α := hb
  have h6 : 𝕊.den (𝕊.cons b (𝕊.cons m (𝕊.cons M (𝕊.cons a (𝕊.cons α ρ))))) (rA6 u) =
      𝕊.cand (𝕊.eqCand α a b) :=
    den_eqApp (ρ := 𝕊.cons b (𝕊.cons m (𝕊.cons M (𝕊.cons a (𝕊.cons α ρ)))))
      (A := .bvar 4) (x := .bvar 3) (y := .bvar 0) hα' ha' hb'
  rw [h6] at ht hu6
  obtain ⟨hts, hne⟩ := 𝕊.mem_El_cand.1 ht
  have hαv := (mem_sortDen hα').1
  have H : 𝕊.RecArgs u v α a M m b :=
    ⟨hα', ha', hM, hm, hb', ((eqCand_nonempty_iff hαv.isPER).1 hne).2⟩
  have hR : 𝕊.den (𝕊.cons t (𝕊.cons b (𝕊.cons m (𝕊.cons M (𝕊.cons a (𝕊.cons α ρ)))))) rR =
      𝕊.Fib M b := by
    show 𝕊.mkApp (𝕊.mkApp M b) t = _
    rw [hts]; rfl
  rw [hR] at hc7 ⊢
  have hu6' : (𝕊.eqCand α a b).mem u6 := by
    have := hu6 ⟨_, rfl⟩
    rwa [𝕊.candOf_cand] at this
  exact ((𝕊.candOf _).steps (recVal_steps u1 u2 u3 u4 u5 u6)).2 (case_realizes H hc7 hu4 hu6')

end SetModel
end VEnv.Strengthening
end Lean4Lean
