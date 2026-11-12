import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.EqRecVal

/-! # Reading the head invariant

Inversion of chains (`chain_const_inv`, `chain_step`), the forms of a non-collapsed Π
(`mkPi_eq_tPi`, `mkPi_eq_tPiP`), membership of a tracked spine in its tracked type
(`Chain.mem`) and the fact that an untracked spine denotes `•` (`Chain.none_star`).
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace SetModel
variable {𝕋 : SetModel} {env : VEnv} {ρ : Nat → 𝕋.S} {w : Nat → PVal}

local infix:50 " ∈ₛ " => 𝕋.mem

theorem argsOf_tPi (D : 𝕋.S) (F : 𝕋.S → 𝕋.S) :
    𝕋.argsOf (𝕋.tPi D F) = 𝕋.pair D (𝕋.lam (𝕋.El D) F) := by simp [tPi]

theorem argsOf_tPiP (c : Candidate) (B : 𝕋.S) :
    𝕋.argsOf (𝕋.tPiP c B) = 𝕋.pair (𝕋.enc c) B := by simp [tPiP]

/-- A Π that is a `tPi` has that domain and those fibres. -/
theorem mkPi_eq_tPi {D D' : 𝕋.S} {F F' : 𝕋.S → 𝕋.S} (h : 𝕋.mkPi D F = 𝕋.tPi D' F') :
    D = D' ∧ ¬ 𝕋.IsCand D ∧ ∀ d, d ∈ₛ 𝕋.El D → F d = F' d := by
  have hk : 𝕋.kind (𝕋.mkPi D F) = 𝕋.tagN 4 := by rw [h, kind_tPi]
  unfold mkPi at h hk
  by_cases hDc : 𝕋.IsCand D
  · rw [if_pos hDc] at hk
    by_cases hn : ∃ v, (𝕋.candOf D).mem v
    · rw [if_pos hn] at hk
      by_cases hFc : 𝕋.IsCand (F 𝕋.star)
      · rw [if_pos hFc, kind_cand] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
      · rw [if_neg hFc, kind_tPiP] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
    · rw [if_neg hn, kind_cand] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
  · rw [if_neg hDc] at h hk
    by_cases hall : ∀ d, d ∈ₛ 𝕋.El D → 𝕋.IsCand (F d)
    · rw [if_pos hall, kind_cand] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
    · rw [if_neg hall] at h
      have ha := congrArg 𝕋.argsOf h
      rw [argsOf_tPi, argsOf_tPi] at ha
      obtain ⟨hD, hl⟩ := 𝕋.pair_inj ha
      subst hD
      refine ⟨rfl, hDc, fun d hd => ?_⟩
      have : 𝕋.app (𝕋.lam (𝕋.El D) F) d = 𝕋.app (𝕋.lam (𝕋.El D) F') d := by rw [hl]
      rwa [𝕋.app_lam hd, 𝕋.app_lam hd] at this

/-- A Π that is a `tPiP` is over that inhabited proposition, with that fibre. -/
theorem mkPi_eq_tPiP {D B : 𝕋.S} {c : Candidate} {F : 𝕋.S → 𝕋.S}
    (h : 𝕋.mkPi D F = 𝕋.tPiP c B) :
    D = 𝕋.cand c ∧ (∃ v, c.mem v) ∧ F 𝕋.star = B := by
  have hk : 𝕋.kind (𝕋.mkPi D F) = 𝕋.tagN 5 := by rw [h, kind_tPiP]
  unfold mkPi at h hk
  by_cases hDc : 𝕋.IsCand D
  · rw [if_pos hDc] at h hk
    by_cases hn : ∃ v, (𝕋.candOf D).mem v
    · rw [if_pos hn] at h hk
      by_cases hFc : 𝕋.IsCand (F 𝕋.star)
      · rw [if_pos hFc, kind_cand] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
      · rw [if_neg hFc] at h
        have ha := congrArg 𝕋.argsOf h
        rw [argsOf_tPiP, argsOf_tPiP] at ha
        obtain ⟨hc, hB⟩ := 𝕋.pair_inj ha
        have hc' : 𝕋.candOf D = c := 𝕋.enc_inj hc
        exact ⟨hc' ▸ isCand_eq hDc, hc' ▸ hn, hB⟩
    · rw [if_neg hn, kind_cand] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
  · rw [if_neg hDc] at hk
    by_cases hall : ∀ d, d ∈ₛ 𝕋.El D → 𝕋.IsCand (F d)
    · rw [if_pos hall, kind_cand] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)
    · rw [if_neg hall, kind_tPi] at hk; exact absurd (𝕋.tagN_inj hk) (by decide)

/-- Inversion of the chain of a constant. -/
theorem chain_const_inv {c : Name} {ls : List VLevel} {o : Option 𝕋.S}
    (h : 𝕋.Chain env ρ w (.const c ls) o) :
    ∃ ci, env.constants c = some ci ∧ o = some (𝕋.den ρ (ci.type.instL ls)) := by
  cases h with
  | const hc => exact ⟨_, hc, rfl⟩

/-- **One step of a tracked chain.** If the spine `f x` is tracked at `R`, then `f` is tracked
at some `P`, and whenever `P` is the Π-type `mkPi D G`, the argument is an element of `D`,
its value realizes `D` when `D` is a proposition, and `R` is the fibre at the argument. -/
theorem chain_step {f x : VExpr} {R : 𝕋.S} (h : 𝕋.Chain env ρ w (.app f x) (some R)) :
    ∃ P, 𝕋.Chain env ρ w f (some P) ∧ ∀ D G, P = 𝕋.mkPi D G →
      𝕋.den ρ x ∈ₛ 𝕋.El D ∧ R = G (𝕋.den ρ x) ∧
      (𝕋.IsCand D → (𝕋.candOf D).mem ((pval x).subst w)) := by
  cases h with
  | @appPi _ _ D' F' hc hx =>
    refine ⟨_, hc, fun D G hP => ?_⟩
    obtain ⟨rfl, hDc, hF⟩ := mkPi_eq_tPi hP.symm
    exact ⟨hx, (hF _ hx).symm, fun h => (hDc h).elim⟩
  | @appPiP _ _ c B hc hv hxs =>
    refine ⟨_, hc, fun D G hP => ?_⟩
    obtain ⟨rfl, hne, hF⟩ := mkPi_eq_tPiP hP.symm
    refine ⟨by rw [hxs]; exact star_mem_cand hne, by rw [hxs, hF], fun _ => ?_⟩
    rw [𝕋.candOf_cand]; exact hv

/-- A tracked spine denotes an element of its tracked type, when every constant does. -/
theorem Chain.mem
    (hconst : ∀ c ci ls, env.constants c = some ci → 𝕋.ConstOK c ls (ci.type.instL ls))
    {e : VExpr} {o : Option 𝕋.S} (h : 𝕋.Chain env ρ w e o) :
    ∀ R, o = some R → 𝕋.den ρ e ∈ₛ 𝕋.El R := by
  induction h with
  | const hc => intro R hR; cases hR; exact (hconst _ _ _ hc ρ).1
  | @appPi f x D F _ hx ih =>
    intro R hR
    cases hR
    have hf := ih _ rfl
    show 𝕋.mkApp (𝕋.den ρ f) (𝕋.den ρ x) ∈ₛ _
    rw [mkApp, if_neg (ne_star_of_mem_tPi hf)]
    exact ap_mem_of_mem_tPi hf hx
  | @appPiP f x c B _ _ hxs ih =>
    intro R hR
    cases hR
    have hf := ih _ rfl
    show 𝕋.mkApp (𝕋.den ρ f) (𝕋.den ρ x) ∈ₛ _
    rw [mkApp, if_neg (ne_star_of_mem_tPiP hf), hxs]
    exact ap_mem_of_mem_tPiP hf
  | appStop _ _ _ => intro R hR; cases hR
  | appNone _ _ => intro R hR; cases hR

/-- An untracked spine denotes `•`. -/
theorem Chain.none_star
    (hconst : ∀ c ci ls, env.constants c = some ci → 𝕋.ConstOK c ls (ci.type.instL ls))
    {e : VExpr} {o : Option 𝕋.S} (h : 𝕋.Chain env ρ w e o) :
    o = none → 𝕋.den ρ e = 𝕋.star := by
  induction h with
  | const _ => intro h; cases h
  | appPi _ _ _ => intro h; cases h
  | appPiP _ _ _ _ => intro h; cases h
  | @appStop f x R hc hR _ =>
    intro _
    have hf := hc.mem hconst R rfl
    rw [isCand_eq hR] at hf
    show 𝕋.mkApp (𝕋.den ρ f) _ = _
    rw [(𝕋.mem_El_cand.1 hf).1]; simp [mkApp]
  | @appNone f x _ ih =>
    intro _
    show 𝕋.mkApp (𝕋.den ρ f) _ = _
    rw [ih rfl]; simp [mkApp]

end SetModel
end VEnv.Strengthening
end Lean4Lean
