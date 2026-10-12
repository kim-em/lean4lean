import Lean4Lean.Theory.Typing.ChurchRosser
import Lean4Lean.Theory.Typing.UniqueTyping

/-! # Heterogeneous substitution into a normal equality

`NormalEqF.instN_lr`: substituting two normally equal terms `e₀ ≡ₚ e₀'` for a variable on the
two sides of a normal equality `e₁ ≡ₚ e₂` gives a normal equality `e₁[e₀] ≡ₚ e₂[e₀']`, in the
context instantiated with `e₀`. The library has the homogeneous substitution
`NormalEqN.instN` (one term on both sides) and the right substitution `NormalEqF.instN_r` (two
terms into one typed term); this is their combination, by induction on the derivation of
`e₁ ≡ₚ e₂`, every typing premise of a right-hand term being retyped through `instN_r` on the
term or on its type.

Use (route B's analysis of the normal-equality descent, agent A's `NormalDescent`): a matched
pair of head β-redexes `(λ A₁. s₁) x ≡ₚ (λ A₂. s₂) y` whose arguments `x y` are proofs of a
proposition contracts to `s₁[x] ≡ₚ s₂[y]` (`NormalEqF.contract_proofArgs`), so such pairs do
not obstruct the descent: the comparison index may grow, but the proof-erased size of the pair
strictly drops. The comparison index is not preserved in general (the `refl` leaves containing
the variable become congruence derivations), which is why the result is stated for `NormalEqF`
and not for `NormalEqN` at a fixed index. -/

namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean.VExpr Params

variable [Params]

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≡ₚ{" b "}[" n "] " e2:30 => NormalEqN b n Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≡ₚ{" b "}" e2:30 => NormalEqF b Γ e1 e2

/-- A term substituted on the right is typed, in the left-instantiated context, at the
left-instantiated type: the two instances are normally equal (`NormalEqF.instN_r`). -/
theorem retype_instN_r (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (h₀ : Γ₀ ⊢ e₀ : A₀)
    (H' : Γ₀ ⊢ e₀ ≡ₚ{η} e₀') (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (h : Γ₁ ⊢ e : T) :
    Γ ⊢ e.inst e₀' k : T.inst e₀ k := by
  have hΓ := (W.wf henv.ordered h₀ hΓ₁).2
  have hee := (NormalEqF.instN_r hΓ₁ h₀ H' W h).defeq hΓ
  exact (h.instN henv.ordered W h₀).defeqU_l henv hΓ hee

/-- **Heterogeneous substitution.** -/
theorem NormalEqF.instN_lr (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (h₀ : Γ₀ ⊢ e₀ : A₀)
    (H' : Γ₀ ⊢ e₀ ≡ₚ{η} e₀') (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ)
    (H : Γ₁ ⊢ e1 ≡ₚ{η}[n] e2) : Γ ⊢ e1.inst e₀ k ≡ₚ{η} e2.inst e₀' k := by
  induction H generalizing Γ k with
  | refl h => exact NormalEqF.instN_r hΓ₁ h₀ H' W h
  | sortDF h1 h2 h3 => exact ⟨_, .sortDF h1 h2 h3⟩
  | constDF h1 h2 h3 h4 h5 => exact ⟨_, .constDF h1 h2 h3 h4 h5⟩
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    obtain ⟨_, D1⟩ := ih1 hΓ₁ H' W
    obtain ⟨_, D2⟩ := ih2 hΓ₁ H' W
    exact ⟨_, .appDF (h1.instN henv.ordered W h₀) (retype_instN_r hΓ₁ h₀ H' W h2)
      (h3.instN henv.ordered W h₀) (retype_instN_r hΓ₁ h₀ H' W h4) D1 D2⟩
  | projDF hproj _ ih =>
    obtain ⟨_, D⟩ := ih hΓ₁ H' W
    exact ⟨_, .projDF (hproj.instN henv.ordered W h₀) D⟩
  | @lamDF Γ₁ A A₁ u A₂ b n body₁ body₂ h1 h2 _ ih =>
    have hΓ := (W.wf henv.ordered h₀ hΓ₁).2
    have hΓ₁' : OnCtx (A :: Γ₁) (env.IsType univs) := ⟨hΓ₁, _, h1.hasType.1⟩
    obtain ⟨_, D⟩ := ih hΓ₁' H' W.succ
    have e1 : Γ ⊢ A.inst e₀ k ≡ A₁.inst e₀ k : .sort u := h1.instN henv.ordered h₀ W
    have e2 : Γ ⊢ A.inst e₀ k ≡ A₂.inst e₀ k : .sort u := h2.instN henv.ordered h₀ W
    have e3 : Γ ⊢ A₂.inst e₀ k ≡ A₂.inst e₀' k : .sort u :=
      ((NormalEqF.instN_r hΓ₁ h₀ H' W h2.hasType.2).defeq hΓ).of_l henv hΓ
        (h2.hasType.2.instN henv.ordered W h₀)
    exact ⟨_, .lamDF e1 (e2.trans e3) D⟩
  | @forallEDF Γ₁ A A₁ u A₂ b n₁ B₁ v n₂ B₂ h1 _ h3 _ ihA ihB =>
    have hΓ₁' : OnCtx (A :: Γ₁) (env.IsType univs) := ⟨hΓ₁, _, h1.hasType.1⟩
    obtain ⟨_, DA⟩ := ihA hΓ₁ H' W
    obtain ⟨_, DB⟩ := ihB hΓ₁' H' W.succ
    exact ⟨_, .forallEDF (h1.instN henv.ordered h₀ W) DA (h3.instN henv.ordered W.succ h₀) DB⟩
  | etaL h1 _ ih =>
    have hΓ₁' : OnCtx (_ :: _) (env.IsType univs) :=
      ⟨hΓ₁, ((h1.isType henv.ordered hΓ₁).forallE_inv henv.ordered).1⟩
    obtain ⟨_, D⟩ := ih hΓ₁' H' W.succ
    simp only [inst, instVar, Nat.zero_lt_succ, if_true] at D; rw [← lift_instN_lo] at D
    exact ⟨_, .etaL (retype_instN_r hΓ₁ h₀ H' W h1) D⟩
  | @etaR Γ₁ e' A B _ _ h1 _ ih =>
    have hΓ := (W.wf henv.ordered h₀ hΓ₁).2
    obtain ⟨u, hAB⟩ := h1.isType henv.ordered hΓ₁
    obtain ⟨w, hA'⟩ := (hAB.forallE_inv henv.ordered).1
    have hΓ₁' : OnCtx (A :: Γ₁) (env.IsType univs) := ⟨hΓ₁, _, hA'⟩
    obtain ⟨_, D⟩ := ih hΓ₁' H' W.succ
    have hAA : Γ ⊢ A.inst e₀ k ≡ A.inst e₀' k : .sort w :=
      ((NormalEqF.instN_r hΓ₁ h₀ H' W hA').defeq hΓ).of_l henv hΓ (hA'.instN henv.ordered W h₀)
    have hTT := (NormalEqF.instN_r hΓ₁ h₀ H' W hAB).defeq hΓ
    have he' : Γ ⊢ e'.inst e₀ k : .forallE (A.inst e₀' k) (B.inst e₀' (k + 1)) :=
      (h1.instN henv.ordered W h₀).defeqU_r henv hΓ hTT
    have D' := NormalEqN.defeqDFC hΓ (.succ .zero hAA) D
    simp only [inst, instVar, Nat.zero_lt_succ, if_true] at D'; rw [← lift_instN_lo] at D'
    exact ⟨_, .etaR he' D'⟩
  | etaBoth h1 h2 _ ih =>
    have hΓ₁' : OnCtx (_ :: _) (env.IsType univs) :=
      ⟨hΓ₁, ((h1.isType henv.ordered hΓ₁).forallE_inv henv.ordered).1⟩
    obtain ⟨_, D⟩ := ih hΓ₁' H' W.succ
    simp only [inst, instVar, Nat.zero_lt_succ, if_true] at D; rw [← lift_instN_lo, ← lift_instN_lo] at D
    exact ⟨_, .etaBoth (h1.instN henv.ordered W h₀) (retype_instN_r hΓ₁ h₀ H' W h2) D⟩
  | proofIrrel h1 h2 h3 =>
    exact ⟨_, .proofIrrel (h1.instN henv.ordered W h₀) (h2.instN henv.ordered W h₀)
      (retype_instN_r hΓ₁ h₀ H' W h3)⟩

/-- **Contraction of a matched β-redex pair with proof arguments.** Bodies normally equal under
a binder of a proposition `A`, and two proofs `x y : A`, give normally equal contracta. With
`x ≡ₚ y` by `proofIrrel`, this is `instN_lr` at depth `0`. In the descent of a normal equality
between lifts (route B's analysis), this replaces the pair `(λ A. s₁) x ≡ₚ (λ A'. s₂) y`, whose
lambdas have no common type, by `s₁[x] ≡ₚ s₂[y]` at the common type of the redexes; the
proof-erased size of the pair strictly drops. -/
theorem NormalEqF.contract_proofArgs (hΓ : OnCtx Γ (env.IsType univs))
    (hA : Γ ⊢ A : .sort .zero) (hx : Γ ⊢ x : A) (hy : Γ ⊢ y : A)
    (H : A :: Γ ⊢ s₁ ≡ₚ{η} s₂) : Γ ⊢ s₁.inst x ≡ₚ{η} s₂.inst y := by
  obtain ⟨_, H⟩ := H
  have hΓ' : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  exact NormalEqF.instN_lr hΓ' hx ⟨_, .proofIrrel hA hx hy⟩ .zero H

/-- The same for arguments that are normally equal (not necessarily proofs). -/
theorem NormalEqF.contract (hΓ : OnCtx Γ (env.IsType univs))
    (hA : Γ ⊢ A : .sort u) (hx : Γ ⊢ x : A) (Hxy : Γ ⊢ x ≡ₚ{η} y)
    (H : A :: Γ ⊢ s₁ ≡ₚ{η} s₂) : Γ ⊢ s₁.inst x ≡ₚ{η} s₂.inst y := by
  obtain ⟨_, H⟩ := H
  have hΓ' : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  exact NormalEqF.instN_lr hΓ' hx Hxy .zero H

end Lean4Lean.VEnv.Strengthening
