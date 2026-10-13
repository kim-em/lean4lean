import Lean4Lean.Theory.Typing.Strengthening.BidirectionalDescent
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta

/-! # Applying common-mode comparisons up to beta reduction

A common-mode comparison cannot be placed directly in an independent function
slot. Applying it to the same typed argument instead gives a finite beta join:
lambda cases contract, eta cases instantiate their body certificate. This is a
local application rule, not arbitrary transitivity or join completeness.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU Params.env univs Γ e1 e2

/-- Homogeneous substitution preserves both mode and index, even when the argument
is a lambda. There is no claim here about substituting two different arguments. -/
theorem BiNormal.instN (hx : Γ₀ ⊢ x : A₀) (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ₂)
    (H : BiNormal mode n Γ₁ a b) : BiNormal mode n Γ₂ (a.inst x k) (b.inst x k) := by
  induction H generalizing k Γ₂ with
  | refl h => exact .refl (h.instN henv W hx)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    exact .appDF (h1.instN henv W hx) (h2.instN henv W hx) (h3.instN henv W hx)
      (h4.instN henv W hx) (ih1 W) (ih2 W)
  | projDF h _ ih => exact .projDF (h.instN henv W hx) (ih W)
  | lamIndependent hA _ _ ihA ihb => exact .lamIndependent (hA.instN henv W hx) (ihA W) (ihb W.succ)
  | lamCommon h1 h2 _ ih => exact .lamCommon (h1.instN henv hx W) (h2.instN henv hx W) (ih W.succ)
  | forallEDF hA _ hB _ ihA ihB =>
    exact .forallEDF (hA.instN henv W hx) (ihA W) (hB.instN henv W.succ hx) (ihB W.succ)
  | etaL hf _ ih =>
    refine .etaL (hf.instN henv W hx) ?_
    have H := ih W.succ
    simp only [inst, instVar, Nat.zero_lt_succ, if_true] at H
    rwa [← lift_instN_lo] at H
  | etaR hf _ ih =>
    refine .etaR (hf.instN henv W hx) ?_
    have H := ih W.succ
    simp only [inst, instVar, Nat.zero_lt_succ, if_true] at H
    rwa [← lift_instN_lo] at H
  | etaBoth hf hg _ ih =>
    refine .etaBoth (hf.instN henv W hx) (hg.instN henv W hx) ?_
    have H := ih W.succ
    simp only [inst, instVar, Nat.zero_lt_succ, if_true] at H
    rwa [← lift_instN_lo, ← lift_instN_lo] at H
  | proofIrrel hP ha hb => exact .proofIrrel (hP.instN henv W hx) (ha.instN henv W hx) (hb.instN henv W hx)
  | promote _ ih => exact .promote (ih W)

/-- A finite beta join ending in a mode-indexed comparison. -/
def BiBetaJoin (mode : Bool) (Γ : List VExpr) (a b : VExpr) : Prop :=
  ∃ a' b' n, BetaRed a a' ∧ BetaRed b b' ∧ BiNormal mode n Γ a' b'

/-- Applying an independent comparison directly preserves a common-mode argument
comparison. This requires no lambda restriction on either function. -/
theorem BiNormal.apply_independent (hf : Γ ⊢ f : .forallE A B) (hg : Γ ⊢ g : .forallE A B)
    (ha : Γ ⊢ a : A) (hb : Γ ⊢ b : A) (Hf : BiNormal false nf Γ f g)
    (Ha : BiNormal true na Γ a b) : BiBetaJoin true Γ (.app f a) (.app g b) :=
  ⟨_, _, _, .refl, .refl, .appDF hf hg ha hb Hf Ha⟩

private theorem argument_at_other_domain (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hf : Γ ⊢ f : .forallE A B) (hf' : Γ ⊢ f : .forallE D C) (hx : Γ ⊢ x : A) : Γ ⊢ x : D := by
  obtain ⟨⟨_, hAD⟩, _⟩ := (hf.uniqU henv hΓ hf').forallE_inv henv hΓ
  exact hAD.defeq hx

/-- A common-mode function comparison can be applied to the same typed argument
by contracting its displayed lambda redexes and instantiating eta-body certificates.
This rule avoids coercing an eta comparison into independent mode. -/
theorem BiNormal.apply_same_arg (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hf : Γ ⊢ f : .forallE A B) (hg : Γ ⊢ g : .forallE A B) (hx : Γ ⊢ x : A)
    (H : BiNormal true n Γ f g) : BiBetaJoin true Γ (.app f x) (.app g x) := by
  cases H with
  | refl _ => exact ⟨_, _, _, .refl, .refl, .refl (HasType.app hf hx)⟩
  | sortDF h1 h2 h3 => exact BiNormal.apply_independent hf hg hx hx (.sortDF h1 h2 h3) (.refl hx)
  | constDF h1 h2 h3 h4 h5 => exact BiNormal.apply_independent hf hg hx hx (.constDF h1 h2 h3 h4 h5) (.refl hx)
  | appDF h1 h2 h3 h4 Hf Ha => exact BiNormal.apply_independent hf hg hx hx (.appDF h1 h2 h3 h4 Hf Ha) (.refl hx)
  | projDF h Hm => exact BiNormal.apply_independent hf hg hx hx (.projDF h Hm) (.refl hx)
  | forallEDF hA HA hB HB => exact BiNormal.apply_independent hf hg hx hx (.forallEDF hA HA hB HB) (.refl hx)
  | proofIrrel hP ha hb => exact BiNormal.apply_independent hf hg hx hx (.proofIrrel hP ha hb) (.refl hx)
  | promote H => exact BiNormal.apply_independent hf hg hx hx H (.refl hx)
  | lamCommon hD1 _ HB =>
    have hΓD : OnCtx (_ :: _) (Params.env.IsType univs) := ⟨hΓ, _, hD1.hasType.1⟩
    obtain ⟨_, hb⟩ := HB.defeq hΓD
    have hfD := (IsDefEq.lamDF hD1 hb.hasType.1).hasType.2
    have hxD := argument_at_other_domain hΓ hf hfD hx
    exact ⟨_, _, _, .beta, .beta, HB.instN hxD .zero⟩
  | etaL hgD HB =>
    have hxD := argument_at_other_domain hΓ hg hgD hx
    have HB' := HB.instN hxD .zero
    simp only [inst, instVar_zero, inst_lift] at HB'
    exact ⟨_, _, _, .beta, .refl, HB'⟩
  | etaR hfD HB =>
    have hxD := argument_at_other_domain hΓ hf hfD hx
    have HB' := HB.instN hxD .zero
    simp only [inst, instVar_zero, inst_lift] at HB'
    exact ⟨_, _, _, .refl, .beta, HB'⟩
  | etaBoth hfD _ HB =>
    have hxD := argument_at_other_domain hΓ hf hfD hx
    have HB' := HB.instN hxD .zero
    simp only [inst, instVar_zero, inst_lift] at HB'
    exact ⟨_, _, _, .refl, .refl, HB'⟩

/-- Beta joins of lifted endpoints descend in either comparison mode. The endpoint
typings of the lowered reducts follow from beta subject reduction. -/
theorem BiBetaJoin.descend (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ' : OnCtx Γ' (Params.env.IsType univs)) (W : Ctx.Lift' ρ Γ Γ')
    (ha : Γ ⊢ a : A) (hb : Γ ⊢ b : B) (H : BiBetaJoin mode Γ' (a.lift' ρ) (b.lift' ρ))
    (hmode : if mode then Γ ⊢ A ≡ B else ¬ IsProof Γ a) : Γ ⊢ a ≡ b := by
  obtain ⟨a', b', n, Ra, Rb, HC⟩ := H
  obtain ⟨a₀, Ra₀, rfl⟩ := betaRed_lift_inv Ra
  obtain ⟨b₀, Rb₀, rfl⟩ := betaRed_lift_inv Rb
  have hAA := Ra₀.simAt henv.orderedStrong henv.betaSubjectReduction hΓ A ha
  have hBB := Rb₀.simAt henv.orderedStrong henv.betaSubjectReduction hΓ B hb
  have hm : if mode then Γ ⊢ A ≡ B else ¬ IsProof Γ a₀ := by
    cases mode with
    | true => exact hmode
    | false =>
      rintro ⟨P, ht, hP⟩
      exact hmode ⟨P, ((show Γ ⊢ a₀ ≡ a from ⟨_, hAA.symm⟩).of_l henv hΓ ht).hasType.2, hP⟩
  have H₀ := BiNormal.descend n W hΓ hΓ' hAA.hasType.2 hBB.hasType.2 HC hm
  exact (show Γ ⊢ a ≡ a₀ from ⟨_, hAA⟩).trans henv hΓ (H₀.trans henv hΓ ⟨_, hBB.symm⟩)

end Lean4Lean.VEnv.Strengthening
