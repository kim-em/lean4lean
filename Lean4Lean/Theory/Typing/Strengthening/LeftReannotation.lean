import Lean4Lean.Theory.Typing.Strengthening.LambdaReannotation

/-! # Eta-free repair using only the left lambda annotations

The left endpoint stays unchanged. The right endpoint is repaired by borrowing
left lambda annotations, so both endpoints' absence of an extra variable is
preserved syntactically. The reductions and their typings remain in the ambient
context; syntactic scope preservation is not a typing-strengthening theorem.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params

/-- A syntactic record of replacing right lambda domains by their left partners.
Proof-irrelevance leaves may be kept without inspecting their syntax. -/
inductive Reannotates : VExpr → VExpr → VExpr → Prop where
  | keep : Reannotates a b b
  | app : Reannotates f₁ f₂ f₃ → Reannotates a₁ a₂ a₃ →
      Reannotates (.app f₁ a₁) (.app f₂ a₂) (.app f₃ a₃)
  | proj : Reannotates a b c → Reannotates (.proj S i a) (.proj S i b) (.proj S i c)
  | lam : Reannotates b₁ b₂ b₃ → Reannotates (.lam A₁ b₁) (.lam A₂ b₂) (.lam A₁ b₃)
  | forallE : Reannotates A₁ A₂ A₃ → Reannotates B₁ B₂ B₃ →
      Reannotates (.forallE A₁ B₁) (.forallE A₂ B₂) (.forallE A₃ B₃)

/-- Borrowing annotations from two lifts produces a lift and a corresponding
syntactic reannotation below. This statement requires no typing assumptions. -/
theorem Reannotates.lift_inv (H : Reannotates (a.lift' ρ) (b.lift' ρ) out) :
    ∃ c, Reannotates a b c ∧ out = c.lift' ρ := by
  generalize hl : a.lift' ρ = al at H
  generalize hr : b.lift' ρ = br at H
  induction H generalizing ρ a b with
  | keep => exact ⟨b, .keep, hr.symm⟩
  | app _ _ ihf iha =>
    obtain ⟨f₁, a₁, rfl, rfl, rfl⟩ := lift'_eq_app hl
    obtain ⟨f₂, a₂, rfl, rfl, rfl⟩ := lift'_eq_app hr
    obtain ⟨f₃, hf, rfl⟩ := ihf rfl rfl
    obtain ⟨a₃, ha, rfl⟩ := iha rfl rfl
    exact ⟨.app f₃ a₃, .app hf ha, rfl⟩
  | proj _ ih =>
    obtain ⟨a₁, rfl, rfl⟩ := lift'_eq_proj hl
    obtain ⟨a₂, rfl, rfl⟩ := lift'_eq_proj hr
    obtain ⟨a₃, h, rfl⟩ := ih rfl rfl
    exact ⟨_, .proj h, rfl⟩
  | lam _ ih =>
    obtain ⟨A₁, b₁, rfl, rfl, rfl⟩ := lift'_eq_lam hl
    obtain ⟨A₂, b₂, rfl, rfl, rfl⟩ := lift'_eq_lam hr
    obtain ⟨b₃, h, rfl⟩ := ih rfl rfl
    exact ⟨.lam A₁ b₃, .lam h, rfl⟩
  | forallE _ _ ihA ihB =>
    obtain ⟨A₁, B₁, rfl, rfl, rfl⟩ := lift'_eq_forallE hl
    obtain ⟨A₂, B₂, rfl, rfl, rfl⟩ := lift'_eq_forallE hr
    obtain ⟨A₃, hA, rfl⟩ := ihA rfl rfl
    obtain ⟨B₃, hB, rfl⟩ := ihB rfl rfl
    exact ⟨.forallE A₃ B₃, .forallE hA hB, rfl⟩

variable [Params]

/-- An eta-free normal comparison can be repaired with the left endpoint fixed,
using only its displayed lambda domains. The comparison index is retained. -/
theorem normal0_left_reannotation (hΓ : OnCtx Γ (Params.env.IsType univs))
    (H : NormalEqN false n Γ a b) :
    ∃ b', FullReduction Γ b b' ∧ Reannotates a b b' ∧ DomainNormal n Γ a b' := by
  generalize hη : false = η at H
  induction H with
  | refl h => exact ⟨_, .rfl, .keep, .refl h⟩
  | sortDF h1 h2 h3 => exact ⟨_, .rfl, .keep, .sortDF h1 h2 h3⟩
  | constDF h1 h2 h3 h4 h5 => exact ⟨_, .rfl, .keep, .constDF h1 h2 h3 h4 h5⟩
  | appDF hf1 hf2 ha1 ha2 _ _ ihf iha =>
    obtain ⟨_, Rf, Hf, HF⟩ := ihf hΓ hη
    obtain ⟨_, Ra, Ha, HA⟩ := iha hΓ hη
    exact ⟨_, Rf.app Ra, .app Hf Ha,
      .appDF hf1 (Rf.hasType hΓ hf2) ha1 (Ra.hasType hΓ ha2) HF HA⟩
  | projDF hp _ ihm =>
    obtain ⟨_, Rm, Hm, HM⟩ := ihm hΓ hη
    exact ⟨_, Rm.proj, .proj Hm, .projDF hp HM⟩
  | lamDF hA1 hA2 HB ihb =>
    have hΓA : OnCtx (_ :: _) (Params.env.IsType univs) := ⟨hΓ, _, hA1.hasType.1⟩
    obtain ⟨_, hb⟩ := HB.defeq hΓA
    obtain ⟨_, Rb, Hb, HB'⟩ := ihb hΓA hη
    have hA12 := hA1.symm.trans hA2
    have hr := (IsDefEq.lamDF hA12 (hb.hasType.2.defeqDFC henv (.succ .zero hA1))).hasType.2
    have Rb' := Rb.defeqDFC hΓ (.succ .zero hA1) hb.hasType.2
    refine ⟨_, (lambda_reannotation hr).trans (FullReduction.lam .rfl Rb'), .lam Hb, ?_⟩
    simpa only [Nat.zero_add] using
      DomainNormal.lamDF hA1.hasType.2 (.refl hA1.hasType.2) (HB'.defeqDFC (.succ .zero hA1))
  | forallEDF hA1 HA hB1 HB ihA ihB =>
    have hΓA : OnCtx (_ :: _) (Params.env.IsType univs) := ⟨hΓ, _, hA1.hasType.1⟩
    have hA2 := hA1.transU_l henv hΓ (HA.defeq hΓ)
    have hB2 := ((HB.defeq hΓA).of_l henv hΓA hB1).hasType.2
    obtain ⟨_, RA, Ha, HA'⟩ := ihA hΓ hη
    obtain ⟨_, RB, Hb, HB'⟩ := ihB hΓA hη
    exact ⟨_, .forallE RA (RB.defeqDFC hΓ (.succ .zero hA2) hB2), .forallE Ha Hb,
      .forallEDF hA1.hasType.2 HA' (hB1.defeqDFC henv (.succ .zero hA1))
        (HB'.defeqDFC (.succ .zero hA1))⟩
  | etaL | etaR | etaBoth => cases hη
  | proofIrrel hP ha hb => exact ⟨_, .rfl, .keep, .proofIrrel hP ha hb⟩

/-- Eta-free repair of lifted endpoints has lifted final syntax and leaves its
left endpoint fixed. What is missing for strengthening is lowering the right-hand
reannotation reductions and their typing witnesses; this theorem gives them only
in the larger context. -/
theorem normal0_lift_reannotation (hΓ' : OnCtx Γ' (Params.env.IsType univs))
    (H : NormalEqN false n Γ' (a.lift' ρ) (b.lift' ρ)) :
    ∃ b', Reannotates a b b' ∧ FullReduction Γ' (b.lift' ρ) (b'.lift' ρ) ∧
      DomainNormal n Γ' (a.lift' ρ) (b'.lift' ρ) := by
  obtain ⟨out, R, Hshape, Hcert⟩ := normal0_left_reannotation hΓ' H
  obtain ⟨b', Hshape', rfl⟩ := Hshape.lift_inv
  exact ⟨b', Hshape', R, Hcert⟩

end Lean4Lean.VEnv.Strengthening
