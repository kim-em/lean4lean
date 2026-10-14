import Lean4Lean.Theory.Typing.Strengthening.EtaLambdaExposure

/-! # Head beta contraction commutes with finite typed eta

A single head beta step moves before eta as at most one head step. The step
vanishes when it consumes a lambda introduced by function eta. In particular
head beta preserves eta expansion from an existing constant spine.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params

/-- One beta contraction on the function spine, never inside an argument. -/
inductive HeadBetaStep : VExpr → VExpr → Prop where
  | beta : HeadBetaStep (.app (.lam A b) a) (b.inst a)
  | appL : HeadBetaStep f f' → HeadBetaStep (.app f a) (.app f' a)

/-- Finite head beta computation. -/
abbrev HeadBetaRed := ReflTransGen HeadBetaStep

theorem HeadBetaStep.toBeta (R : HeadBetaStep a b) : BetaRed a b := by
  induction R with
  | beta => exact .beta
  | appL _ ih => exact .app ih .refl

theorem HeadBetaRed.toBeta (R : HeadBetaRed a b) : BetaRed a b := by
  induction R with
  | rfl => exact .refl
  | tail _ R ih => exact ih.trans R.toBeta

theorem HeadBetaStep.mkApps (R : HeadBetaStep f f') (args : List VExpr) :
    HeadBetaStep (mkApps f args) (mkApps f' args) := by
  induction args generalizing f f' with
  | nil => exact R
  | cons _ _ ih => exact ih (.appL R)

/-- A literal constant spine has no head beta step, even when arguments reduce. -/
theorem HeadBetaStep.not_constant_spine (R : HeadBetaStep (VExpr.mkApps (.const c ls) args) out) : False := by
  generalize hsrc : VExpr.mkApps (.const c ls) args = source at R
  induction R generalizing args with
  | beta =>
    have h := congrArg getAppFn hsrc
    simp only [getAppFn_mkApps, getAppFn] at h
    cases h
  | appL R ih =>
    obtain ⟨args0, _, he⟩ := RigidHead.const.mkApps_eq_app hsrc
    exact ih he.symm

variable [Params]

/-- Exchange a root beta redex with eta paths in its function and argument,
retaining at most one actual head contraction of the original application. -/
theorem eta_function_headBeta (hΓ : OnCtx Γ (env.IsType univs))
    (RF : TypedEtaExpansion Γ f (.lam A b)) (RA : TypedEtaExpansion Γ a a')
    (ht : env.HasType univs Γ (.app f a) T) :
    ∃ out, (out = .app f a ∨ HeadBetaStep (.app f a) out) ∧
      TypedEtaExpansion Γ out (b.inst a') := by
  obtain ⟨A1, B1, hf, ha⟩ := ht.app_inv henv hΓ
  rcases RF.lam_exposure hΓ hf with ⟨A0, b0, rfl, _, RB⟩ | ⟨A0, B0, hf0, _, RB⟩
  · exact ⟨_, .inr .beta, RB.inst_both (HasType.app_lam_arg hΓ ht) RA⟩
  · obtain ⟨⟨_, hAA⟩, _⟩ := (hf.uniqU henv hΓ hf0).forallE_inv henv hΓ
    exact ⟨_, .inl rfl, function_eta_beta_exchange RB (hAA.defeq ha) RA⟩

/-- A head step after an arbitrary finite eta path moves to before it without
duplicating the computational step. This bound permits induction through eta
transitivity and does not cover compatible argument or projection contraction. -/
theorem eta_headBeta_step (hΓ : OnCtx Γ (env.IsType univs))
    (RE : TypedEtaExpansion Γ a b) (ht : env.HasType univs Γ a T)
    (RB : HeadBetaStep b c) :
    ∃ out, (out = a ∨ HeadBetaStep a out) ∧ TypedEtaExpansion Γ out c := by
  induction RE generalizing c T with
  | refl => exact ⟨_, .inr RB, .refl⟩
  | structEta => exact RB.not_constant_spine.elim
  | funEta | lam | forallE | proj => cases RB
  | trans R1 R2 ih1 ih2 =>
    obtain ⟨mid, H, RE2⟩ := ih2 hΓ (R1.simAt hΓ _ ht).hasType.2 RB
    rcases H with rfl | H
    · exact ⟨_, .inl rfl, R1.trans RE2⟩
    · obtain ⟨out, H0, RE1⟩ := ih1 hΓ ht H
      exact ⟨out, H0, RE1.trans RE2⟩
  | app RF RA ihf iha =>
    cases RB with
    | beta => exact eta_function_headBeta hΓ RF RA ht
    | appL RB =>
      obtain ⟨A, B, hf, ha⟩ := ht.app_inv henv hΓ
      obtain ⟨f0, H, RE0⟩ := ihf hΓ hf RB
      rcases H with rfl | H
      · exact ⟨_, .inl rfl, .app RE0 RA⟩
      · exact ⟨_, .inr (.appL H), .app RE0 RA⟩

/-- Head beta from an eta-expanded literal constant spine is still just eta
expansion of that same source. The source admits no earlier head contraction. -/
theorem eta_constant_headBeta (hΓ : OnCtx Γ (env.IsType univs))
    (RE : TypedEtaExpansion Γ (mkApps (.const name levels) args) mid)
    (ht : env.HasType univs Γ (mkApps (.const name levels) args) T)
    (RB : HeadBetaRed mid out) :
    TypedEtaExpansion Γ (mkApps (.const name levels) args) out := by
  induction RB with
  | rfl => exact RE
  | tail _ R ih =>
    obtain ⟨out0, H, HE⟩ := eta_headBeta_step hΓ ih ht R
    rcases H with rfl | H
    · exact HE
    · exact H.not_constant_spine.elim

end Lean4Lean.VEnv.Strengthening.PureObservation
