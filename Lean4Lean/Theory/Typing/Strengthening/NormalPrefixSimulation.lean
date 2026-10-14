import Lean4Lean.Theory.Typing.Strengthening.NormalPrefixTransport
import Lean4Lean.Theory.Typing.Strengthening.PrefixStep
import Lean4Lean.Theory.Typing.Strengthening.NormalPatternSimulation

/-! # Conditional normal simulation of finite checked prefix computation

All compatible computation can pass through ordinary normal comparison without
adding eta expansion steps. The witnessed front remains explicit, and opaque
lambda-domain comparisons remain in the final NormalEq.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}

private theorem compute_type (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (R : PrefixCompute D Γ a b) (ht : env.HasType univs Γ a T) : env.HasType univs Γ b T :=
  (R.simAt hs hΓ _ ht).hasType.2

private theorem normal_base (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : NormalEq Γ a b) (R : PatternStep D b b') :
    ∃ a', PrefixCompute D Γ a a' ∧ NormalEq Γ a' b' := by
  obtain ⟨n, H⟩ := H
  obtain ⟨a', R, H⟩ := normal_pattern_step_compatible hs hl hΓ H R
  exact ⟨a', .base R, H⟩

/-- One compatible checked contraction transports through normal comparison.
Context conversion under binders retains every original prefix check. -/
theorem normal_prefix_step_compatible (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hl : D.LevelCompatible univs)
    (hfront : GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b))
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEqN η n Γ a b) (R : PrefixStep D Γ b b') :
    ∃ a', PrefixCompute D Γ a a' ∧ NormalEq Γ a' b' := by
  induction H generalizing b' with
  | refl ht => exact ⟨_, R.toCompute, .refl (compute_type hs hΓ R.toCompute ht)⟩
  | @sortDF l1 l2 η Γ hu hv he =>
    have H0 : NormalEq Γ _ _ := .sortDF hu hv he
    generalize hsrc : VExpr.sort l2 = source at R
    cases R with
    | base R => exact normal_base hs hl hΓ (hsrc ▸ H0) R
    | singleton R => exact normal_singleton_prefix heq hs hfront hΓ (hsrc ▸ H0) R
    | quotient R => exact normal_quotient_prefix heq hs hfront hΓ (hsrc ▸ H0) R
    | appL | appR | lamL | lamR | forallL | forallR | proj => cases hsrc
  | @constDF c ci ls ls' η Γ hc hw1 hw2 hlen hlevels =>
    have H0 : NormalEq Γ _ _ := .constDF hc hw1 hw2 hlen hlevels
    generalize hsrc : VExpr.const c ls' = source at R
    cases R with
    | base R => exact normal_base hs hl hΓ (hsrc ▸ H0) R
    | singleton R => exact normal_singleton_prefix heq hs hfront hΓ (hsrc ▸ H0) R
    | quotient R => exact normal_quotient_prefix heq hs hfront hΓ (hsrc ▸ H0) R
    | appL | appR | lamL | lamR | forallL | forallR | proj => cases hsrc
  | @appDF Γ f1 A B f2 a1 a2 η n1 n2 hf1 hf2 ha1 ha2 Hf Ha ihf iha =>
    have H0 : NormalEq _ _ _ := .appDF hf1 hf2 ha1 ha2 ⟨_, Hf.toTrue⟩ ⟨_, Ha.toTrue⟩
    generalize hsrc : VExpr.app f2 a2 = source at R
    cases R with
    | base R => exact normal_base hs hl hΓ (hsrc ▸ H0) R
    | singleton R => exact normal_singleton_prefix heq hs hfront hΓ (hsrc ▸ H0) R
    | quotient R => exact normal_quotient_prefix heq hs hfront hΓ (hsrc ▸ H0) R
    | appL R =>
      cases hsrc
      obtain ⟨f', Rf, HF⟩ := ihf hΓ R
      exact ⟨_, .app Rf .refl, .appDF (compute_type hs hΓ Rf hf1)
        (compute_type hs hΓ R.toCompute hf2) ha1 ha2 HF ⟨_, Ha.toTrue⟩⟩
    | appR R =>
      cases hsrc
      obtain ⟨a', Ra, HA⟩ := iha hΓ R
      exact ⟨_, .app .refl Ra, .appDF hf1 hf2 (compute_type hs hΓ Ra ha1)
        (compute_type hs hΓ R.toCompute ha2) ⟨_, Hf.toTrue⟩ HA⟩
    | lamL | lamR | forallL | forallR | proj => cases hsrc
  | @projDF Γ s i major T η n major' hp HM ihm =>
    have H0 : NormalEq _ _ _ := .projDF hp ⟨_, HM.toTrue⟩
    generalize hsrc : VExpr.proj s i major' = source at R
    cases R with
    | base R => exact normal_base hs hl hΓ (hsrc ▸ H0) R
    | singleton R => exact normal_singleton_prefix heq hs hfront hΓ (hsrc ▸ H0) R
    | quotient R => exact normal_quotient_prefix heq hs hfront hΓ (hsrc ▸ H0) R
    | proj R =>
      cases hsrc
      obtain ⟨m', Rm, HM'⟩ := ihm hΓ R
      exact ⟨_, .proj Rm, .projDF (compute_type hs hΓ (.proj Rm) hp) HM'⟩
    | appL | appR | lamL | lamR | forallL | forallR => cases hsrc
  | @lamDF Γ A A1 u A2 η n body1 body2 hD1 hD2 HB ihb =>
    have H0 : NormalEq _ _ _ := .lamDF hD1 hD2 ⟨_, HB.toTrue⟩
    have hΓD : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hD1.hasType.1⟩
    generalize hsrc : VExpr.lam A2 body2 = source at R
    cases R with
    | base R => exact normal_base hs hl hΓ (hsrc ▸ H0) R
    | singleton R => exact normal_singleton_prefix heq hs hfront hΓ (hsrc ▸ H0) R
    | quotient R => exact normal_quotient_prefix heq hs hfront hΓ (hsrc ▸ H0) R
    | lamL R =>
      cases hsrc
      exact ⟨_, .refl, .lamDF hD1
        (hD2.trans (R.toCompute.simAt hs hΓ _ hD2.hasType.2)) ⟨_, HB.toTrue⟩⟩
    | lamR R =>
      cases hsrc
      obtain ⟨_, hB⟩ := HB.defeq hΓD
      have R' := R.defeqDFC hΓ (.succ .zero hD2.symm)
        (hB.hasType.2.defeqDFC henv (.succ .zero hD2))
      obtain ⟨b', Rb, HB'⟩ := ihb hΓD R'
      have Rb' := Rb.defeqDFC hs hΓ (.succ .zero hD1) hB.hasType.1
      exact ⟨_, .lam .refl Rb', .lamDF hD1 hD2 HB'⟩
    | appL | appR | forallL | forallR | proj => cases hsrc
  | @forallEDF Γ A A1 u η n1 A2 B1 v n2 B2 hD HD hb HB ihD ihB =>
    have H0 : NormalEq _ _ _ := .forallEDF hD ⟨_, HD.toTrue⟩ hb ⟨_, HB.toTrue⟩
    have hΓD : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hD.hasType.1⟩
    generalize hsrc : VExpr.forallE A2 B2 = source at R
    cases R with
    | base R => exact normal_base hs hl hΓ (hsrc ▸ H0) R
    | singleton R => exact normal_singleton_prefix heq hs hfront hΓ (hsrc ▸ H0) R
    | quotient R => exact normal_quotient_prefix heq hs hfront hΓ (hsrc ▸ H0) R
    | forallL R =>
      cases hsrc
      obtain ⟨D', RD, HD'⟩ := ihD hΓ R
      exact ⟨_, .forallE RD .refl,
        .forallEDF (hD.trans (RD.simAt hs hΓ _ hD.hasType.2)) HD' hb ⟨_, HB.toTrue⟩⟩
    | forallR R =>
      cases hsrc
      have W := hD.transU_l henv hΓ (HD.defeq hΓ)
      have hb2 := hb.defeqU_l henv hΓD (HB.defeq hΓD)
      have R' := R.defeqDFC hΓ (.succ .zero W.symm) (hb2.defeqDFC henv (.succ .zero W))
      obtain ⟨B', RB, HB'⟩ := ihB hΓD R'
      have RB' := RB.defeqDFC hs hΓ (.succ .zero hD) hb
      exact ⟨_, .forallE .refl RB',
        .forallEDF hD ⟨_, HD.toTrue⟩ (compute_type hs hΓD RB hb) HB'⟩
    | appL | appR | lamL | lamR | proj => cases hsrc
  | etaL hf HB ih =>
    obtain ⟨⟨_, hA⟩, _⟩ := let ⟨_, ht⟩ := hf.isType henv hΓ; ht.forallE_inv henv
    have hΓA : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hA⟩
    obtain ⟨b', Rb, HB'⟩ := ih hΓA (.appL (R.weakN .one))
    exact ⟨_, .lam .refl Rb, .etaL (compute_type hs hΓ R.toCompute hf) HB'⟩
  | @etaR Γ f A B n body hf HB ih =>
    have H0 : NormalEq _ _ _ := .etaR hf ⟨_, HB.toTrue⟩
    obtain ⟨⟨_, hA⟩, _⟩ := let ⟨_, ht⟩ := hf.isType henv hΓ; ht.forallE_inv henv
    have hΓA : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hA⟩
    generalize hsrc : VExpr.lam A body = source at R
    cases R with
    | base R => exact normal_base hs hl hΓ (hsrc ▸ H0) R
    | singleton R => exact normal_singleton_prefix heq hs hfront hΓ (hsrc ▸ H0) R
    | quotient R => exact normal_quotient_prefix heq hs hfront hΓ (hsrc ▸ H0) R
    | lamL R =>
      cases hsrc
      have hAA := R.toCompute.simAt hs hΓ _ hA
      obtain ⟨_, hEq⟩ := HB.defeq hΓA
      exact ⟨_, .refl, H0.trans hΓ (.lamDF hA hAA (.refl hEq.hasType.2))⟩
    | lamR R =>
      cases hsrc
      obtain ⟨body', Rbody, HB'⟩ := ih hΓA R
      obtain ⟨f', Rf, HF⟩ := Rbody.eta_body_reflection heq hs hfront hΓ hf
      exact ⟨_, Rf, HF.trans hΓ (.lamDF hA hA HB')⟩
    | appL | appR | forallL | forallR | proj => cases hsrc
  | etaBoth hf hg HB ih =>
    obtain ⟨⟨_, hA⟩, _⟩ := let ⟨_, ht⟩ := hf.isType henv hΓ; ht.forallE_inv henv
    have hΓA : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hA⟩
    obtain ⟨body', Rbody, HB'⟩ := ih hΓA (.appL (R.weakN .one))
    obtain ⟨f', Rf, HF⟩ := Rbody.eta_body_reflection heq hs hfront hΓ hf
    exact ⟨_, Rf, HF.trans hΓ (.etaL (compute_type hs hΓ R.toCompute hg) HB')⟩
  | proofIrrel hp ha hb => exact ⟨_, .refl, .proofIrrel hp ha (compute_type hs hΓ R.toCompute hb)⟩

/-- Under the witnessed front, every finite compatible pattern-and-prefix path
commutes with ordinary normal comparison. No eta computation is introduced. -/
theorem normal_prefix_simulation_compatible (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hl : D.LevelCompatible univs)
    (hfront : GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b))
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEqF η Γ a b) (R : PrefixCompute D Γ b b') :
    ∃ a', PrefixCompute D Γ a a' ∧ NormalEq Γ a' b' := by
  obtain ⟨n, H⟩ := H
  apply prefix_induct_steps hcon (P := fun y => ∃ x, PrefixCompute D Γ a x ∧ NormalEq Γ x y) R
  · exact ⟨_, .refl, _, H.toTrue⟩
  · intro x y R H
    obtain ⟨a1, R1, _, H1⟩ := H
    obtain ⟨a2, R2, H2⟩ := normal_prefix_step_compatible heq hs hl hfront hΓ H1 R
    exact ⟨a2, R1.trans R2, H2⟩

/-- Prefix transport with the original exact universe stability interface. -/
theorem normal_prefix_step (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hl : D.LevelStable univs)
    (hfront : GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b))
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEqN η n Γ a b) (R : PrefixStep D Γ b b') :
    ∃ a', PrefixCompute D Γ a a' ∧ NormalEq Γ a' b' :=
  normal_prefix_step_compatible heq hs hl.compatible hfront hΓ H R

/-- Prefix transport with the original exact universe stability interface. -/
theorem normal_prefix_simulation (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hl : D.LevelStable univs)
    (hfront : GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b))
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEqF η Γ a b) (R : PrefixCompute D Γ b b') :
    ∃ a', PrefixCompute D Γ a a' ∧ NormalEq Γ a' b' :=
  normal_prefix_simulation_compatible heq hs hl.compatible hfront hcon hΓ H R

end Lean4Lean.VEnv.Strengthening.PureObservation
