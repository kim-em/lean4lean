import Lean4Lean.Theory.Typing.Strengthening.ParameterStep
import Lean4Lean.Theory.Typing.Strengthening.NormalParameterTransport

/-! # Normal transport of compatible constructor parameter changes

A single compatible parameter change after normal comparison moves to beta
computation and reconstruction before normal comparison. Exact fresh-argument
beta reflection handles extensional comparisons. Finite mixed composition is
not asserted: it still needs reconstruction/computation postponement.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

private theorem beta_type (hΓ : OnCtx Γ (env.IsType univs))
    (R : BetaRed a b) (ht : env.HasType univs Γ a T) : env.HasType univs Γ b T :=
  (R.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ ht).hasType.2

private theorem reconstruction_type (hΓ : OnCtx Γ (env.IsType univs))
    (R : TypedReconstruction Γ a b) (ht : env.HasType univs Γ a T) : env.HasType univs Γ b T :=
  (R.simAt hΓ _ ht).hasType.2

private theorem normal_parameter_root (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEq Γ a b) (R : ConstructorParameterChange Γ b c) :
    ∃ a0 a1, BetaRed a a0 ∧ TypedReconstruction Γ a0 a1 ∧ NormalEq Γ a1 c := by
  obtain ⟨a0, a1, RB, RP, HN⟩ := normal_parameter_change hΓ H R
  refine ⟨a0, a1, RB.toBeta, ?_, HN⟩
  rcases RP with rfl | RP
  · exact .refl
  · exact .parameters RP

/-- Transport a single compatible parameter-change step through normal
comparison. Computation is beta only and precedes all residual reconstruction;
opaque lambda domains remain in the final normal comparison. -/
theorem normal_parameter_step (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEqN η n Γ a b) (R : ParameterStep Γ b b') :
    ∃ a0 a1, BetaRed a a0 ∧ TypedReconstruction Γ a0 a1 ∧ NormalEq Γ a1 b' := by
  induction H generalizing b' with
  | refl ht => exact ⟨_, _, .refl, R.toReconstruction,
      .refl (reconstruction_type hΓ R.toReconstruction ht)⟩
  | @sortDF l1 l2 η Γ hu hv he =>
    have H0 : NormalEq Γ _ _ := .sortDF hu hv he
    generalize hsrc : VExpr.sort l2 = source at R
    cases R with
    | root R => exact normal_parameter_root hΓ (hsrc ▸ H0) R
    | appL | appR | lamL | lamR | forallL | forallR | proj => cases hsrc
  | @constDF c ci ls ls' η Γ hc hw1 hw2 hlen hlevels =>
    have H0 : NormalEq Γ _ _ := .constDF hc hw1 hw2 hlen hlevels
    generalize hsrc : VExpr.const c ls' = source at R
    cases R with
    | root R => exact normal_parameter_root hΓ (hsrc ▸ H0) R
    | appL | appR | lamL | lamR | forallL | forallR | proj => cases hsrc
  | @appDF Γ f1 A B f2 a1 a2 η n1 n2 hf1 hf2 ha1 ha2 Hf Ha ihf iha =>
    have H0 : NormalEq _ _ _ := .appDF hf1 hf2 ha1 ha2 ⟨_, Hf.toTrue⟩ ⟨_, Ha.toTrue⟩
    generalize hsrc : VExpr.app f2 a2 = source at R
    cases R with
    | root R => exact normal_parameter_root hΓ (hsrc ▸ H0) R
    | appL R =>
      cases hsrc
      obtain ⟨f0, f', RB, Rf, HF⟩ := ihf hΓ R
      exact ⟨_, _, .app RB .refl, .app Rf .refl,
        .appDF (reconstruction_type hΓ Rf (beta_type hΓ RB hf1))
          (reconstruction_type hΓ R.toReconstruction hf2) ha1 ha2 HF ⟨_, Ha.toTrue⟩⟩
    | appR R =>
      cases hsrc
      obtain ⟨a0, a', RB, Ra, HA⟩ := iha hΓ R
      exact ⟨_, _, .app .refl RB, .app .refl Ra,
        .appDF hf1 hf2 (reconstruction_type hΓ Ra (beta_type hΓ RB ha1))
          (reconstruction_type hΓ R.toReconstruction ha2) ⟨_, Hf.toTrue⟩ HA⟩
    | lamL | lamR | forallL | forallR | proj => cases hsrc
  | @projDF Γ s i major T η n major' hp HM ihm =>
    have H0 : NormalEq _ _ _ := .projDF hp ⟨_, HM.toTrue⟩
    generalize hsrc : VExpr.proj s i major' = source at R
    cases R with
    | root R => exact normal_parameter_root hΓ (hsrc ▸ H0) R
    | proj R =>
      cases hsrc
      obtain ⟨m0, m', RB, Rm, HM'⟩ := ihm hΓ R
      exact ⟨_, _, .proj RB, .proj Rm,
        .projDF (reconstruction_type hΓ (.proj Rm) (beta_type hΓ (.proj RB) hp)) HM'⟩
    | appL | appR | lamL | lamR | forallL | forallR => cases hsrc
  | @lamDF Γ A A1 u A2 η n body1 body2 hD1 hD2 HB ihb =>
    have H0 : NormalEq _ _ _ := .lamDF hD1 hD2 ⟨_, HB.toTrue⟩
    have hΓD : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hD1.hasType.1⟩
    generalize hsrc : VExpr.lam A2 body2 = source at R
    cases R with
    | root R => exact normal_parameter_root hΓ (hsrc ▸ H0) R
    | lamL R =>
      cases hsrc
      exact ⟨_, _, .refl, .refl, .lamDF hD1
        (hD2.trans (R.toReconstruction.simAt hΓ _ hD2.hasType.2)) ⟨_, HB.toTrue⟩⟩
    | lamR R =>
      cases hsrc
      obtain ⟨_, hB⟩ := HB.defeq hΓD
      have R' := R.defeqDFC hΓ (.succ .zero hD2.symm)
        (hB.hasType.2.defeqDFC henv (.succ .zero hD2))
      obtain ⟨b0, b', RB, Rb, HB'⟩ := ihb hΓD R'
      have Rb' := Rb.defeqDFC hΓ (.succ .zero hD1) (beta_type hΓD RB hB.hasType.1)
      exact ⟨_, _, .lam .refl RB, .lam .refl Rb', .lamDF hD1 hD2 HB'⟩
    | appL | appR | forallL | forallR | proj => cases hsrc
  | @forallEDF Γ A A1 u η n1 A2 B1 v n2 B2 hD HD hb HB ihD ihB =>
    have H0 : NormalEq _ _ _ := .forallEDF hD ⟨_, HD.toTrue⟩ hb ⟨_, HB.toTrue⟩
    have hΓD : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hD.hasType.1⟩
    generalize hsrc : VExpr.forallE A2 B2 = source at R
    cases R with
    | root R => exact normal_parameter_root hΓ (hsrc ▸ H0) R
    | forallL R =>
      cases hsrc
      obtain ⟨D0, D', RB, RD, HD'⟩ := ihD hΓ R
      have hDD := RB.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ hD.hasType.2
      exact ⟨_, _, .forallE RB .refl, .forallE RD .refl,
        .forallEDF (hD.trans (hDD.trans (RD.simAt hΓ _ hDD.hasType.2))) HD' hb ⟨_, HB.toTrue⟩⟩
    | forallR R =>
      cases hsrc
      have W := hD.transU_l henv hΓ (HD.defeq hΓ)
      have hb2 := hb.defeqU_l henv hΓD (HB.defeq hΓD)
      have R' := R.defeqDFC hΓ (.succ .zero W.symm) (hb2.defeqDFC henv (.succ .zero W))
      obtain ⟨B0, B', RC, RB, HB'⟩ := ihB hΓD R'
      have RB' := RB.defeqDFC hΓ (.succ .zero hD) (beta_type hΓD RC hb)
      exact ⟨_, _, .forallE .refl RC, .forallE .refl RB',
        .forallEDF hD ⟨_, HD.toTrue⟩ (reconstruction_type hΓD RB (beta_type hΓD RC hb)) HB'⟩
    | appL | appR | lamL | lamR | proj => cases hsrc
  | etaL hf HB ih =>
    obtain ⟨⟨_, hA⟩, _⟩ := let ⟨_, ht⟩ := hf.isType henv hΓ; ht.forallE_inv henv
    have hΓA : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hA⟩
    obtain ⟨b0, b', RB, Rb, HB'⟩ := ih hΓA (.appL (R.weakN .one))
    exact ⟨_, _, .lam .refl RB, .lam .refl Rb,
      .etaL (reconstruction_type hΓ R.toReconstruction hf) HB'⟩
  | @etaR Γ f A B n body hf HB ih =>
    have H0 : NormalEq _ _ _ := .etaR hf ⟨_, HB.toTrue⟩
    obtain ⟨⟨_, hA⟩, _⟩ := let ⟨_, ht⟩ := hf.isType henv hΓ; ht.forallE_inv henv
    have hΓA : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hA⟩
    generalize hsrc : VExpr.lam A body = source at R
    cases R with
    | root R => exact normal_parameter_root hΓ (hsrc ▸ H0) R
    | lamL R =>
      cases hsrc
      have hAA := R.toReconstruction.simAt hΓ _ hA
      obtain ⟨_, hEq⟩ := HB.defeq hΓA
      exact ⟨_, _, .refl, .refl, H0.trans hΓ (.lamDF hA hAA (.refl hEq.hasType.2))⟩
    | lamR R =>
      cases hsrc
      obtain ⟨body0, body', RB, Rbody, HB'⟩ := ih hΓA R
      exact fresh_beta_reconstruction hΓ hf RB Rbody HB'
    | appL | appR | forallL | forallR | proj => cases hsrc
  | etaBoth hf hg HB ih =>
    obtain ⟨⟨_, hA⟩, _⟩ := let ⟨_, ht⟩ := hf.isType henv hΓ; ht.forallE_inv henv
    have hΓA : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hA⟩
    obtain ⟨body0, body', RB, Rbody, HB'⟩ := ih hΓA (.appL (R.weakN .one))
    obtain ⟨f0, f1, RF, RE, HN⟩ := fresh_beta_reconstruction hΓ hf RB Rbody HB'
    have hg' := reconstruction_type hΓ R.toReconstruction hg
    exact ⟨_, _, RF, RE, HN.trans hΓ (.etaL hg' (.refl
      (HasType.app (hg'.weak henv) (.bvar .zero))))⟩
  | proofIrrel hp ha hb => exact ⟨_, _, .refl, .refl,
      .proofIrrel hp ha (reconstruction_type hΓ R.toReconstruction hb)⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
