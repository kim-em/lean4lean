import Lean4Lean.Theory.Typing.Strengthening.NormalEtaRoot

/-! # Moving finite eta expansion before normal comparison

Normal comparison followed by any finite compatible typed eta path factors as
eta expansion followed by normal comparison. Extensional cases expand the left
function under its original Pi domain. No computational replay or front is used.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

private theorem eta_type (hΓ : OnCtx Γ (env.IsType univs))
    (R : TypedEtaExpansion Γ a b) (ht : env.HasType univs Γ a T) : env.HasType univs Γ b T :=
  (R.simAt hΓ _ ht).hasType.2

/-- One compatible eta expansion transports through normal comparison, keeping
all structure expansions on the left and all opaque domain conversions in the
final comparison. -/
theorem normal_eta_step (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEqN η n Γ a b) (R : TypedEtaStep Γ b b') :
    ∃ a', TypedEtaExpansion Γ a a' ∧ NormalEq Γ a' b' := by
  induction H generalizing b' with
  | refl ht => exact ⟨_, R.toExpansion, .refl (eta_type hΓ R.toExpansion ht)⟩
  | @sortDF l1 l2 η Γ hu hv he =>
    have H0 : NormalEq Γ _ _ := .sortDF hu hv he
    generalize hsrc : VExpr.sort l2 = source at R
    cases R with
    | root R => exact normal_eta_root hΓ (hsrc ▸ H0) R
    | appL | appR | lamL | lamR | forallL | forallR | proj => cases hsrc
  | @constDF c ci ls ls' η Γ hc hw1 hw2 hlen hlevels =>
    have H0 : NormalEq Γ _ _ := .constDF hc hw1 hw2 hlen hlevels
    generalize hsrc : VExpr.const c ls' = source at R
    cases R with
    | root R => exact normal_eta_root hΓ (hsrc ▸ H0) R
    | appL | appR | lamL | lamR | forallL | forallR | proj => cases hsrc
  | @appDF Γ f1 A B f2 a1 a2 η n1 n2 hf1 hf2 ha1 ha2 Hf Ha ihf iha =>
    have H0 : NormalEq _ _ _ := .appDF hf1 hf2 ha1 ha2 ⟨_, Hf.toTrue⟩ ⟨_, Ha.toTrue⟩
    generalize hsrc : VExpr.app f2 a2 = source at R
    cases R with
    | root R => exact normal_eta_root hΓ (hsrc ▸ H0) R
    | appL R =>
      cases hsrc
      obtain ⟨f', Rf, HF⟩ := ihf hΓ R
      exact ⟨_, .app Rf .refl, .appDF (eta_type hΓ Rf hf1)
        (eta_type hΓ R.toExpansion hf2) ha1 ha2 HF ⟨_, Ha.toTrue⟩⟩
    | appR R =>
      cases hsrc
      obtain ⟨a', Ra, HA⟩ := iha hΓ R
      exact ⟨_, .app .refl Ra, .appDF hf1 hf2 (eta_type hΓ Ra ha1)
        (eta_type hΓ R.toExpansion ha2) ⟨_, Hf.toTrue⟩ HA⟩
    | lamL | lamR | forallL | forallR | proj => cases hsrc
  | @projDF Γ s i major T η n major' hp HM ihm =>
    have H0 : NormalEq _ _ _ := .projDF hp ⟨_, HM.toTrue⟩
    generalize hsrc : VExpr.proj s i major' = source at R
    cases R with
    | root R => exact normal_eta_root hΓ (hsrc ▸ H0) R
    | proj R =>
      cases hsrc
      obtain ⟨m', Rm, HM'⟩ := ihm hΓ R
      exact ⟨_, .proj Rm, .projDF (eta_type hΓ (.proj Rm) hp) HM'⟩
    | appL | appR | lamL | lamR | forallL | forallR => cases hsrc
  | @lamDF Γ A A1 u A2 η n body1 body2 hD1 hD2 HB ihb =>
    have H0 : NormalEq _ _ _ := .lamDF hD1 hD2 ⟨_, HB.toTrue⟩
    have hΓD : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hD1.hasType.1⟩
    generalize hsrc : VExpr.lam A2 body2 = source at R
    cases R with
    | root R => exact normal_eta_root hΓ (hsrc ▸ H0) R
    | lamL R =>
      cases hsrc
      exact ⟨_, .refl, .lamDF hD1
        (hD2.trans (R.toExpansion.simAt hΓ _ hD2.hasType.2)) ⟨_, HB.toTrue⟩⟩
    | lamR R =>
      cases hsrc
      obtain ⟨_, hB⟩ := HB.defeq hΓD
      have R' := R.defeqDFC hΓ (.succ .zero hD2.symm)
        (hB.hasType.2.defeqDFC henv (.succ .zero hD2))
      obtain ⟨b', Rb, HB'⟩ := ihb hΓD R'
      have Rb' := Rb.defeqDFC hΓ (.succ .zero hD1) hB.hasType.1
      exact ⟨_, .lam .refl Rb', .lamDF hD1 hD2 HB'⟩
    | appL | appR | forallL | forallR | proj => cases hsrc
  | @forallEDF Γ A A1 u η n1 A2 B1 v n2 B2 hD HD hb HB ihD ihB =>
    have H0 : NormalEq _ _ _ := .forallEDF hD ⟨_, HD.toTrue⟩ hb ⟨_, HB.toTrue⟩
    have hΓD : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hD.hasType.1⟩
    generalize hsrc : VExpr.forallE A2 B2 = source at R
    cases R with
    | root R => exact normal_eta_root hΓ (hsrc ▸ H0) R
    | forallL R =>
      cases hsrc
      obtain ⟨D', RD, HD'⟩ := ihD hΓ R
      exact ⟨_, .forallE RD .refl,
        .forallEDF (hD.trans (RD.simAt hΓ _ hD.hasType.2)) HD' hb ⟨_, HB.toTrue⟩⟩
    | forallR R =>
      cases hsrc
      have W := hD.transU_l henv hΓ (HD.defeq hΓ)
      have hb2 := hb.defeqU_l henv hΓD (HB.defeq hΓD)
      have R' := R.defeqDFC hΓ (.succ .zero W.symm) (hb2.defeqDFC henv (.succ .zero W))
      obtain ⟨B', RB, HB'⟩ := ihB hΓD R'
      have RB' := RB.defeqDFC hΓ (.succ .zero hD) hb
      exact ⟨_, .forallE .refl RB',
        .forallEDF hD ⟨_, HD.toTrue⟩ (eta_type hΓD RB hb) HB'⟩
    | appL | appR | lamL | lamR | proj => cases hsrc
  | etaL hf HB ih =>
    obtain ⟨⟨_, hA⟩, _⟩ := let ⟨_, ht⟩ := hf.isType henv hΓ; ht.forallE_inv henv
    have hΓA : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hA⟩
    obtain ⟨b', Rb, HB'⟩ := ih hΓA (.appL (R.weakN .one))
    exact ⟨_, .lam .refl Rb, .etaL (eta_type hΓ R.toExpansion hf) HB'⟩
  | @etaR Γ f A B n body hf HB ih =>
    have H0 : NormalEq _ _ _ := .etaR hf ⟨_, HB.toTrue⟩
    obtain ⟨⟨_, hA⟩, _⟩ := let ⟨_, ht⟩ := hf.isType henv hΓ; ht.forallE_inv henv
    have hΓA : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hA⟩
    generalize hsrc : VExpr.lam A body = source at R
    cases R with
    | root R => exact normal_eta_root hΓ (hsrc ▸ H0) R
    | lamL R =>
      cases hsrc
      have hAA := R.toExpansion.simAt hΓ _ hA
      obtain ⟨_, hEq⟩ := HB.defeq hΓA
      exact ⟨_, .refl, H0.trans hΓ (.lamDF hA hAA (.refl hEq.hasType.2))⟩
    | lamR R =>
      cases hsrc
      obtain ⟨body', Rbody, HB'⟩ := ih hΓA R
      exact ⟨_, (TypedEtaExpansion.funEta hf).trans (.lam .refl Rbody), .lamDF hA hA HB'⟩
    | appL | appR | forallL | forallR | proj => cases hsrc
  | etaBoth hf hg HB ih =>
    obtain ⟨⟨_, hA⟩, _⟩ := let ⟨_, ht⟩ := hf.isType henv hΓ; ht.forallE_inv henv
    have hΓA : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hA⟩
    obtain ⟨body', Rbody, HB'⟩ := ih hΓA (.appL (R.weakN .one))
    exact ⟨_, (TypedEtaExpansion.funEta hf).trans (.lam .refl Rbody),
      .etaL (eta_type hΓ R.toExpansion hg) HB'⟩
  | proofIrrel hp ha hb => exact ⟨_, .refl, .proofIrrel hp ha (eta_type hΓ R.toExpansion hb)⟩

/-- Every finite eta path after normal comparison moves to before it. This is
phase exchange, not the still-missing computational postponement theorem. -/
theorem normal_eta_simulation (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEq Γ a b) (R : TypedEtaExpansion Γ b c) :
    ∃ a', TypedEtaExpansion Γ a a' ∧ NormalEq Γ a' c := by
  apply eta_induct_steps R (P := fun x => ∃ a', TypedEtaExpansion Γ a a' ∧ NormalEq Γ a' x)
    ⟨a, .refl, H⟩
  intro x y R H
  obtain ⟨a', RA, n, HN⟩ := H
  obtain ⟨a'', RB, HN'⟩ := normal_eta_step hΓ HN R
  exact ⟨a'', RA.trans RB, HN'⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
