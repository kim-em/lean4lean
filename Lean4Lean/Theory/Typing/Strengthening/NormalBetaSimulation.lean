import Lean4Lean.Theory.Typing.Strengthening.BetaStep

/-! # Compatible beta simulation through ordinary normal comparison

The simulated path uses beta alone, even when the comparison uses eta or
extensionality. Opaque lambda-domain conversions are retained in the comparison.
No completeness of a descending comparison relation is asserted here.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

private theorem beta_eq (hΓ : OnCtx Γ (env.IsType univs)) (R : BetaRed e e')
    (ht : env.HasType univs Γ e T) : env.IsDefEq univs Γ e e' T :=
  R.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ ht

private theorem beta_type (hΓ : OnCtx Γ (env.IsType univs)) (R : BetaRed e e')
    (ht : env.HasType univs Γ e T) : env.HasType univs Γ e' T :=
  (beta_eq hΓ R ht).hasType.2

/-- One compatible contraction on the right can be mirrored by a finite beta
path on the left. In particular, the etaBoth case adds no eta step. -/
theorem normal_beta_step (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEqN η n Γ a b) (R : BetaStep b b') :
    ∃ a', BetaRed a a' ∧ NormalEq Γ a' b' := by
  induction H generalizing b' with
  | refl ht => exact ⟨_, R.toBeta, .refl (beta_type hΓ R.toBeta ht)⟩
  | sortDF | constDF => cases R
  | appDF hf1 hf2 ha1 ha2 Hf Ha ihf iha =>
    cases R with
    | beta =>
      exact normal_beta_spine (bs := []) hΓ ⟨_, .appDF hf1 hf2 ha1 ha2 Hf.toTrue Ha.toTrue⟩ (hf1.app ha1)
    | appL R =>
      obtain ⟨f', Rf, HF⟩ := ihf hΓ R
      exact ⟨_, .app Rf .refl, .appDF (beta_type hΓ Rf hf1)
        (beta_type hΓ R.toBeta hf2) ha1 ha2 HF ⟨_, Ha.toTrue⟩⟩
    | appR R =>
      obtain ⟨a', Ra, HA⟩ := iha hΓ R
      exact ⟨_, .app .refl Ra, .appDF hf1 hf2 (beta_type hΓ Ra ha1)
        (beta_type hΓ R.toBeta ha2) ⟨_, Hf.toTrue⟩ HA⟩
  | projDF hp HM ihm =>
    cases R with
    | proj R =>
      obtain ⟨m', Rm, HM'⟩ := ihm hΓ R
      exact ⟨_, .proj Rm, .projDF (beta_type hΓ (.proj Rm) hp) HM'⟩
  | lamDF hD1 hD2 HB ihb =>
    have hΓD : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hD1.hasType.1⟩
    cases R with
    | lamL R =>
      exact ⟨_, .refl, .lamDF hD1 (hD2.trans (beta_eq hΓ R.toBeta hD2.hasType.2)) ⟨_, HB.toTrue⟩⟩
    | lamR R =>
      obtain ⟨b', Rb, HB'⟩ := ihb hΓD R
      exact ⟨_, .lam .refl Rb, .lamDF hD1 hD2 HB'⟩
  | forallEDF hD HD hb HB ihD ihB =>
    have hΓD : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hD.hasType.1⟩
    cases R with
    | forallL R =>
      obtain ⟨D', RD, HD'⟩ := ihD hΓ R
      exact ⟨_, .forallE RD .refl,
        .forallEDF (hD.trans (beta_eq hΓ RD hD.hasType.2)) HD' hb ⟨_, HB.toTrue⟩⟩
    | forallR R =>
      obtain ⟨B', RB, HB'⟩ := ihB hΓD R
      exact ⟨_, .forallE .refl RB, .forallEDF hD ⟨_, HD.toTrue⟩ (beta_type hΓD RB hb) HB'⟩
  | etaL hf HB ih =>
    obtain ⟨⟨_, hA⟩, _⟩ := let ⟨_, ht⟩ := hf.isType henv hΓ; ht.forallE_inv henv
    have hΓA : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hA⟩
    obtain ⟨b', Rb, HB'⟩ := ih hΓA (.appL (R.liftN 1 0))
    exact ⟨_, .lam .refl Rb, .etaL (beta_type hΓ R.toBeta hf) HB'⟩
  | etaR hf HB ih =>
    obtain ⟨⟨_, hA⟩, _⟩ := let ⟨_, ht⟩ := hf.isType henv hΓ; ht.forallE_inv henv
    have hΓA : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hA⟩
    cases R with
    | lamL R =>
      have hAA := beta_eq hΓ R.toBeta hA
      have hn : NormalEq _ _ _ := .etaR hf ⟨_, HB.toTrue⟩
      obtain ⟨_, hEq⟩ := HB.defeq hΓA
      have hbody := hEq.hasType.2
      exact ⟨_, .refl, hn.trans hΓ (.lamDF hA hAA (.refl hbody))⟩
    | lamR R =>
      obtain ⟨body', Rbody, HB'⟩ := ih hΓA R
      obtain ⟨f', Rf, HF⟩ := beta_eta_body_reflection hΓ hf Rbody
      exact ⟨_, Rf, HF.trans hΓ (.lamDF hA hA HB')⟩
  | etaBoth hf hg HB ih =>
    obtain ⟨⟨_, hA⟩, _⟩ := let ⟨_, ht⟩ := hf.isType henv hΓ; ht.forallE_inv henv
    have hΓA : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hA⟩
    obtain ⟨body', Rbody, HB'⟩ := ih hΓA (.appL (R.liftN 1 0))
    obtain ⟨f', Rf, HF⟩ := beta_eta_body_reflection hΓ hf Rbody
    exact ⟨_, Rf, HF.trans hΓ (.etaL (beta_type hΓ R.toBeta hg) HB')⟩
  | proofIrrel hp ha hb => exact ⟨_, .refl, .proofIrrel hp ha (beta_type hΓ R.toBeta hb)⟩

/-- Every finite compatible beta path can be mirrored through ordinary normal
comparison by beta alone. Both eta directions, extensionality, and annotation
reductions are covered; the final comparison still has opaque domain equalities. -/
theorem normal_beta_simulation (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEqF η Γ a b) (R : BetaRed b b') :
    ∃ a', BetaRed a a' ∧ NormalEq Γ a' b' := by
  obtain ⟨n, H⟩ := H
  apply betaRed_induct_steps (P := fun y => ∃ x, BetaRed a x ∧ NormalEq Γ x y) R
  · exact ⟨_, .refl, _, H.toTrue⟩
  · intro x y R H
    obtain ⟨a1, R1, _, H1⟩ := H
    obtain ⟨a2, R2, H2⟩ := normal_beta_step hΓ H1 R
    exact ⟨a2, R1.trans R2, H2⟩

end Lean4Lean.VEnv.Strengthening
