import Lean4Lean.Theory.Typing.Strengthening.DeclarationStep
import Lean4Lean.Theory.Typing.Strengthening.NormalBetaReflection

/-! # Compatible beta/delta simulation through ordinary normal comparison

The simulated path uses beta and closed unfolding, even when the comparison
uses eta or extensionality. Opaque lambda-domain conversions are retained in the comparison.
No completeness of a descending comparison relation is asserted here.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}
variable (hs : D.Sound env univs) (hl : D.LevelStable univs)
include hs hl

omit hl in
private theorem compute_eq (hΓ : OnCtx Γ (env.IsType univs)) (R : Compute D e e')
    (ht : env.HasType univs Γ e T) : env.IsDefEq univs Γ e e' T :=
  R.simAt henv hs hΓ _ ht

omit hl in
private theorem compute_type (hΓ : OnCtx Γ (env.IsType univs)) (R : Compute D e e')
    (ht : env.HasType univs Γ e T) : env.HasType univs Γ e' T :=
  (compute_eq hs hΓ R ht).hasType.2

/-- One compatible contraction on the right can be mirrored by a finite beta/delta
path on the left. In particular, the etaBoth case adds no eta step. -/
theorem normal_compute_step (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEqN η n Γ a b) (R : ComputeStep D b b') :
    ∃ a', Compute D a a' ∧ NormalEq Γ a' b' := by
  induction H generalizing b' with
  | refl ht => exact ⟨_, R.toCompute, .refl (compute_type hs hΓ R.toCompute ht)⟩
  | sortDF => cases R
  | constDF hc hw1 hw2 hlen hlevels =>
    cases R with
    | delta HR =>
      have HR' := hl HR hw1 (hlevels.flip.imp (fun _ _ h => h.symm))
      obtain ⟨T, HT⟩ := hs _ _ _ _ HR'
      exact ⟨_, .delta HR', .refl HT.hasType.2⟩
  | appDF hf1 hf2 ha1 ha2 Hf Ha ihf iha =>
    cases R with
    | beta =>
      obtain ⟨x, RX, HX⟩ := normal_beta_spine (bs := []) hΓ
        ⟨_, .appDF hf1 hf2 ha1 ha2 Hf.toTrue Ha.toTrue⟩ (hf1.app ha1)
      exact ⟨x, .of_beta RX, HX⟩
    | appL R =>
      obtain ⟨f', Rf, HF⟩ := ihf hΓ R
      exact ⟨_, .app Rf .refl, .appDF (compute_type hs hΓ Rf hf1)
        (compute_type hs hΓ R.toCompute hf2) ha1 ha2 HF ⟨_, Ha.toTrue⟩⟩
    | appR R =>
      obtain ⟨a', Ra, HA⟩ := iha hΓ R
      exact ⟨_, .app .refl Ra, .appDF hf1 hf2 (compute_type hs hΓ Ra ha1)
        (compute_type hs hΓ R.toCompute ha2) ⟨_, Hf.toTrue⟩ HA⟩
  | projDF hp HM ihm =>
    cases R with
    | proj R =>
      obtain ⟨m', Rm, HM'⟩ := ihm hΓ R
      exact ⟨_, .proj Rm, .projDF (compute_type hs hΓ (.proj Rm) hp) HM'⟩
  | lamDF hD1 hD2 HB ihb =>
    have hΓD : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hD1.hasType.1⟩
    cases R with
    | lamL R =>
      exact ⟨_, .refl, .lamDF hD1 (hD2.trans (compute_eq hs hΓ R.toCompute hD2.hasType.2)) ⟨_, HB.toTrue⟩⟩
    | lamR R =>
      obtain ⟨b', Rb, HB'⟩ := ihb hΓD R
      exact ⟨_, .lam .refl Rb, .lamDF hD1 hD2 HB'⟩
  | forallEDF hD HD hb HB ihD ihB =>
    have hΓD : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hD.hasType.1⟩
    cases R with
    | forallL R =>
      obtain ⟨D', RD, HD'⟩ := ihD hΓ R
      exact ⟨_, .forallE RD .refl,
        .forallEDF (hD.trans (compute_eq hs hΓ RD hD.hasType.2)) HD' hb ⟨_, HB.toTrue⟩⟩
    | forallR R =>
      obtain ⟨B', RB, HB'⟩ := ihB hΓD R
      exact ⟨_, .forallE .refl RB, .forallEDF hD ⟨_, HD.toTrue⟩ (compute_type hs hΓD RB hb) HB'⟩
  | etaL hf HB ih =>
    obtain ⟨⟨_, hA⟩, _⟩ := let ⟨_, ht⟩ := hf.isType henv hΓ; ht.forallE_inv henv
    have hΓA : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hA⟩
    obtain ⟨b', Rb, HB'⟩ := ih hΓA (.appL (R.liftN 1 0))
    exact ⟨_, .lam .refl Rb, .etaL (compute_type hs hΓ R.toCompute hf) HB'⟩
  | etaR hf HB ih =>
    obtain ⟨⟨_, hA⟩, _⟩ := let ⟨_, ht⟩ := hf.isType henv hΓ; ht.forallE_inv henv
    have hΓA : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hA⟩
    cases R with
    | lamL R =>
      have hAA := compute_eq hs hΓ R.toCompute hA
      have hn : NormalEq _ _ _ := .etaR hf ⟨_, HB.toTrue⟩
      obtain ⟨_, hEq⟩ := HB.defeq hΓA
      have hbody := hEq.hasType.2
      exact ⟨_, .refl, hn.trans hΓ (.lamDF hA hAA (.refl hbody))⟩
    | lamR R =>
      obtain ⟨body', Rbody, HB'⟩ := ih hΓA R
      obtain ⟨f', Rf, HF⟩ := compute_eta_body_reflection hs hΓ hf Rbody
      exact ⟨_, Rf, HF.trans hΓ (.lamDF hA hA HB')⟩
  | etaBoth hf hg HB ih =>
    obtain ⟨⟨_, hA⟩, _⟩ := let ⟨_, ht⟩ := hf.isType henv hΓ; ht.forallE_inv henv
    have hΓA : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hA⟩
    obtain ⟨body', Rbody, HB'⟩ := ih hΓA (.appL (R.liftN 1 0))
    obtain ⟨f', Rf, HF⟩ := compute_eta_body_reflection hs hΓ hf Rbody
    exact ⟨_, Rf, HF.trans hΓ (.etaL (compute_type hs hΓ R.toCompute hg) HB')⟩
  | proofIrrel hp ha hb => exact ⟨_, .refl, .proofIrrel hp ha (compute_type hs hΓ R.toCompute hb)⟩

/-- Every finite compatible beta/delta path can be mirrored through ordinary normal
comparison by beta and closed unfolding. Both eta directions, extensionality, and annotation
reductions are covered; the final comparison still has opaque domain equalities. -/
theorem normal_compute_simulation (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEqF η Γ a b) (R : Compute D b b') :
    ∃ a', Compute D a a' ∧ NormalEq Γ a' b' := by
  obtain ⟨n, H⟩ := H
  apply compute_induct_steps (P := fun y => ∃ x, Compute D a x ∧ NormalEq Γ x y) R
  · exact ⟨_, .refl, _, H.toTrue⟩
  · intro x y R H
    obtain ⟨a1, R1, _, H1⟩ := H
    obtain ⟨a2, R2, H2⟩ := normal_compute_step hs hl hΓ H1 R
    exact ⟨a2, R1.trans R2, H2⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
