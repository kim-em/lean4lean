import Lean4Lean.Theory.Typing.Strengthening.PatternStep
import Lean4Lean.Theory.Typing.Strengthening.NormalBetaReflection

/-! # Compatible concrete pattern simulation through ordinary normal comparison

The simulated path uses beta, closed unfolding, patterns and projection computation, even when the comparison
uses eta or extensionality. Opaque lambda-domain conversions are retained in the comparison.
No completeness of a descending comparison relation is asserted here.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}
variable (hs : D.Sound env univs) (hl : D.LevelStable univs)
include hs hl

omit hl in
private theorem pattern_eq (hΓ : OnCtx Γ (env.IsType univs)) (R : PatternCompute D e e')
    (ht : env.HasType univs Γ e T) : env.IsDefEq univs Γ e e' T :=
  R.simAt hs hΓ _ ht

omit hl in
private theorem pattern_type (hΓ : OnCtx Γ (env.IsType univs)) (R : PatternCompute D e e')
    (ht : env.HasType univs Γ e T) : env.HasType univs Γ e' T :=
  (pattern_eq hs hΓ R ht).hasType.2

/-- One compatible contraction on the right can be mirrored by a finite pattern
path on the left. In particular, the etaBoth case adds no eta step. -/
theorem normal_pattern_step (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEqN η n Γ a b) (R : PatternStep D b b') :
    ∃ a', PatternCompute D a a' ∧ NormalEq Γ a' b' := by
  induction H generalizing b' with
  | refl ht => exact ⟨_, R.toCompute, .refl (pattern_type hs hΓ R.toCompute ht)⟩
  | sortDF => cases R with | pattern _ _ hm _ => cases hm
  | constDF hc hw1 hw2 hlen hlevels =>
    cases R with
    | delta HR =>
      have HR' := hl HR hw1 (hlevels.flip.imp (fun _ _ h => h.symm))
      obtain ⟨T, HT⟩ := hs _ _ _ _ HR'
      exact ⟨_, .base (.base (.delta HR')), .refl HT.hasType.2⟩
    | pattern hp hcon hm hcheck =>
      cases hm
      obtain ⟨_, HE⟩ := (NormalEq.constDF hc hw1 hw2 hlen hlevels).defeq hΓ
      have ht := HE.hasType.1
      have hr := hcheck hΓ Pattern.Matches.const HE.hasType.2
      have hlc := Pattern.Check.const_levels hΓ hw2 hw1
        (hlevels.flip.imp (fun _ _ h => h.symm)) hr (values' := fun a => nomatch a)
      have RF : PatternCompute D _ _ := .pattern hp .const
        (ConcretePattern.checkFromTyping henv hcon hlc)
      exact ⟨_, RF, NormalEq.of_levelEquiv hΓ
        (Pattern.RHS.const_levelEquiv _ hw1 hw2 hlevels) (pattern_type hs hΓ RF ht)⟩
  | appDF hf1 hf2 ha1 ha2 Hf Ha ihf iha =>
    cases R with
    | beta =>
      obtain ⟨x, RX, HX⟩ := normal_beta_spine (bs := []) hΓ
        ⟨_, .appDF hf1 hf2 ha1 ha2 Hf.toTrue Ha.toTrue⟩ (hf1.app ha1)
      exact ⟨x, .of_beta RX, HX⟩
    | pattern hp hcon hm hcheck =>
      obtain ⟨sp, hsp⟩ := pat_simple hp
      cases sp with
      | defn => subst hsp; cases hm
      | iota =>
        subst hsp
        exact normal_iota_compute hs hΓ hp hcon hm (hcheck hΓ hm (hf2.app ha2))
          ⟨_, .appDF hf1 hf2 ha1 ha2 Hf.toTrue Ha.toTrue⟩
    | appL R =>
      obtain ⟨f', Rf, HF⟩ := ihf hΓ R
      exact ⟨_, .app Rf .refl, .appDF (pattern_type hs hΓ Rf hf1)
        (pattern_type hs hΓ R.toCompute hf2) ha1 ha2 HF ⟨_, Ha.toTrue⟩⟩
    | appR R =>
      obtain ⟨a', Ra, HA⟩ := iha hΓ R
      exact ⟨_, .app .refl Ra, .appDF hf1 hf2 (pattern_type hs hΓ Ra ha1)
        (pattern_type hs hΓ R.toCompute ha2) ⟨_, Hf.toTrue⟩ HA⟩
  | projDF hp HM ihm =>
    cases R with
    | pattern _ _ hm _ => cases hm
    | projIota hi hl hg =>
      have hn := NormalEq.projDF hp ⟨_, HM.toTrue⟩
      have hright := ((hn.defeq hΓ).of_l henv hΓ hp).hasType.2
      have hfield := HasType.projIota_field hΓ hi hright hl hg
      exact normal_projection_compute hs hΓ hp HM.toTrue hi hright hl hg hfield
    | proj R =>
      obtain ⟨m', Rm, HM'⟩ := ihm hΓ R
      exact ⟨_, .proj Rm, .projDF (pattern_type hs hΓ (.proj Rm) hp) HM'⟩
  | lamDF hD1 hD2 HB ihb =>
    have hΓD : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hD1.hasType.1⟩
    cases R with
    | pattern _ _ hm _ => cases hm
    | lamL R =>
      exact ⟨_, .refl, .lamDF hD1 (hD2.trans (pattern_eq hs hΓ R.toCompute hD2.hasType.2)) ⟨_, HB.toTrue⟩⟩
    | lamR R =>
      obtain ⟨b', Rb, HB'⟩ := ihb hΓD R
      exact ⟨_, .lam .refl Rb, .lamDF hD1 hD2 HB'⟩
  | forallEDF hD HD hb HB ihD ihB =>
    have hΓD : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hD.hasType.1⟩
    cases R with
    | pattern _ _ hm _ => cases hm
    | forallL R =>
      obtain ⟨D', RD, HD'⟩ := ihD hΓ R
      exact ⟨_, .forallE RD .refl,
        .forallEDF (hD.trans (pattern_eq hs hΓ RD hD.hasType.2)) HD' hb ⟨_, HB.toTrue⟩⟩
    | forallR R =>
      obtain ⟨B', RB, HB'⟩ := ihB hΓD R
      exact ⟨_, .forallE .refl RB, .forallEDF hD ⟨_, HD.toTrue⟩ (pattern_type hs hΓD RB hb) HB'⟩
  | etaL hf HB ih =>
    obtain ⟨⟨_, hA⟩, _⟩ := let ⟨_, ht⟩ := hf.isType henv hΓ; ht.forallE_inv henv
    have hΓA : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hA⟩
    obtain ⟨b', Rb, HB'⟩ := ih hΓA (.appL (R.liftN 1 0))
    exact ⟨_, .lam .refl Rb, .etaL (pattern_type hs hΓ R.toCompute hf) HB'⟩
  | etaR hf HB ih =>
    obtain ⟨⟨_, hA⟩, _⟩ := let ⟨_, ht⟩ := hf.isType henv hΓ; ht.forallE_inv henv
    have hΓA : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hA⟩
    cases R with
    | pattern _ _ hm _ => cases hm
    | lamL R =>
      have hAA := pattern_eq hs hΓ R.toCompute hA
      have hn : NormalEq _ _ _ := .etaR hf ⟨_, HB.toTrue⟩
      obtain ⟨_, hEq⟩ := HB.defeq hΓA
      have hbody := hEq.hasType.2
      exact ⟨_, .refl, hn.trans hΓ (.lamDF hA hAA (.refl hbody))⟩
    | lamR R =>
      obtain ⟨body', Rbody, HB'⟩ := ih hΓA R
      obtain ⟨f', Rf, HF⟩ := Rbody.eta_body_reflection hs hΓ hf
      exact ⟨_, Rf, HF.trans hΓ (.lamDF hA hA HB')⟩
  | etaBoth hf hg HB ih =>
    obtain ⟨⟨_, hA⟩, _⟩ := let ⟨_, ht⟩ := hf.isType henv hΓ; ht.forallE_inv henv
    have hΓA : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hA⟩
    obtain ⟨body', Rbody, HB'⟩ := ih hΓA (.appL (R.liftN 1 0))
    obtain ⟨f', Rf, HF⟩ := Rbody.eta_body_reflection hs hΓ hf
    exact ⟨_, Rf, HF.trans hΓ (.etaL (pattern_type hs hΓ R.toCompute hg) HB')⟩
  | proofIrrel hp ha hb => exact ⟨_, .refl, .proofIrrel hp ha (pattern_type hs hΓ R.toCompute hb)⟩

/-- Every finite compatible beta/delta path can be mirrored through ordinary normal
comparison by pattern computation. Both eta directions, extensionality, and annotation
reductions are covered; the final comparison still has opaque domain equalities. -/
theorem normal_pattern_simulation
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEqF η Γ a b) (R : PatternCompute D b b') :
    ∃ a', PatternCompute D a a' ∧ NormalEq Γ a' b' := by
  obtain ⟨n, H⟩ := H
  apply pattern_induct_steps hcon (P := fun y => ∃ x, PatternCompute D a x ∧ NormalEq Γ x y) R
  · exact ⟨_, .refl, _, H.toTrue⟩
  · intro x y R H
    obtain ⟨a1, R1, _, H1⟩ := H
    obtain ⟨a2, R2, H2⟩ := normal_pattern_step hs hl hΓ H1 R
    exact ⟨a2, R1.trans R2, H2⟩

omit [Params] hs hl in
/-- The original concrete core parallel reduction is covered. The collection of
extra closed equations may be any sound level-stable collection. -/
theorem normal_core_computation {env : VEnv} (henv : env.WF)
    (hs : D.Sound env U) (hl : D.LevelStable U) (hΓ : OnCtx Γ (env.IsType U))
    (H : @NormalEq (henv.params U) Γ a b) (R : @ParRed (henv.params U) Γ b b') :
    ∃ a', @PatternCompute (henv.params U) D a a' ∧ @NormalEq (henv.params U) Γ a' b' := by
  letI := henv.params U
  exact normal_pattern_simulation hs hl (fun hp => hp) hΓ H (PatternCompute.of_parRed henv R)

end Lean4Lean.VEnv.Strengthening.PureObservation
