import Lean4Lean.Theory.Typing.Strengthening.PatternSpineTransport

/-! # Root iota transport using pattern computation alone

A concrete ordinary or quotient iota step can be mirrored through arbitrary
normal comparison without adding eta reductions. The existing large-elimination
guards are retained; this does not cover singleton-prefix unfolding at Prop.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A

/-- Every enabled concrete iota rule transports at all renamed application
spines using pattern computation alone. The constructor-major function cases
are excluded by the original redex typing, rather than eta expansion. -/
theorem pattern_iota_transport (hs : D.Sound env univs)
    {r : (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).RHS ×
      (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).Check}
    (hp : Pat (.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) r)
    (hconcrete : ConcretePattern env (.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) r)
    (hm : (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).Matches e m1 m2)
    (hc : r.2.OK (IsDefEqU env univs Γ) m1 m2) :
    ∀ n, PatternSpineTransport D Γ e (r.1.apply m1 m2) n := by
  have hstep : ParRed Γ e (r.1.apply m1 m2) := .extra hp hm hc (fun _ => .rfl)
  obtain ⟨F, M, lsc, g1, g2, hF, hM, rfl, rfl⟩ :
      ∃ F M lsc g1 g2, ((Pattern.const rc).varN mr).Matches F m1 g1 ∧
        ((Pattern.const cc).varN kc).Matches M lsc g2 ∧ e = .app F M ∧ m2 = Sum.elim g1 g2 := by
    cases hm with | app hF hM => exact ⟨_, _, _, _, _, hF, hM, rfl, rfl⟩
  obtain ⟨vsF, rfl⟩ : ∃ vs, F = VExpr.mkApps (.const rc m1) vs := ⟨_, hF.const_arguments⟩
  obtain ⟨fsM, rfl⟩ : ∃ fs, M = VExpr.mkApps (.const cc lsc) fs := ⟨_, hM.const_arguments⟩
  -- target of the step, lifted
  have fire : ∀ {ρ Γ' ls₁ vs₁ M₁ T Tℓ}, OnCtx Γ' (env.IsType univs) → Ctx.Lift' ρ Γ Γ' →
      List.Forall₂ (· ≈ ·) ls₁ m1 → List.Forall₂ (NormalEq Γ') vs₁ (vsF.map (·.lift' ρ)) →
      NormalEq Γ' M₁ ((VExpr.mkApps (.const cc lsc) fsM).lift' ρ) →
      Γ' ⊢ (VExpr.app (VExpr.mkApps (.const rc m1) vsF) (VExpr.mkApps (.const cc lsc) fsM)).lift' ρ : Tℓ →
      Γ' ⊢ .app (VExpr.mkApps (.const rc ls₁) vs₁) M₁ : T →
      ∃ X, PatternCompute D (.app (VExpr.mkApps (.const rc ls₁) vs₁) M₁) X ∧
        NormalEq Γ' X ((r.1.apply (p := .app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) m1 (Sum.elim g1 g2)).lift' ρ) := by
    intro ρ Γ' ls₁ vs₁ M₁ T Tℓ hΓ W hls hvs hMr hEt ht
    simp only [VExpr.lift', VExpr.lift'_mkApps] at hEt hMr
    have hFℓ : ((Pattern.const rc).varN mr).Matches
        (VExpr.mkApps (.const rc m1) (vsF.map (·.lift' ρ))) m1 (fun a => (g1 a).lift' ρ) := by
      have := (Pattern.matches_lift' (ρ := ρ)).2 ⟨_, hF, fun _ => rfl⟩
      simpa only [VExpr.lift'_mkApps, VExpr.lift'] using this
    have hMℓ : ((Pattern.const cc).varN kc).Matches
        (VExpr.mkApps (.const cc lsc) (fsM.map (·.lift' ρ))) lsc (fun a => (g2 a).lift' ρ) := by
      have := (Pattern.matches_lift' (ρ := ρ)).2 ⟨_, hM, fun _ => rfl⟩
      simpa only [VExpr.lift'_mkApps, VExpr.lift'] using this
    have hval : (fun a => (Sum.elim g1 g2 a).lift' ρ) =
        Sum.elim (fun a => (g1 a).lift' ρ) (fun a => (g2 a).lift' ρ) := by
      funext a; cases a <;> rfl
    have hEℓ := Pattern.Matches.app hFℓ hMℓ
    have hcℓ := (hc.weak' W).congr_values
      (p := Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc))
      (m' := Sum.elim (fun a => (g1 a).lift' ρ) (fun a => (g2 a).lift' ρ))
      (fun a => by cases a <;> rfl)
    have hstepℓ := hstep.weak' W
    simp only [VExpr.lift', VExpr.lift'_mkApps] at hstepℓ
    -- typing and the comparison with the lifted redex
    obtain ⟨_, _, hft, hMt⟩ := ht.app_inv henv hΓ
    obtain ⟨_, _, hFt, hMℓt⟩ := hEt.app_inv henv hΓ
    obtain ⟨_, hh₁⟩ := mkApps_head_type hΓ hft
    obtain ⟨_, hh⟩ := mkApps_head_type hΓ hFt
    obtain ⟨ci, hci, hw₁, hlen₁⟩ := hh₁.const_inv henv hΓ
    obtain ⟨_, _, hw, _⟩ := hh.const_inv henv hΓ
    have hhead : NormalEq Γ' (.const rc ls₁) (.const rc m1) := .constDF hci hw₁ hw hlen₁ hls
    have hnF := NormalEq.mkApps_spine hΓ hhead hvs hft
    have hFt' := ((hnF.defeq hΓ).of_l henv hΓ hft).hasType.2
    have hMt' := ((hMr.defeq hΓ).of_l henv hΓ hMt).hasType.2
    have hxE : NormalEq Γ' (.app (VExpr.mkApps (.const rc ls₁) vs₁) M₁) _ :=
      .appDF hft hFt' hMt hMt' hnF hMr
    have hxT : Γ' ⊢ .app (VExpr.mkApps (.const rc ls₁) vs₁) M₁ : Tℓ :=
      hEt.defeqU_l henv hΓ (hxE.defeq hΓ).symm
    have hrhsT := hstepℓ.hasType hΓ hEt
    obtain ⟨k, HM⟩ := hMr
    rcases normal_spine_expose_beta hΓ .const k HM (bs := []) .nil hMt with
      hprop | ⟨h', fs₂, he, hred, hfs⟩ | ⟨A', g, m, targs₁, B', _, _, _, hrel, hty⟩ | ⟨z, A', B', m, targs₁, _, _, _, _, hrel, hty⟩
    · have hMℓP := hMt.defeqU_l henv hΓ (HM.defeq hΓ)
      have hTℓ := Params.major_proof hΓ hp hEℓ hcℓ hEt hMℓP hprop
      exact ⟨_, .refl, .proofIrrel hTℓ hxT hrhsT⟩
    · obtain ⟨lsc₂, rfl, hlsc⟩ : ∃ lsc₂, h' = .const cc lsc₂ ∧ List.Forall₂ (· ≈ ·) lsc₂ lsc := by
        cases he with | const h => exact ⟨_, rfl, h⟩
      simp only [List.append_nil] at hfs
      obtain ⟨m3₁, hm3₁, hr₁⟩ := Pattern.Matches.constVarN_transport mr hFℓ hvs (ls' := ls₁)
      obtain ⟨m3₂, hm3₂, hr₂⟩ := Pattern.Matches.constVarN_transport kc hMℓ hfs (ls' := lsc₂)
      have hm₃ := Pattern.Matches.app hm3₁ hm3₂
      have hrel3 : ∀ a, NormalEq Γ' (Sum.elim m3₁ m3₂ a)
          (Sum.elim (fun a => (g1 a).lift' ρ) (fun a => (g2 a).lift' ρ) a) := by
        intro a; cases a with
        | inl a => exact hr₁ a
        | inr a => exact hr₂ a
      have hc₃ := hcℓ.normal_congr hΓ (ls₁ := ls₁)
        (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.symm) (Lean4Lean.List.Forall₂.flip hls))
        hw hw₁ (fun a => (hrel3 a).symm hΓ)
      have hred₃ : PatternCompute D (.app (VExpr.mkApps (.const rc ls₁) vs₁) M₁)
          (.app (VExpr.mkApps (.const rc ls₁) vs₁) (VExpr.mkApps (.const cc lsc₂) fs₂)) :=
        PatternCompute.app .refl (.of_beta hred)
      have hfire : PatternCompute D _ _ := .pattern hp hm₃
        (ConcretePattern.checkFromTyping henv hconcrete hc₃)
      have htot := hred₃.trans hfire
      have hT4 := (htot.simAt hs hΓ _ ht).hasType.2
      refine ⟨_, htot, ?_⟩
      rw [Pattern.RHS.lift'_apply (p := .app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) (r := r.1) (m1 := m1) (m2 := Sum.elim g1 g2) (ρ := ρ)]
      exact NormalEq.apply_congr hΓ r.1 hls hw₁ hw
        (fun a => by cases a <;> exact hrel3 _) hT4
    · exfalso
      simp only [List.append_nil] at hrel
      obtain ⟨_, hcc⟩ := mkApps_head_type hΓ hty
      have hMℓ' := NormalEq.mkApps_spine hΓ (NormalEq.refl hcc) hrel hty
      have hpi := hty.defeqU_l henv hΓ (hMℓ'.defeq hΓ)
      exact Params.major_not_pi hΓ hp hEℓ hEt hpi
    · exfalso
      simp only [List.append_nil] at hrel
      obtain ⟨_, hcc⟩ := mkApps_head_type hΓ hty
      have hMℓ' := NormalEq.mkApps_spine hΓ (NormalEq.refl hcc) hrel hty
      have hpi := hty.defeqU_l henv hΓ (hMℓ'.defeq hΓ)
      exact Params.major_not_pi hΓ hp hEℓ hEt hpi
  have fire' : ∀ {ρ Γ' ls₁ vs₁ M₁ T Tℓ}, OnCtx Γ' (env.IsType univs) → Ctx.Lift' ρ Γ Γ' →
      List.Forall₂ (· ≈ ·) ls₁ m1 → List.Forall₂ (NormalEq Γ') vs₁ (vsF.map (·.lift' ρ)) →
      NormalEq Γ' M₁ ((VExpr.mkApps (.const cc lsc) fsM).lift' ρ) →
      Γ' ⊢ (VExpr.app (VExpr.mkApps (.const rc m1) vsF)
        (VExpr.mkApps (.const cc lsc) fsM)).lift' ρ : Tℓ →
      Γ' ⊢ .app (VExpr.mkApps (.const rc ls₁) vs₁) M₁ : T →
      ∃ X, PatternCompute D (.app (VExpr.mkApps (.const rc ls₁) vs₁) M₁) X ∧
        NormalEq Γ' X ((r.1.apply (p := .app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) m1 (Sum.elim g1 g2)).lift' ρ) := fire
  exact pattern_redex_transport hs (hd := fun ls => .const rc ls) (fun _ => .const) (fun _ _ => rfl)
    (fun he => by cases he with | const h => exact ⟨_, rfl, h⟩) fire'

/-- The unrenamed root-rule consequence: ordinary normal comparison followed
by one concrete iota contraction is computation followed by normal comparison. -/
theorem normal_iota_compute (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    {r : (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).RHS ×
      (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).Check}
    (hp : Pat (.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) r)
    (hconcrete : ConcretePattern env (.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) r)
    (hm : (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).Matches e ls values)
    (hc : r.2.OK (IsDefEqU env univs Γ) ls values) (H : NormalEq Γ x e) :
    ∃ out, PatternCompute D x out ∧ NormalEq Γ out (r.1.apply ls values) := by
  obtain ⟨n, H⟩ := H
  have H' : NormalEqN true n Γ x (mkApps (e.lift' .refl) []) := by simpa using H
  simpa only [lift'_refl, mkApps, List.foldl] using
    pattern_iota_transport hs hp hconcrete hm hc n hΓ Ctx.Lift'.refl H'

end Lean4Lean.VEnv.Strengthening.PureObservation
