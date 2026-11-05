import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIdentityCarrierExposure

/-! # Recursive carrier exposure from comparison and record cases

Written identity annotations close the function, computation, symmetry, and
subsingleton cases of the full carrier grammar. Common comparison and record
exposure remain explicit hypotheses; they are not assumed complete elsewhere.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : Definitions}

private def CarrierExposureAt (D : Definitions) (Δ : List ProofShape)
    (kind : JointCheckKind) (x y : ProofShape) : Prop :=
  match kind with
  | .compare _ => True
  | .carrier C => ∀ {Γ A a b}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ a A → env.HasType univs Γ b A →
      proofEraseCtx Γ = Δ → proofErase Γ A = C → proofErase Γ a = x → proofErase Γ b = y →
      IdentityCarrierExposure D Δ C x y

/-- The full recursive carrier grammar needs exposure cases only for common
comparison and registered record families once typed lower computations
simulate at stage one. Both hypotheses remain open, and the record hypothesis
covers all carrier certificates at such a family, not only a chosen fragment.
This is a conditional reduction, not a proof of exposure completeness. -/
theorem identity_carrier_exposure_of_comparison_and_record_cases
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hstep : ErasedScopedPrimitiveDescent Source)
    (hcompute : ∀ {Δ a b}, TypedSource Δ a → ScopedCompute Source Δ a b →
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b)
    (HC : ∀ {Γ A a b}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ a A → env.HasType univs Γ b A →
      ComputedJointCompare Source (proofEraseCtx Γ) true (proofErase Γ a) (proofErase Γ b) →
      IdentityCarrierExposure D (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ a) (proofErase Γ b))
    (HR : ∀ {Γ A a b family info ls ps}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ a A → env.HasType univs Γ b A → env.projections family info →
      proofErase Γ A = ProofShape.mkApps (.const family ls) ps →
      ComputedJointCarrierGuard Source (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ a) (proofErase Γ b) →
      IdentityCarrierExposure D (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ a) (proofErase Γ b))
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (HG : ComputedJointCarrierGuard Source (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ a) (proofErase Γ b)) :
    IdentityCarrierExposure D (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ a) (proofErase Γ b) := by
  have general {Δ kind x y} (H : ComputedJointCheck Source Δ kind x y) : CarrierExposureAt D Δ kind x y := by
    induction H with
    | leaf | app | appCarrier | appComputed | proj | lam | forallE | lamSorted | forallSorted |
        lamCommon | etaBodyL | etaBodyR | structFields | etaLams | compute | symm => trivial
    | carrierChecked H _ =>
      intro Γ A a b hΓ ha hb EΓ EA Ea Eb
      have HE := HC hΓ ha hb (by simpa only [EΓ, Ea, Eb] using H)
      simpa only [EΓ, EA, Ea, Eb] using HE
    | carrierSubsingleton H =>
      intro Γ A a b hΓ ha hb EΓ EA Ea Eb
      exact .of_guard (.carrierSubsingleton H)
    | carrierSymm _ ih =>
      intro Γ A a b hΓ ha hb EΓ EA Ea Eb
      exact (ih hΓ hb ha EΓ EA Eb Ea).symm
    | carrierCompute R _ ih =>
      intro Γ A a b hΓ ha hb EΓ EA Ea Eb
      obtain ⟨u, hA⟩ := ha.isType henv hΓ
      obtain ⟨A', HE, EA'⟩ := proofErase_scoped_compute_realize hstep hΓ hA EΓ EA R
      exact (ih hΓ (HE.defeq ha) (HE.defeq hb) EΓ EA' Ea Eb).carrier_compute
        (hcompute ⟨Γ, A, _, hΓ, EΓ, hA, EA⟩ R)
    | carrierReduce Ra Rb _ ih =>
      intro Γ A a b hΓ ha hb EΓ EA Ea Eb
      obtain ⟨a', HA, Ea'⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea Ra
      obtain ⟨b', HB, Eb'⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb Rb
      exact (ih hΓ HA.hasType.2 HB.hasType.2 EΓ EA Ea' Eb').reduce
        (hcompute ⟨Γ, a, _, hΓ, EΓ, ha, Ea⟩ Ra)
        (hcompute ⟨Γ, b, _, hΓ, EΓ, hb, Eb⟩ Rb)
    | @carrierFunction Δraw Araw u Braw araw braw SD _ ih =>
      intro Γ A a b hΓ ha hb EΓ EA Ea Eb
      obtain ⟨X, Y, rfl, _, EX, EY⟩ := erase_forallE_inv EA
      obtain ⟨_, hPi⟩ := ha.isType henv hΓ
      obtain ⟨⟨_, hX₀⟩, _, hY⟩ := hPi.forallE_inv henv
      have SD' : DomainSort (proofEraseCtx Γ) ((proofErase Γ X).liftN 0 0) u := by
        simpa only [ProofShape.liftN_zero, EΓ, EX] using SD
      have hX := SD'.descend hΓ hΓ (Ctx.LiftN.zero []) hX₀
      by_cases hpa : IsProof Γ a
      · have hpb := isProof_of_common_type hΓ ha hb hpa
        have Eap := (proofErase_eq_proof.2 hpa).symm.trans Ea
        have Ebp := (proofErase_eq_proof.2 hpb).symm.trans Eb
        rw [← Eap, ← Ebp]
        exact .of_guard (.carrierChecked (.leaf .refl))
      have hpb : ¬ IsProof Γ b := fun H => hpa (isProof_of_common_type hΓ hb ha H)
      have hΓX : OnCtx (X :: Γ) (env.IsType univs) := ⟨hΓ, _, hX⟩
      have hfa : env.HasType univs (X :: Γ) (.app a.lift (.bvar 0)) Y := by
        simpa only [VExpr.lift, VExpr.liftN, inst_liftN_bvar] using
          HasType.app (ha.weak henv) (HasType.bvar .zero)
      have hfb : env.HasType univs (X :: Γ) (.app b.lift (.bvar 0)) Y := by
        simpa only [VExpr.lift, VExpr.liftN, inst_liftN_bvar] using
          HasType.app (hb.weak henv) (HasType.bvar .zero)
      have HI := ih hΓX hfa hfb (by simp only [proofEraseCtx, EX, EΓ]) EY
        (by simpa only [Ea] using proofErase_eta_body hΓ hX ha hpa)
        (by simpa only [Eb] using proofErase_eta_body hΓ hX hb hpb)
      have HE := IdentityCarrierExposure.function heq hs hΓ hX hY ha hb
        (by simpa only [proofEraseCtx, EΓ, EX, EY, proofErase_eta_body hΓ hX ha hpa,
          proofErase_eta_body hΓ hX hb hpb, Ea, Eb] using HI)
      simpa only [EΓ, EA, Ea, Eb] using HE
    | carrierIntro hi hx hp hadm Hfields _ =>
      intro Γ A a b hΓ ha hb EΓ EA Ea Eb
      have HE := HR hΓ ha hb hi EA (by
        simpa only [EΓ, EA, Ea, Eb] using ComputedJointCheck.carrierIntro hi hx hp hadm Hfields)
      simpa only [EΓ, EA, Ea, Eb] using HE
    | carrierNested hi hx hp hadm HT Hfields _ =>
      intro Γ A a b hΓ ha hb EΓ EA Ea Eb
      have HE := HR hΓ ha hb hi EA (by
        simpa only [EΓ, EA, Ea, Eb] using ComputedJointCheck.carrierNested hi hx hp hadm HT Hfields)
      simpa only [EΓ, EA, Ea, Eb] using HE
  exact general HG hΓ ha hb rfl rfl rfl rfl

end Lean4Lean.VEnv.Strengthening
