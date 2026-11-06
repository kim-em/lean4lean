import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEtaSpineBypass

/-! # Typed origins for retained eta endpoints

A component-only eta body descends to a counted short-function path. The
computed annotation and short function share an actual Pi typing. This
witness survives typed endpoint substitution without transporting either
the computation or a native recovery certificate.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private typed_spine_head from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
variable [Params]

/-- An actual nonproof function at the displayed eta domain, together with
that domain's sort. This records ordinary typing, not native type recovery. -/
def TypedEtaOrigin (Δ : List ProofShape) (A f : ProofShape) (u : VLevel) : Prop :=
  ∃ Γ a g B, OnCtx Γ (env.IsType univs) ∧ proofEraseCtx Γ = Δ ∧
    env.HasType univs Γ a (.sort u) ∧ env.HasType univs Γ g (.forallE a B) ∧
    ¬ IsProof Γ g ∧ proofErase Γ a = A ∧ proofErase Γ g = f

/-- The origin can be realized in any well-formed context with the same
erasure. Only ordinary context conversion is used. -/
theorem TypedEtaOrigin.realize (H : TypedEtaOrigin (proofEraseCtx Γ) A f u)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ a g B, env.HasType univs Γ a (.sort u) ∧
      env.HasType univs Γ g (.forallE a B) ∧ ¬ IsProof Γ g ∧
      proofErase Γ a = A ∧ proofErase Γ g = f := by
  obtain ⟨Γ₀, a, g, B, hΓ₀, EΓ, ha, hg, hn, Ea, Eg⟩ := H
  have W := proofEraseCtx_defeq hΓ₀ hΓ EΓ
  exact ⟨a, g, B, ha.defeqDFC henv W, hg.defeqDFC henv W,
    fun hp => hn ((isProof_defeqCtx W).2 hp),
    (proofErase_defeqCtx hΓ₀ W ha).symm.trans Ea,
    (proofErase_defeqCtx hΓ₀ W hg).symm.trans Eg⟩

/-- Endpoint substitution preserves the actual eta origin, including the
displayed domain and proof/nonproof classification of the fresh slot. -/
theorem TypedEtaOrigin.subst (H : TypedEtaOrigin Δ A f u)
    (W : ContextSubstitution Δ Ω τ) : TypedEtaOrigin Ω (A.subst τ) (f.subst τ) u := by
  obtain ⟨Γ, a, g, B, hΓ, EΓ, ha, hg, hn, Ea, Eg⟩ := H
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, HS, ES⟩ := W hΓ EΓ
  exact ⟨Γ₀, a.subst σ, g.subst σ, B.subst σ.lift, hΓ₀, EΓ₀,
    ha.subst henv.orderedStrong HS hΓ₀, hg.subst henv.orderedStrong HS hΓ₀,
    fun hp => hn ((isProof_subst hΓ₀ HS hg).1 hp),
    (proofErase_subst_with hΓ₀ HS ha ES).trans (congrArg (·.subst τ) Ea),
    (proofErase_subst_with hΓ₀ HS hg ES).trans (congrArg (·.subst τ) Eg)⟩

/-- The retained long endpoint is an actual typed eta lambda. Its written
annotation is the origin's current domain, rather than an older recovered one. -/
theorem TypedEtaOrigin.lambda_typed (H : TypedEtaOrigin Δ A f u) :
    TypedSource Δ (.lam A (.app (f.liftN 1) (etaArgument u))) := by
  obtain ⟨Γ, a, g, B, hΓ, EΓ, ha, hg, hn, Ea, Eg⟩ := H
  have hnl : ¬ IsProof Γ (.lam a (.app g.lift (.bvar 0))) :=
    fun hp => hn ((isProof_congr hΓ (IsDefEq.eta hg)).1 hp)
  refine ⟨Γ, .lam a (.app g.lift (.bvar 0)), .forallE a B, hΓ, EΓ,
    (IsDefEq.eta hg).hasType.1, ?_⟩
  rw [show proofErase Γ (.lam a (.app g.lift (.bvar 0))) =
    .lam (proofErase Γ a) (proofErase (a :: Γ) (.app g.lift (.bvar 0))) from if_neg hnl,
    proofErase_eta_body hΓ ha hg hn, Ea, Eg]

/-- An actual application of the short endpoint types its argument at the
retained domain. Consequently the fresh eta slot instantiates to that exact
argument, even when the slot is a proof marker. -/
theorem TypedEtaOrigin.argument_inst (H : TypedEtaOrigin Δ A f u)
    (HT : TypedSource Δ (.app f x)) :
    (ProofShape.app (f.liftN 1) (etaArgument u)).inst x = .app f x := by
  obtain ⟨Γ, e, T, hΓ, rfl, ht, Ee⟩ := HT
  obtain ⟨g, y, rfl, _, Eg, Ey⟩ := erase_app_inv Ee
  obtain ⟨C, B, hg, hy⟩ := ht.app_inv henv hΓ
  obtain ⟨a, g₀, B₀, ha, hg₀, hn₀, _, Eg₀⟩ := H.realize hΓ
  obtain ⟨_, HE⟩ := (proofErase_reflect hΓ hg₀ hg (Eg₀.trans Eg.symm)).2 hn₀
  have hg' := ((HE.defeq hΓ).of_l henv hΓ hg₀).hasType.2
  have hyA := argument_at_displayed_domain hΓ hg hg' hy
  rw [← Ey]
  simp only [ProofShape.inst, proofErase_eta_argument_inst hΓ ha hyA]
  congr 1
  simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
    ProofShape.lift_subst_cons, ProofShape.subst_id]

/-- A later computation of a retained eta lambda can again be read in its
current original binder context. This applies after endpoint substitution:
the typed origin replaces the unavailable native recovery certificate. -/
theorem TypedEtaOrigin.count_body_readout
    (H : TypedEtaOrigin Δ A f u) (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (R : ScopedComputeCount (PiInertStage D n) cost Δ
      (.lam A (.app (f.liftN 1) (etaArgument u))) (.lam A' body')) :
    ∃ ca cb m, ca+cb = cost ∧
      ScopedComputeCount (PiInertStage D n) ca Δ A A' ∧
      ScopedComputeCount (PiInertStage D m) cb (A :: Δ)
        (.app (f.liftN 1) (etaArgument u)) body' := by
  obtain ⟨Γ, a, g, B, hΓ, rfl, ha, hg, hn, rfl, rfl⟩ := H
  have hgw : env.HasType univs (a :: Γ) g.lift
      (.forallE a.lift (B.liftN 1 1)) := hg.weak henv
  have hb : env.HasType univs (a :: Γ) (.app g.lift (.bvar 0)) B := by
    simpa only [VExpr.inst_liftN_bvar] using hgw.app (HasType.bvar .zero)
  have EB := proofErase_eta_body hΓ ha hg hn
  obtain ⟨a', b', ca, cb, m, hc, _, _, EO, RA, RB⟩ := pi_inert_lambda_count_readout
    heq hs hΓ ha hb rfl (by simpa only [EB] using R)
  obtain ⟨EA', EB'⟩ := ProofShape.lam.inj EO
  exact ⟨ca, cb, m, hc, by simpa only [← EA'] using RA,
    by simpa only [proofEraseCtx, EB, ← EB'] using RB⟩

/-- If the eta body still only computes the lifted function at its later
consumption, bypass it at the exact endpoint and count. The origin can have
crossed a typed substitution; only the new scope's paths are replayed. -/
theorem TypedEtaOrigin.component_body_bypass
    (H : TypedEtaOrigin Δ A f u) (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ (ProofShape.mkApps f args))
    (RG : ScopedComputeCount (PiInertStage D m) cg (A :: Δ) (f.liftN 1) g)
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca args (x' :: xs'))
    (RS : ScopedComputeCount (PiInertStage D n) cs Δ
      (ProofShape.mkApps ((ProofShape.app g (etaArgument u)).inst x') xs') out) :
    ScopedComputeCount (PiInertStage D (max m n)) (cg+ca+cs) Δ
      (ProofShape.mkApps f args) out := by
  cases RX with
  | cons RX RXS =>
    have HTapp : TypedSource Δ (.app f _) := typed_spine_head HT
    obtain ⟨Γ, e, T, hΓ, rfl, ht, Ee⟩ := HTapp
    obtain ⟨f₀, x₀, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
    obtain ⟨C₀, B₀, hf₀, hx⟩ := ht.app_inv henv hΓ
    obtain ⟨a, f₁, B₁, ha, hf₁, hn₁, Ea, Ef₁⟩ := H.realize hΓ
    obtain ⟨_, HE⟩ := (proofErase_reflect hΓ hf₁ hf₀ (Ef₁.trans Ef.symm)).2 hn₁
    have hf := ((HE.defeq hΓ).of_l henv hΓ hf₁).hasType.2
    have hΓa : OnCtx (a :: Γ) (env.IsType univs) := ⟨hΓ, u, ha⟩
    obtain ⟨f₂, _, RF, EF⟩ := proofErase_scoped_compute_count_descend
      (pi_inert_stage_rule_descent heq hs) hΓ hΓa Ctx.LiftN.one hf
      (congrArg (fun rawA => rawA :: proofEraseCtx Γ) Ea)
      (by simpa only [Ef] using RG)
    obtain ⟨x₁, HX, EX⟩ := proofErase_scoped_compute_realize
      (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n))
      hΓ hx rfl Ex RX.forget
    have hxA := argument_at_displayed_domain hΓ hf₀ hf HX.hasType.2
    have EB : (ProofShape.app g (etaArgument u)).inst x' = .app (proofErase Γ f₂) x' := by
      rw [← EF, ← EX]
      simp only [ProofShape.inst, proofErase_eta_argument_inst hΓ ha hxA]
      congr 1
      simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
        ProofShape.lift_subst_cons, ProofShape.subst_id]
    have RF' := (Ef ▸ RF).mono (pi_inert_stage_mono (Nat.le_max_left m n))
    have RX' := (ScopedArgumentsCount.cons RX RXS).mono (pi_inert_stage_mono (Nat.le_max_right m n))
    exact (RF'.mkApps RX').trans (by
      simpa only [ProofShape.mkApps, EB] using RS.mono (pi_inert_stage_mono (Nat.le_max_right m n)))

/-- The actual computed first argument interprets the later eta binder.
This supplies a concrete application frame after substitution has removed
the original native recovery certificate. Only ordinary Pi typing is used. -/
theorem TypedEtaOrigin.body_interpretation
    (H : TypedEtaOrigin Δ A f u) (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ (ProofShape.mkApps f args))
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca args (x' :: xs')) :
    ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x') := by
  cases RX with
  | cons RX _ =>
    have HTapp : TypedSource Δ (.app f _) := typed_spine_head HT
    obtain ⟨Γ, e, T, hΓ, rfl, ht, Ee⟩ := HTapp
    obtain ⟨f₀, x₀, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
    obtain ⟨C₀, B₀, hf₀, hx⟩ := ht.app_inv henv hΓ
    obtain ⟨a, f₁, B₁, ha, hf₁, hn₁, Ea, Ef₁⟩ := H.realize hΓ
    obtain ⟨_, HE⟩ := (proofErase_reflect hΓ hf₁ hf₀ (Ef₁.trans Ef.symm)).2 hn₁
    have hf := ((HE.defeq hΓ).of_l henv hΓ hf₁).hasType.2
    have hΓa : OnCtx (a :: Γ) (env.IsType univs) := ⟨hΓ, u, ha⟩
    obtain ⟨x₁, HX, EX⟩ := proofErase_scoped_compute_realize
      (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n))
      hΓ hx rfl Ex RX.forget
    have hxA := argument_at_displayed_domain hΓ hf₀ hf HX.hasType.2
    have WI : ContextSubstitution (proofEraseCtx (a :: Γ)) (proofEraseCtx Γ)
        (ProofShape.Subst.one (proofErase Γ x₁)) :=
      ContextSubstitution.of_typed hΓ (Ctx.InstN.zero.substEq hΓa hxA)
        (erasedSubstAgreement_one hΓa hxA)
    rw [proofEraseCtx, Ea, EX] at WI
    intro Γ' hΓ' EΓ'
    exact WI hΓ' EΓ'

/-- Read a component-only retained eta body back to its short function with
the exact body-function count. Annotation computation converts its actual Pi
typing to the displayed endpoint domain. No path is substituted. -/
theorem pi_inert_retained_eta_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (HT : TypedSource Δ f)
    (RN : ScopedTypeRecovery Guard Δ f (.forallE A B)) (SD : DomainSort Δ A u)
    (RD : ScopedComputeCount (PiInertStage D n) cd Δ A A')
    (RG : ScopedComputeCount (PiInertStage D m) cg (A :: Δ) (f.liftN 1) g) :
    ∃ short, ScopedComputeCount (PiInertStage D m) cg Δ f short ∧
      g = short.liftN 1 ∧ TypedEtaOrigin Δ A' short u := by
  obtain ⟨Γ, f₀, T, hΓ, rfl, ht, rfl⟩ := HT
  have W : Ctx.LiftN 0 0 Γ Γ := .zero []
  obtain ⟨a, C, hf, Ea, _⟩ := proofErase_scoped_recovered_pi_descend hguard hΓ hΓ W ht
    (by simpa only [ProofShape.liftN_zero] using RN)
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨_, ha⟩, _, hC⟩ := hPi.forallE_inv henv
  have ha := (Ea ▸ SD).descend hΓ hΓ W ha
  simp only [ProofShape.liftN_zero] at Ea
  obtain ⟨a', HA, Ea'⟩ := proofErase_scoped_compute_realize
    (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n))
    hΓ ha rfl Ea RD.forget
  have hΓa : OnCtx (a :: Γ) (env.IsType univs) := ⟨hΓ, u, ha⟩
  obtain ⟨f', HF, RF, Ef'⟩ := proofErase_scoped_compute_count_descend
    (pi_inert_stage_rule_descent heq hs) hΓ hΓa Ctx.LiftN.one hf
    (congrArg (fun rawA => rawA :: proofEraseCtx Γ) Ea) RG
  have hn : ¬ IsProof Γ f₀ := fun hp => RN.ne_proof (proofErase_eq_proof.2 hp)
  exact ⟨_, RF, Ef'.symm, Γ, a', f', C, hΓ, rfl, HA.hasType.2,
    (IsDefEq.forallEDF HA hC).defeq HF.hasType.2,
    fun hp => hn ((isProof_congr hΓ HF).2 hp), Ea', rfl⟩

end Lean4Lean.VEnv.Strengthening
