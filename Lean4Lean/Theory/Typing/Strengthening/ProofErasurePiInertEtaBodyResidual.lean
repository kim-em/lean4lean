import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertMinimalSpineCut
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedEtaApplication

/-! # A minimum-count eta cut must compute its body beyond beta

Changing an eta annotation does not by itself prevent bypass. If the final
body is a beta reduct of its original body, instantiate only that beta path,
retain all argument computations, and save the eta primitive. No substitution
closure of the guarded primitive relation is needed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_spine_head from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
open private erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

private theorem native_eta_body_inst
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hx : env.HasType univs Γ x A)
    (H : NativeEtaExpansion Step (proofEraseCtx Γ) (proofErase Γ f) (.lam rawA body)) :
    body.inst (proofErase Γ x) = .app (proofErase Γ f) (proofErase Γ x) := by
  cases H with
  | intro R S =>
    have W : Ctx.LiftN 0 0 Γ Γ := .zero []
    obtain ⟨D, C, hfD, ED, _⟩ := proofErase_scoped_recovered_pi_descend hstep hΓ hΓ W hf
      (by simpa only [ProofShape.liftN_zero] using R)
    obtain ⟨_, hPi⟩ := hfD.isType henv hΓ
    obtain ⟨⟨_, hD⟩, _, _⟩ := hPi.forallE_inv henv
    have hD := (ED ▸ S).descend hΓ hΓ W hD
    have hxD := argument_at_displayed_domain hΓ hf hfD hx
    simp only [ProofShape.inst, proofErase_eta_argument_inst hΓ hD hxD]
    congr 1
    simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
      ProofShape.lift_subst_cons, ProofShape.subst_id]

/-- A beta-only evolution of the eta body can be replayed after its actual
computed argument, even if the annotation took arbitrary guarded steps. The
argument vector and suffix keep their exact primitive counts. -/
theorem pi_inert_eta_beta_body_count_bypass
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (HT : TypedSource Δ (ProofShape.mkApps f args))
    (H : NativeEtaExpansion Guard Δ f (.lam A body))
    (RB : ProofShape.BetaRed body body')
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca args (x' :: xs'))
    (RT : ScopedComputeCount (PiInertStage D n) ct Δ
      (ProofShape.mkApps (body'.inst x') xs') out) :
    ScopedComputeCount (PiInertStage D n) (ca+ct) Δ (ProofShape.mkApps f args) out := by
  cases RX with
  | cons RX RXS =>
    rename_i cx x cxs xs
    have HTapp : TypedSource Δ (.app f _) := typed_spine_head HT
    obtain ⟨Γ, e, T, hΓ, rfl, ht, Ee⟩ := HTapp
    obtain ⟨f₀, x₀, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
    obtain ⟨D₀, B₀, hf, hx⟩ := ht.app_inv henv hΓ
    obtain ⟨x₁, HX, EX⟩ := proofErase_scoped_compute_realize
      (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n))
      hΓ hx rfl Ex RX.forget
    have EH : body.inst x' = .app f x' := by
      rw [← EX, ← Ef]
      exact native_eta_body_inst hguard hΓ hf HX.hasType.2 (Ef.symm ▸ H)
    have RB' : ProofShape.BetaRed (.app f x') (body'.inst x') := by
      rw [← EH, ProofShape.inst_eq_subst, ProofShape.inst_eq_subst]
      exact RB.subst
    have RF : ScopedComputeCount (PiInertStage D n) (cx+cxs) (proofEraseCtx Γ)
        (ProofShape.mkApps f (x :: xs)) (ProofShape.mkApps (.app f x') xs') := by
      simpa only [Nat.zero_add, ProofShape.mkApps] using
        (ScopedComputeCount.beta (BetaRed.refl (e := f))).mkApps (.cons RX RXS)
    simpa only [Nat.zero_add] using RF.trans (((ScopedComputeCount.beta RB').mkApps ScopedArgumentsCount.refl).trans RT)

/-- Any counted first-beta decomposition of a globally minimal eta cut must
have a body that is not a beta reduct of the original eta body. In particular,
the lambda computation has positive primitive count. Prefix, all arguments
and the exact post-beta tail survive; annotation-only work cannot explain it. -/
theorem minimal_pi_inert_eta_cut_nonbeta_body
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (HT : TypedSource Δ (ProofShape.mkApps f args))
    (H : NativeEtaExpansion Guard Δ f (.lam A body))
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original (ProofShape.mkApps f args))
    (RT : ScopedComputeCount (PiInertStage D n) ct Δ (ProofShape.mkApps (.lam A body) args) out)
    (hcost : cp+1+ct ≤ cost)
    (hmin : ∀ k, ScopedComputeCount (PiInertStage D n) k Δ original out → cost ≤ k)
    (HE : CarrierExposure out) :
    ∃ A' body' x' xs' cf ca cs, cf+ca+cs ≤ ct ∧
      ScopedComputeCount (PiInertStage D n) cf Δ (.lam A body) (.lam A' body') ∧
      ScopedArgumentsCount (PiInertStage D n) Δ ca args (x' :: xs') ∧
      ScopedComputeCount (PiInertStage D n) cs Δ (ProofShape.mkApps (body'.inst x') xs') out ∧
      ¬ ProofShape.BetaRed body body' ∧ 0 < cf := by
  rcases RT.pi_inert_lambda_spine_or_beta with ⟨A', b', args', cf, ca, _, EO, _, _⟩ |
      ⟨A', b', x', xs', cf, ca, cs, hc, RF, RX, RS⟩
  · exact (HE.not_lambda_spine A' b' args' EO).elim
  · have HN : ¬ ProofShape.BetaRed body b' := by
      intro RB
      have RR := pi_inert_eta_beta_body_count_bypass heq hs hguard HT H RB RX RS
      have HM := hmin _ (RP.trans RR)
      omega
    refine ⟨A', b', x', xs', cf, ca, cs, hc, RF, RX, RS, HN, ?_⟩
    by_contra hz
    have hz : cf = 0 := by omega
    obtain ⟨_, _, EE, _, RB⟩ := (hz ▸ RF).zero_beta.lam_inv
    cases EE
    exact HN RB

end Lean4Lean.VEnv.Strengthening
