import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCountedNativeTransport

/-! # Recover a counted lambda body in its original binder context

Changing annotations enlarge only the finite guard bound. The exact sum of
annotation and body primitive counts remains the original lambda count.
This does not assert substitution at an arbitrary argument or a fixed-stage
body readout.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

private theorem lambda_count_segment
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hΔ : proofEraseCtx Γ = Δ)
    (RA : ScopedComputeCount (PiInertStage D n) ca Δ (proofErase Γ A) rawA)
    (RB : ScopedComputeCount (PiInertStage D n) cb (proofErase Γ A :: Δ)
      (proofErase (A :: Γ) b) rawB) :
    ∃ A' b', env.IsDefEq univs Γ A A' (.sort u) ∧
      env.IsDefEq univs (A :: Γ) b b' B ∧
      proofErase Γ A' = rawA ∧ proofErase (A :: Γ) b' = rawB ∧
      ScopedComputeCount (PiInertStage D n) ca (proofEraseCtx Γ)
        (proofErase Γ A) (proofErase Γ A') ∧
      ScopedComputeCount (PiInertStage D n) cb (proofEraseCtx (A :: Γ))
        (proofErase (A :: Γ) b) (proofErase (A :: Γ) b') := by
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D n) :=
    ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n)
  obtain ⟨A', HA, EA⟩ := proofErase_scoped_compute_realize hd hΓ hA hΔ rfl RA.forget
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hd hΓA hb
    (congrArg (List.cons (proofErase Γ A)) hΔ) rfl RB.forget
  exact ⟨A', b', HA, HB, EA, EB, by simpa only [EA, hΔ] using RA,
    by simpa only [proofEraseCtx, EB, hΔ] using RB⟩

/-- Every typed Pi-inert lambda computation admits an exact body path in
its initial binder context at some finite guard stage. Domain computation
keeps its original stage, and the two component costs sum to the input cost.
Both output representatives retain semantic equality in their initial scopes. -/
theorem pi_inert_lambda_count_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hΔ : proofEraseCtx Γ = Δ)
    (R : ScopedComputeCount (PiInertStage D n) cost Δ
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) out) :
    ∃ A' b' ca cb m, ca+cb = cost ∧
      env.IsDefEq univs Γ A A' (.sort u) ∧ env.IsDefEq univs (A :: Γ) b b' B ∧
      out = .lam (proofErase Γ A') (proofErase (A :: Γ) b') ∧
      ScopedComputeCount (PiInertStage D n) ca (proofEraseCtx Γ)
        (proofErase Γ A) (proofErase Γ A') ∧
      ScopedComputeCount (PiInertStage D m) cb (proofEraseCtx (A :: Γ))
        (proofErase (A :: Γ) b) (proofErase (A :: Γ) b') := by
  generalize E : ProofShape.lam (proofErase Γ A) (proofErase (A :: Γ) b) = source at R
  induction R generalizing Γ A u b B with
  | base H => exact (pi_inert_stage_no_lam (E ▸ H)).elim
  | beta H =>
    cases E
    obtain ⟨rawA, rawB, EO, RA, RB⟩ := H.lam_inv
    obtain ⟨A', b', HA, HB, EA, EB, RA', RB'⟩ := lambda_count_segment heq hs hΓ hA hb hΔ
      (ScopedComputeCount.beta (Step := PiInertStage D n) RA) (.beta RB)
    exact ⟨A', b', 0, 0, n, rfl, HA, HB, by simpa only [EA, EB] using EO, RA', RB'⟩
  | lam RA RB =>
    cases E
    obtain ⟨A', b', HA, HB, EA, EB, RA', RB'⟩ := lambda_count_segment heq hs hΓ hA hb hΔ RA RB
    exact ⟨A', b', _, _, n, rfl, HA, HB, by rw [EA, EB], RA', RB'⟩
  | trans R₁ R₂ ih₁ ih₂ =>
    obtain ⟨A₁, b₁, ca₁, cb₁, m₁, hc₁, HA₁, HB₁, EO₁, RA₁, RB₁⟩ := ih₁ hΓ hA hb hΔ E
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have Hctx : IsDefEqCtx env univs Γ (A :: Γ) (A₁ :: Γ) := .succ .zero HA₁
    have hb₁ := HB₁.hasType.2.defeqDFC henv Hctx
    have EB₁ := proofErase_defeqCtx hΓA Hctx HB₁.hasType.2
    obtain ⟨A₂, b₂, ca₂, cb₂, m₂, hc₂, HA₂, HB₂, EO₂, RA₂, RB₂⟩ :=
      ih₂ hΓ HA₁.hasType.2 hb₁ hΔ (by rw [← EB₁]; exact EO₁.symm)
    have HB₂old := HB₂.defeqDFC henv (IsDefEqCtx.succ .zero HA₁.symm)
    have EB₂ := proofErase_defeqCtx hΓA Hctx HB₂old.hasType.2
    have RB₂old := pi_inert_compute_count_backward_context heq hs hΓ HA₁ RA₁.forget hb₁ RB₂
    rw [← EB₂] at RB₂old
    refine ⟨A₂, b₂, ca₁+ca₂, cb₁+cb₂, max m₁ (m₂+n), by omega,
      HA₁.trans HA₂, HB₁.trans HB₂old, ?_, RA₁.trans RA₂, ?_⟩
    · simpa only [← EB₂] using EO₂
    · exact (RB₁.mono (pi_inert_stage_mono (Nat.le_max_left _ _))).trans
        (RB₂old.mono (pi_inert_stage_mono (Nat.le_max_right _ _)))
  | app | proj | forallE => cases E

/-- A recovered native eta supplies the typed originals needed by lambda
readout. Its arbitrary changing-annotation history yields an exact counted
body path in the original raw binder context at a finite later stage. -/
theorem pi_inert_native_eta_count_body_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (HT : TypedSource Δ f)
    (H : NativeEtaExpansion Guard Δ f (.lam A body))
    (R : ScopedComputeCount (PiInertStage D n) cost Δ
      (.lam A body) (.lam A' body')) :
    ∃ ca cb m, ca+cb = cost ∧
      ScopedComputeCount (PiInertStage D n) ca Δ A A' ∧
      ScopedComputeCount (PiInertStage D m) cb (A :: Δ) body body' := by
  obtain ⟨Γ, f, T, hΓ, rfl, ht, rfl⟩ := HT
  cases H with
  | intro RN SD =>
    have W : Ctx.LiftN 0 0 Γ Γ := .zero []
    obtain ⟨D₀, B₀, hf, ED, _⟩ := proofErase_scoped_recovered_pi_descend hguard hΓ hΓ W ht
      (by simpa only [ProofShape.liftN_zero] using RN)
    obtain ⟨_, hPi⟩ := hf.isType henv hΓ
    obtain ⟨⟨_, hD⟩, _, _⟩ := hPi.forallE_inv henv
    have hD := (ED ▸ SD).descend hΓ hΓ W hD
    simp only [ProofShape.liftN_zero] at ED
    have hnf : ¬ IsProof Γ f := fun hp => RN.ne_proof (proofErase_eq_proof.2 hp)
    have hfw : env.HasType univs (D₀ :: Γ) f.lift
        (.forallE D₀.lift (B₀.liftN 1 1)) := hf.weak henv
    have hb : env.HasType univs (D₀ :: Γ) (.app f.lift (.bvar 0)) B₀ := by
      simpa only [VExpr.inst_liftN_bvar] using hfw.app (HasType.bvar .zero)
    have EB := proofErase_eta_body hΓ hD hf hnf
    obtain ⟨D₁, b₁, ca, cb, m, hc, _, _, EO, RA, RB⟩ := pi_inert_lambda_count_readout
      heq hs hΓ hD hb rfl (by simpa only [ED, EB] using R)
    obtain ⟨EA', EB'⟩ := ProofShape.lam.inj EO
    exact ⟨ca, cb, m, hc, by simpa only [ED, ← EA'] using RA,
      by simpa only [proofEraseCtx, ED, EB, ← EB'] using RB⟩

end Lean4Lean.VEnv.Strengthening
