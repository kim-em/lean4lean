import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaJoinedTypeRepair

/-! # Native eta substitution from a joined guard image

The substituted native Pi need not itself be recovered. An independently
recovered target type and the substituted Pi may compute to a common type;
eta-aware Pi readout then joins the short image with the exact long image.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Native eta transports to a common reduct when its selected type has a
joined native image. Both residuals start at the exact substituted raw shapes.
The source guard relation is arbitrary subject to typed descent; no purity,
exact assigned-type recovery, or exact native argument image is required. -/
theorem proofErase_native_eta_subst_of_joined_guard
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hrec : ErasedScopedPrimitiveDescent Recovery)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (hf : env.HasType univs Γ f T)
    (RN : ScopedTypeRecovery Recovery (proofEraseCtx Γ) (proofErase Γ f) (.forallE X Y))
    (SD : DomainSort (proofEraseCtx Γ) X u)
    (RI : ScopedTypeRecovery (ErasedEtaExpansionUnion D) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (f.subst σ)) native)
    (RP : ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ₀)
      ((ProofShape.forallE X Y).subst τ) common)
    (RT : ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ₀) native common) :
    ∃ shared, ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ₀)
        ((proofErase Γ f).subst τ) shared ∧
      ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ₀)
        ((ProofShape.lam X (.app ((proofErase Γ f).liftN 1) (etaArgument u))).subst τ) shared := by
  obtain ⟨A, B, hfPi, EA, EB⟩ := proofErase_scoped_recovered_pi_descend hrec W.wf W.wf
    (show Ctx.LiftN 0 0 Γ Γ from .zero []) hf
    (by simpa only [ProofShape.liftN_zero] using RN)
  simp only [ProofShape.liftN_zero] at EA EB
  obtain ⟨_, hPi⟩ := hfPi.isType henv W.wf
  obtain ⟨⟨_, hA⟩, _, hB⟩ := hPi.forallE_inv henv
  have SD' : DomainSort (proofEraseCtx Γ) ((proofErase Γ A).liftN 0) u := by
    simpa only [ProofShape.liftN_zero, EA] using SD
  have hAu := SD'.descend W.wf W.wf (Ctx.LiftN.zero []) hA
  have hA₀ := hAu.subst henv.orderedStrong W hΓ₀
  have hf₀ : env.HasType univs Γ₀ (f.subst σ) (.forallE (A.subst σ) (B.subst σ.lift)) :=
    hfPi.subst henv.orderedStrong W hΓ₀
  have hΓA₀ : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) := ⟨hΓ₀, u, hA₀⟩
  have EAs := proofErase_subst_with hΓ₀ W hAu ES
  have EBs := proofErase_subst_with hΓA₀ (W.lift henv.ordered hAu) hB (ES.lift hΓ₀ W hAu)
  rw [EA] at EAs
  rw [EB] at EBs
  have RP' := RP
  change ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ₀)
    (.forallE (X.subst τ) (Y.subst τ.lift)) common at RP'
  rw [← EAs, ← EBs] at RP'
  obtain ⟨shared, RS, RL⟩ := proofErase_eta_union_joined_type_square heq hs hΓ₀ hA₀ hf₀ RI RP' RT
  have hn₀ : ¬ IsProof Γ₀ (f.subst σ) := fun hp => RI.ne_proof (proofErase_eq_proof.2 hp)
  rw [proofErase_nativeEtaExpansion hΓ₀ hA₀ hf₀ hn₀, EAs,
    proofErase_subst_with hΓ₀ W hf ES] at RL
  rw [proofErase_subst_with hΓ₀ W hf ES] at RS
  exact ⟨shared, RS, by simpa only [ProofShape.subst, ProofShape.lift_subst_lift, etaArgument_subst] using RL⟩

end Lean4Lean.VEnv.Strengthening
