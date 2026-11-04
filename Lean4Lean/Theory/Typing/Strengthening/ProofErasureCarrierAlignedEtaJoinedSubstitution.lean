import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedEtaJoinedRepair
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedJoinedNativeImages

/-! # Eta repair after substitution by joined native images

Pure controlled-beta native recovery transports to beta-only native evidence
modulo a raw join. The eta annotation repair then realizes a common reduct at
eta stage one, instead of demanding the exact substituted native Pi.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Joined native images suffice to transport a pure recovered eta demand to
a common reduct. The source native guard may have arbitrary controlled-beta
depth; the target uses eta stage one. Neither the target context nor its image
syntax is required to be pure, and exact native image recovery is not assumed. -/
theorem proofErase_eta_joined_native_subst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (HΔ : PureContext (proofEraseCtx Γ)) (HF : PureLambda (proofErase Γ f))
    (RN : ScopedTypeRecovery (ErasedExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ f)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)))
    (HI : JoinedNativeImages (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ) :
    ∃ common, ScopedCompute (ErasedEtaExpansionStage D 1) (proofEraseCtx Γ₀)
        (proofErase Γ₀ (f.subst σ)) common ∧
      ScopedCompute (fun _ => LevelPrimitive univs) (proofEraseCtx Γ₀)
        (proofErase Γ₀ (.lam (A.subst σ) (.app (f.subst σ).lift (.bvar 0)))) common := by
  obtain ⟨native, R, HJ⟩ := erased_expansion_union_native_joined_subst RN HΔ HF HI
  have hA₀ := hA.subst henv.orderedStrong W hΓ₀
  have hf₀ := hf.subst henv.orderedStrong W hΓ₀
  obtain ⟨_, hPi⟩ := hf.isType henv W.wf
  obtain ⟨_, _, hB⟩ := hPi.forallE_inv henv
  have hΓA₀ : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) := ⟨hΓ₀, u, hA₀⟩
  have EB := proofErase_subst_with hΓA₀ (W.lift henv.ordered hA) hB (ES.lift hΓ₀ W hA)
  rw [← proofErase_subst_with hΓ₀ W hf ES] at R
  change BetaLevelJoin native
    (.forallE ((proofErase Γ A).subst τ) ((proofErase (A :: Γ) B).subst τ.lift)) at HJ
  rw [← proofErase_subst_with hΓ₀ W hA ES, ← EB] at HJ
  exact proofErase_eta_stage_joined_native_square (k := 0) heq hs hΓ₀ hA₀ hf₀
    (R.mono (fun H => H.elim)) HJ

end Lean4Lean.VEnv.Strengthening
