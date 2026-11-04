import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedNativeEtaExpansion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedEtaBeta
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedEtaStages

/-! # The function-computation residual of native eta

Computing a short function to a lambda also computes its selected eta expansion
to a lambda with exactly the same body. Only the outer annotations can differ.
The computation can use arbitrary guarded rules; ordinary typed replay fixes
the fresh argument's proof status without recovering the computed function.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

/-- A computation to a lambda can run inside a selected native eta expansion,
then beta restores exactly the computed body's erasure. The selected domain
stays fixed. No native output for the computed function or its fresh argument
is assumed, and the domain may classify that argument as an erased proof. -/
theorem proofErase_native_eta_function_lambda_residual
    (hrec : ErasedScopedPrimitiveDescent Recovery)
    (hfun : ErasedScopedPrimitiveDescent Source)
    (hrename : ∀ {Δ Δ' a b τ}, Source Δ a b → ContextRenaming Δ Δ' τ →
      Target Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f T)
    (RN : ScopedTypeRecovery Recovery (proofEraseCtx Γ) (proofErase Γ f) (.forallE X Y))
    (SD : DomainSort (proofEraseCtx Γ) X u)
    (RF : ScopedCompute Source (proofEraseCtx Γ) (proofErase Γ f) (.lam A b)) :
    ScopedCompute Target (proofEraseCtx Γ)
      (.lam X (.app ((proofErase Γ f).liftN 1) (etaArgument u))) (.lam X b) := by
  obtain ⟨D, C, hfD, ED, _⟩ := proofErase_scoped_recovered_pi_descend hrec hΓ hΓ
    (show Ctx.LiftN 0 0 Γ Γ from .zero []) hf
    (by simpa only [ProofShape.liftN_zero] using RN)
  simp only [ProofShape.liftN_zero] at ED
  obtain ⟨_, hPi⟩ := hfD.isType henv hΓ
  obtain ⟨⟨_, hD⟩, _⟩ := hPi.forallE_inv henv
  have SD' : DomainSort (proofEraseCtx Γ) ((proofErase Γ D).liftN 0) u := by
    simpa only [ProofShape.liftN_zero, ED] using SD
  have hDu := SD'.descend hΓ hΓ (Ctx.LiftN.zero []) hD
  have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hDu⟩
  have RL := RF.rename hrename (ContextRenaming.of_liftN hΓ hΓD Ctx.LiftN.one)
  simp only [subst_bvar_liftN, proofEraseCtx, ED] at RL
  obtain ⟨g, HE, Eg⟩ := proofErase_scoped_compute_realize hfun hΓ hf rfl rfl RF
  obtain ⟨A', b', rfl, _, EA, Eb⟩ := erase_lam_inv Eg
  have hgD := hfD.defeqU_l henv hΓ HE.toU
  obtain ⟨⟨_, hA⟩, _, hb⟩ := hgD.lam_inv henv hΓ
  obtain ⟨⟨_, HAD⟩, _⟩ := ((HasType.lam hA hb).uniqU henv hΓ hgD).forallE_inv henv hΓ
  have hAu := hDu.defeqU_l henv hΓ HAD.toU.symm
  have RB := proofErase_eta_lambda_beta hΓ hAu hb X
  rw [EA, Eb] at RB
  exact (ScopedCompute.lam .refl (.app RL .refl)).trans (.beta RB)

/-- Once the final short lambda's domain and the selected eta domain have
a common computation, the entire function/eta peak joins. The bodies require
no further transport premise: the previous residual made them identical. -/
theorem proofErase_native_eta_function_lambda_square
    (hrec : ErasedScopedPrimitiveDescent Recovery)
    (hfun : ErasedScopedPrimitiveDescent Source)
    (hrename : ∀ {Δ Δ' a b τ}, Source Δ a b → ContextRenaming Δ Δ' τ →
      Target Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f T)
    (RN : ScopedTypeRecovery Recovery (proofEraseCtx Γ) (proofErase Γ f) (.forallE X Y))
    (SD : DomainSort (proofEraseCtx Γ) X u)
    (RF : ScopedCompute Source (proofEraseCtx Γ) (proofErase Γ f) (.lam A b))
    (RA : ScopedCompute Target (proofEraseCtx Γ) A common)
    (RX : ScopedCompute Target (proofEraseCtx Γ) X common) :
    ScopedCompute Target (proofEraseCtx Γ) (.lam A b) (.lam common b) ∧
      ScopedCompute Target (proofEraseCtx Γ)
        (.lam X (.app ((proofErase Γ f).liftN 1) (etaArgument u))) (.lam common b) :=
  ⟨.lam RA .refl, (proofErase_native_eta_function_lambda_residual
    hrec hfun hrename hΓ hf RN SD RF).trans (.lam RX .refl)⟩

/-- Eta stages retain the function path's original bound on the long
residual. The native guard may have any unrelated finite depth. -/
theorem proofErase_eta_stage_function_lambda_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f T)
    (RN : ScopedTypeRecovery (ErasedEtaExpansionStage D k)
      (proofEraseCtx Γ) (proofErase Γ f) (.forallE X Y))
    (SD : DomainSort (proofEraseCtx Γ) X u)
    (RF : ScopedCompute (ErasedEtaExpansionStage D n)
      (proofEraseCtx Γ) (proofErase Γ f) (.lam A b)) :
    ScopedCompute (ErasedEtaExpansionStage D n) (proofEraseCtx Γ)
      (.lam X (.app ((proofErase Γ f).liftN 1) (etaArgument u))) (.lam X b) :=
  proofErase_native_eta_function_lambda_residual
    (erased_eta_expansion_stage_descent heq hs k)
    (erased_eta_expansion_stage_descent heq hs n)
    (erased_eta_expansion_stage_rename heq hs n) hΓ hf RN SD RF

/-- The full eta union allows independently unbounded finite guard and
function depths while retaining the computed body's exact erasure. -/
theorem proofErase_eta_union_function_lambda_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f T)
    (RN : ScopedTypeRecovery (ErasedEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ f) (.forallE X Y))
    (SD : DomainSort (proofEraseCtx Γ) X u)
    (RF : ScopedCompute (ErasedEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ f) (.lam A b)) :
    ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
      (.lam X (.app ((proofErase Γ f).liftN 1) (etaArgument u))) (.lam X b) := by
  apply proofErase_native_eta_function_lambda_residual
    (erased_eta_expansion_union_descent heq hs)
    (erased_eta_expansion_union_descent heq hs) (hΓ := hΓ) (hf := hf) (RN := RN) (SD := SD) (RF := RF)
  intro Δ Δ' a b τ H W
  obtain ⟨stage, H⟩ := H
  exact ⟨stage, erased_eta_expansion_stage_rename heq hs stage H W⟩

end Lean4Lean.VEnv.Strengthening
