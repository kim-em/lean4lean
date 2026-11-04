import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedEtaCertificateDescent
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiReadout

/-! # Retained Pi readouts descend through inserted binder blocks

Both component computations descend in their original scopes. The beta
readout retracts syntactically once its components and source are known lifts;
no lower typing of its selected raw endpoint is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

/-- A readout at lifted endpoints retains both component histories below an
arbitrary binder insertion. The codomain history descends under the original
domain, even when its selected domain has changed. -/
theorem proofErase_pi_readout_certificate_descend
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Target)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (hA : env.HasType univs Γ A (.sort u))
    (hB : env.HasType univs (A :: Γ) B T)
    (H : PiReadout Step (proofEraseCtx Γ') ((proofErase Γ A).liftN n k)
      ((proofErase (A :: Γ) B).liftN n (k+1)) (out.liftN n k)) :
    PiReadout Target (proofEraseCtx Γ) (proofErase Γ A) (proofErase (A :: Γ) B) out := by
  obtain ⟨X, Y, RA, RB, Rβ⟩ := H
  obtain ⟨D, _, RD, ED⟩ := proofErase_scoped_compute_certificate_descend hstep hΓ hΓ' W hA rfl RA
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hΓA' : OnCtx (A.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', u, hA.weakN henv W⟩
  have EΓ : proofEraseCtx (A.liftN n k :: Γ') =
      (proofErase Γ A).liftN n k :: proofEraseCtx Γ' := by
    rw [proofEraseCtx, proofErase_liftN hΓ hΓ' W hA]
  obtain ⟨C, _, RC, EC⟩ := proofErase_scoped_compute_certificate_descend hstep hΓA hΓA'
    W.succ hB EΓ RB
  refine ⟨proofErase Γ D, proofErase (A :: Γ) C, RD, RC, ?_⟩
  have R : ProofShape.BetaRed (out.liftN n k)
      ((ProofShape.forallE (proofErase Γ D) (proofErase (A :: Γ) C)).liftN n k) := by
    simpa only [ProofShape.liftN, ED, EC] using Rβ
  have R' := R.subst (σ := ProofShape.Subst.retract (.consN (.skipN .refl n) k))
  simpa only [← ProofShape.lift'_consN_skipN, ProofShape.subst_retract_lift'] using R'

/-- Exact interpreted renaming lifts both component histories and their beta
readout. The codomain path uses the lifted original domain as its binder. -/
theorem proofErase_pi_readout_lift
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step' Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (hA : env.HasType univs Γ A (.sort u))
    (H : PiReadout Step (proofEraseCtx Γ) (proofErase Γ A) (proofErase (A :: Γ) B) out) :
    PiReadout Step' (proofEraseCtx Γ') ((proofErase Γ A).liftN n k)
      ((proofErase (A :: Γ) B).liftN n (k+1)) (out.liftN n k) := by
  obtain ⟨X, Y, RA, RB, Rβ⟩ := H
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hΓA' : OnCtx (A.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', u, hA.weakN henv W⟩
  have RA' := RA.rename hrename (ContextRenaming.of_liftN hΓ hΓ' W)
  have RB' := RB.rename hrename (ContextRenaming.of_liftN hΓA hΓA' W.succ)
  simp only [subst_bvar_liftN] at RA' RB'
  rw [proofEraseCtx, proofErase_liftN hΓ hΓ' W hA] at RB'
  exact ⟨X.liftN n k, Y.liftN n (k+1), RA', RB', Rβ.liftN⟩

/-- Pi readouts at typed component sources are invariant under unused binder
insertion at the same finite eta stage. This reflects certificates, not
arbitrary declarative equality. -/
theorem proofErase_eta_stage_pi_readout_lift_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (hA : env.HasType univs Γ A (.sort u))
    (hB : env.HasType univs (A :: Γ) B T) :
    PiReadout (ErasedEtaExpansionStage D stage) (proofEraseCtx Γ') ((proofErase Γ A).liftN n k)
      ((proofErase (A :: Γ) B).liftN n (k+1)) (out.liftN n k) ↔
    PiReadout (ErasedEtaExpansionStage D stage) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase (A :: Γ) B) out :=
  ⟨proofErase_pi_readout_certificate_descend (erased_eta_expansion_stage_certificate_descent heq hs stage)
      hΓ hΓ' W hA hB,
    proofErase_pi_readout_lift (erased_eta_expansion_stage_rename heq hs stage) hΓ hΓ' W hA⟩

/-- The entire eta union also retains exact readouts below inserted binders;
each original primitive keeps its own finite guard depth. -/
theorem proofErase_eta_union_pi_readout_lift_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (hA : env.HasType univs Γ A (.sort u))
    (hB : env.HasType univs (A :: Γ) B T) :
    PiReadout (ErasedEtaExpansionUnion D) (proofEraseCtx Γ') ((proofErase Γ A).liftN n k)
      ((proofErase (A :: Γ) B).liftN n (k+1)) (out.liftN n k) ↔
    PiReadout (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase (A :: Γ) B) out :=
  ⟨proofErase_pi_readout_certificate_descend (erased_eta_expansion_union_certificate_descent heq hs)
      hΓ hΓ' W hA hB,
    proofErase_pi_readout_lift (fun ⟨stage, R⟩ W => ⟨stage, erased_eta_expansion_stage_rename heq hs stage R W⟩)
      hΓ hΓ' W hA⟩

end Lean4Lean.VEnv.Strengthening
