import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedEtaCertificateDescent
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedRawBetaJoin

/-! # Reading computations out of arbitrary unused binders

Certificate descent, rather than a particular primitive grammar, supplies the
exact lower body path. This includes native eta expansion and lets beta discard
the wrapper's final annotation and argument without native argument images.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Computation of a lifted typed payload under any well-formed unused binder
has an exact lifted output and a lower target-relation certificate. Every raw
argument and final lambda annotation beta-contracts to that same lower output. -/
theorem proofErase_unused_binder_readout
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Target)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (ht : env.HasType univs Γ e T)
    (RB : ScopedCompute Step (proofEraseCtx (A :: Γ)) ((proofErase Γ e).liftN 1) outB) :
    ∃ e', env.IsDefEq univs Γ e e' T ∧
      ScopedCompute Target (proofEraseCtx Γ) (proofErase Γ e) (proofErase Γ e') ∧
      outB = (proofErase Γ e').liftN 1 ∧
      ∀ X arg, ProofShape.BetaRed (.app (.lam X outB) arg) (proofErase Γ e') := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  obtain ⟨e', HE, RE, EE⟩ := proofErase_scoped_compute_certificate_descend
    hstep hΓ hΓA Ctx.LiftN.one ht rfl RB
  refine ⟨e', HE, RE, EE.symm, ?_⟩
  intro X arg
  rw [← EE]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
    ProofShape.lift_subst_cons, ProofShape.subst_id] using
    (ProofShape.BetaRed.beta (A := X) (b := (proofErase Γ e').liftN 1) (a := arg))

/-- Any beta continuation of the computed constant application meets the
lower retained computation. No exact substituted body certificate or recovery
of the supplied argument is needed. -/
theorem proofErase_unused_binder_beta_residual
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Target)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (ht : env.HasType univs Γ e T)
    (RB : ScopedCompute Step (proofEraseCtx (A :: Γ)) ((proofErase Γ e).liftN 1) outB)
    (Rβ : ProofShape.BetaRed (.app (.lam annotation outB) arg) out) :
    ∃ shared, ScopedCompute Target (proofEraseCtx Γ) (proofErase Γ e) shared ∧
      ProofShape.BetaRed out shared := by
  obtain ⟨e', _, RE, _, HB⟩ := proofErase_unused_binder_readout hstep hΓ hA ht RB
  obtain ⟨shared, RO, RE'⟩ := Rβ.raw_confluent (HB annotation arg)
  exact ⟨shared, RE.trans (.beta RE'), RO⟩

/-- In the eta-aware stages, arbitrary constant-wrapper body computation and
subsequent beta reduction retain a lower common reduct at the original stage. -/
theorem proofErase_eta_stage_unused_binder_beta_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (ht : env.HasType univs Γ e T)
    (RB : ScopedCompute (ErasedEtaExpansionStage D stage) (proofEraseCtx (A :: Γ))
      ((proofErase Γ e).liftN 1) outB)
    (Rβ : ProofShape.BetaRed (.app (.lam annotation outB) arg) out) :
    ∃ shared, ScopedCompute (ErasedEtaExpansionStage D stage) (proofEraseCtx Γ)
        (proofErase Γ e) shared ∧ ProofShape.BetaRed out shared :=
  proofErase_unused_binder_beta_residual (erased_eta_expansion_stage_certificate_descent heq hs stage)
    hΓ hA ht RB Rβ

/-- The union keeps the same constant-wrapper residual without imposing a
uniform bound on all eta guards in the body computation. -/
theorem proofErase_eta_union_unused_binder_beta_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (ht : env.HasType univs Γ e T)
    (RB : ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      ((proofErase Γ e).liftN 1) outB)
    (Rβ : ProofShape.BetaRed (.app (.lam annotation outB) arg) out) :
    ∃ shared, ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ e) shared ∧ ProofShape.BetaRed out shared :=
  proofErase_unused_binder_beta_residual (erased_eta_expansion_union_certificate_descent heq hs)
    hΓ hA ht RB Rβ

end Lean4Lean.VEnv.Strengthening
