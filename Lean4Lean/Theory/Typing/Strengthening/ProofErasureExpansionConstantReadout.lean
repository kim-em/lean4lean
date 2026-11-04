import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionCertificateDescent
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedRawBetaJoin

/-! # Constant-body readout beneath any typed unused binder

Certificate descent removes any typed unused binder, not just the fixed sort
annotation introduced by constant expansion. No path back to an earlier binder
is needed: exact lower computation survives at the body's unchanged stage.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- An arbitrary well-formed unused binder can be removed from an expanded
body computation. Its raw output is exactly a lift of a lower computed term,
so every application argument and final annotation can be discarded by beta. -/
theorem proofErase_expansion_constant_body_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (ht : env.HasType univs Γ e T)
    (RB : ScopedCompute (ErasedExpansionStage D n) (proofEraseCtx (A :: Γ))
      ((proofErase Γ e).liftN 1) outB) :
    ∃ e', env.IsDefEq univs Γ e e' T ∧
      ScopedCompute (ErasedExpansionStage D n) (proofEraseCtx Γ)
        (proofErase Γ e) (proofErase Γ e') ∧
      outB = (proofErase Γ e').liftN 1 ∧
      ∀ X arg, ProofShape.BetaRed (.app (.lam X outB) arg) (proofErase Γ e') := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  obtain ⟨e', HE, RE, EE⟩ := proofErase_scoped_compute_certificate_descend
    (erased_expansion_stage_certificate_descent heq hs n) hΓ hΓA Ctx.LiftN.one ht rfl RB
  refine ⟨e', HE, RE, EE.symm, ?_⟩
  intro X arg
  rw [← EE]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
    ProofShape.lift_subst_cons, ProofShape.subst_id] using
    (ProofShape.BetaRed.beta (A := X) (b := (proofErase Γ e').liftN 1) (a := arg))

/-- Further beta computation after a constant application has a common beta
reduct with a lower computed term. The binder may be any well-formed type;
no comparison to the original wrapper annotation or argument recovery is used. -/
theorem proofErase_expansion_constant_body_beta_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (ht : env.HasType univs Γ e T)
    (RB : ScopedCompute (ErasedExpansionStage D n) (proofEraseCtx (A :: Γ))
      ((proofErase Γ e).liftN 1) outB)
    (Rβ : ProofShape.BetaRed (.app (.lam annotation outB) arg) out) :
    ∃ shared, ScopedCompute (ErasedExpansionStage D n) (proofEraseCtx Γ)
      (proofErase Γ e) shared ∧ ProofShape.BetaRed out shared := by
  obtain ⟨e', _, RE, _, HB⟩ := proofErase_expansion_constant_body_readout
    heq hs hΓ hA ht RB
  obtain ⟨shared, RO, RE'⟩ := Rβ.raw_confluent (HB annotation arg)
  exact ⟨shared, RE.trans (.beta RE'), RO⟩

/-- The same exact lifted body and lower certificate can be read from a path
whose expanded primitive stages are independently bounded. -/
theorem proofErase_expansion_union_constant_body_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (ht : env.HasType univs Γ e T)
    (RB : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx (A :: Γ))
      ((proofErase Γ e).liftN 1) outB) :
    ∃ e', env.IsDefEq univs Γ e e' T ∧
      ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ e) (proofErase Γ e') ∧
      outB = (proofErase Γ e').liftN 1 ∧
      ∀ X arg, ProofShape.BetaRed (.app (.lam X outB) arg) (proofErase Γ e') := by
  obtain ⟨n, RB⟩ := RB.finite_stage (Stages := ErasedExpansionStage D)
    (fun {stage later} hle {Δ a b} H => erased_expansion_stage_mono hle H)
  obtain ⟨e', HE, RE, EE, HB⟩ := proofErase_expansion_constant_body_readout
    heq hs hΓ hA ht RB
  exact ⟨e', HE, RE.mono (fun H => ⟨n, H⟩), EE, HB⟩

end Lean4Lean.VEnv.Strengthening
