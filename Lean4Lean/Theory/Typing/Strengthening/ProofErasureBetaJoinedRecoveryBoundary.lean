import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedJoinedNativeBoundary

/-! # A beta step can lose even joined native recovery

An explicit identity wrapper stores its assigned type in its lambda annotation.
After beta removes the wrapper, the underlying value need not recover any type
beta/universe-joined to that annotation. The eta-assigned neutral example gives
this failure even with pure source, context and assigned-type erasures.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- An explicit identity wrapper natively recovers its exact displayed
assigned type, even when its argument has no native evidence at that type.
The recovery uses only the fresh variable and lambda/application recipes. -/
theorem proofErase_identity_wrapper_native
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p A)
    (hn : ¬ IsProof Γ p) :
    ScopedTypeRecovery Step (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam A (.bvar 0)) p)) (proofErase Γ A) := by
  rw [proofErase_nativeIdentityExpansion hΓ hp hn]
  have R : ScopedTypeRecovery Step (proofEraseCtx Γ)
      (.app (.lam (proofErase Γ A) (.bvar 0)) (proofErase Γ p))
      (((proofErase Γ A).liftN 1).inst (proofErase Γ p)) :=
    .app (.lam (.bvar (i := 0)))
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
    ProofShape.lift_subst_cons, ProofShape.subst_id] using R

/-- The same wrapper has a raw beta step to its retained argument. -/
theorem proofErase_identity_wrapper_beta
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p A)
    (hn : ¬ IsProof Γ p) :
    ProofShape.BetaRed (proofErase Γ (.app (.lam A (.bvar 0)) p)) (proofErase Γ p) := by
  rw [proofErase_nativeIdentityExpansion hΓ hp hn]
  simpa only [ProofShape.inst, instVar, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self,
    ProofShape.liftN_zero] using
    (ProofShape.BetaRed.beta (A := proofErase Γ A) (b := .bvar 0) (a := proofErase Γ p))

/-- Exact native recovery before one typed beta step does not imply even
beta/universe-joined native recovery afterward, in the entire controlled-beta
expansion union. The target and its assigned type are pure, as is the context.
This refutes native source-reduction stability with that smaller join notion;
it makes no negative claim about the eta-expanded union. -/
theorem identity_beta_loses_joined_native_recovery (D : PureObservation.Definitions) :
    ∃ Γ p A, OnCtx Γ (env.IsType univs) ∧ env.HasType univs Γ p A ∧ ¬ IsProof Γ p ∧
      PureContext (proofEraseCtx Γ) ∧ PureLambda (proofErase Γ p) ∧ PureLambda (proofErase Γ A) ∧
      env.IsDefEq univs Γ (.app (.lam A (.bvar 0)) p) p A ∧
      ProofShape.BetaRed (proofErase Γ (.app (.lam A (.bvar 0)) p)) (proofErase Γ p) ∧
      ScopedTypeRecovery (ErasedExpansionStage D 0) (proofEraseCtx Γ)
        (proofErase Γ (.app (.lam A (.bvar 0)) p)) (proofErase Γ A) ∧
      ∀ out, ScopedTypeRecovery (ErasedExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ p) out →
        ¬ BetaLevelJoin out (proofErase Γ A) := by
  obtain ⟨Γ, p, A, hΓ, hp, hn, HΓ, HP, HA, _, Hno⟩ :=
    EtaRecoveryJoinBoundary.expansion_joined_native_failure_empty D
  exact ⟨Γ, p, A, hΓ, hp, hn, HΓ, HP, HA, nativeIdentityExpansion_equal hp,
    proofErase_identity_wrapper_beta hΓ hp hn, proofErase_identity_wrapper_native hΓ hp hn, Hno⟩

end Lean4Lean.VEnv.Strengthening
