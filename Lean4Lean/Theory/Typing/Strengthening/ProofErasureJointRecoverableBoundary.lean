import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecoverableLambda
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary

/-! # Exact recoverable substitution is not arbitrary typed substitution

The eta-converted neutral oracle example still fails the new invariant, even
with image recovery in the entire joint union. This is a premise boundary for
the additive transport theorem, not a failure of its conditional conclusion.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]
namespace EtaRecoveryJoinBoundary

/-- An actual typed substitution by a non-proof variable need not recover its
assigned oracle type, even in the full union. Allowing non-variable images
strictly extends retained renaming but does not remove converted-type alignment. -/
theorem variable_substitution_not_recovering (D : PureObservation.Definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ Γ' T, OnCtx Γ' (env.IsType univs) ∧ env.HasType univs Γ' (.bvar 0) T ∧
      OnCtx (T :: Γ') (env.IsType univs) ∧
      Ctx.SubstEq env univs Γ' (VExpr.Subst.one (.bvar 0)) (VExpr.Subst.one (.bvar 0)) (T :: Γ') ∧
      ¬ RecoveringSubstitution (ErasedJointUnion D) (proofEraseCtx (T :: Γ')) (proofEraseCtx Γ')
        (ProofShape.Subst.one (.bvar 0)) := by
  obtain ⟨Γ', e, T, out, rfl, hΓ', he, hn, _, _, Hno⟩ := typed_join_failure D hΓ
  obtain ⟨u, hT⟩ := he.isType henv hΓ'
  have hΓT : OnCtx (T :: Γ') (env.IsType univs) := ⟨hΓ', u, hT⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ') (e₀ := VExpr.bvar 0) (A₀ := T)).substEq hΓT he
  have hx : env.HasType univs (T :: Γ') (.bvar 0) T.lift := .bvar .zero
  have hvn : ¬ IsProof (T :: Γ') (.bvar 0) := fun hp => hn ((isProof_subst hΓ' W hx).2 hp)
  refine ⟨Γ', T, hΓ', he, hΓT, W, ?_⟩
  intro WR
  have HR := WR.lookup hΓT rfl Lookup.zero hvn
  have HR' : ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ')
      (.bvar 0) (proofErase Γ' T) := by
    simpa only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.Subst.one,
      ProofShape.lift_subst_cons, ProofShape.subst_id, ProofShape.Subst.cons] using HR
  rw [← show proofErase Γ' (.bvar 0) = .bvar 0 from if_neg hn] at HR'
  exact Hno _ _ HR' .refl .refl

end EtaRecoveryJoinBoundary
end Lean4Lean.VEnv.Strengthening
