import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStageZeroPiReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureBetaRecovery

/-! # Exact lambda recovery readout at stage zero

Pi component readout retains the native body's selected codomain without
increasing the stage. The written lambda domain also computes to the exact
selected domain, which makes this branch usable by computed application
checking. Arbitrary function images and compared lambda bodies remain separate.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Native recovery of a literal lambda at a Pi retains both the forward
history of its written domain and native recovery of its body at the exact
selected codomain. The codomain recovery stays under the written domain;
constant expansion and beta in the native conversion tail are allowed. -/
theorem stage_zero_lambda_native_parts
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) (.forallE X Y)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) (proofErase Γ A) X ∧
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) Y := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  obtain ⟨C, RB, RP⟩ := RN.lam_compute
  have RB' : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b) C := by
    simpa only [proofEraseCtx] using RB
  obtain ⟨C', hbC, EC⟩ := proofErase_scoped_typeRecovery_replay
    (erased_static_structure_eta_expansion_stage_descent heq hs 0) hΓA hb RB'
  obtain ⟨v, hC⟩ := hbC.isType henv hΓA
  rw [← EC] at RP
  obtain ⟨_, _, _, _, _, _, RA, RC⟩ := proofErase_stage_zero_pi_components heq hs hΓ hA hC RP
  rw [EC] at RC
  exact ⟨RA, RB'.convert RC⟩

/-- The exact domain selected natively for a literal lambda is exposed by a
stage-zero computation of that lambda. Its body need not be changed, and no
application argument image or comparison transport premise is needed. -/
theorem stage_zero_lambda_selected_domain
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) (.forallE X Y)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) (.lam X (proofErase (A :: Γ) b)) :=
  .lam (stage_zero_lambda_native_parts heq hs hΓ hA hb RN).1 .refl

/-- Native recovery at a beta redex factors through the original body at the
same stage zero, followed by the final instantiated type conversion. This
factorization assumes only ordinary typing of the argument. Preserving the
body recovery after substituting that argument is still a separate question. -/
theorem stage_zero_root_beta_native_factor
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam A b) x)) out) :
    ∃ selected, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0)
        (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b) selected ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
        (selected.inst (proofErase Γ x)) out := by
  have hn : ¬ IsProof Γ (.app (.lam A b) x) := fun H => RN.ne_proof (proofErase_eq_proof.2 H)
  have hnf := not_isProof_fn hΓ (HasType.lam hA hb) hx hn
  rw [show proofErase Γ (.app (.lam A b) x) = .app _ _ from if_neg hn,
    show proofErase Γ (.lam A b) = .lam _ _ from if_neg hnf] at RN
  obtain ⟨X, Y, RF, RC⟩ := RN.app_origin
  exact ⟨Y, (stage_zero_lambda_native_parts heq hs hΓ hA hb RF).2, RC⟩

end Lean4Lean.VEnv.Strengthening
