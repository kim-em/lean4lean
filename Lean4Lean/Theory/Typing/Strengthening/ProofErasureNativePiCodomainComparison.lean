import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiCodomainComparison
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativePiDomainComparison

/-! # Recover native body-type comparisons under a shared written binder

The selected Pi domains may differ. Native lambda recovery retains both the
written-domain computations and native body recoveries in the original scope.
Rebuilding Pis at that written binder lets codomain extraction compare the exact
selected body types there, without transporting a check across selected binders.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Native Pi outputs of actual lambdas with a shared written binder yield
native body recoveries and an inferred check of their exact selected codomains
in that original binder context. The selected Pi domains and universes may
differ. No body-type comparison or native context alignment is assumed. -/
theorem stage_zero_native_lambda_codomains_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (.lam A a) F) (hg : env.HasType univs Γ (.lam A b) G)
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (.lam A a)) (.forallE X Y))
    (RG : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (.lam A b)) (.forallE Z W))
    (HT : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) mode
      (.forallE X Y) (.forallE Z W)) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) a) Y ∧
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) W ∧
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (A :: Γ)) false Y W := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D 0) :=
    erased_static_structure_eta_expansion_stage_descent heq hs 0
  have hnf : ¬ IsProof Γ (.lam A a) := fun H => RF.ne_proof (proofErase_eq_proof.2 H)
  have hng : ¬ IsProof Γ (.lam A b) := fun H => RG.ne_proof (proofErase_eq_proof.2 H)
  obtain ⟨⟨u, hA⟩, _, ha⟩ := hf.lam_inv henv hΓ
  obtain ⟨_, _, hb⟩ := hg.lam_inv henv hΓ
  rw [show proofErase Γ (.lam A a) = .lam _ _ from if_neg hnf] at RF
  rw [show proofErase Γ (.lam A b) = .lam _ _ from if_neg hng] at RG
  obtain ⟨RX, Ra⟩ := stage_zero_lambda_native_parts heq hs hΓ hA ha RF
  obtain ⟨RZ, Rb⟩ := stage_zero_lambda_native_parts heq hs hΓ hA hb RG
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  obtain ⟨P, haP, EP⟩ := proofErase_scoped_typeRecovery_replay hstep hΓA ha Ra
  obtain ⟨Q, hbQ, EQ⟩ := proofErase_scoped_typeRecovery_replay hstep hΓA hb Rb
  obtain ⟨v, hP⟩ := haP.isType henv hΓA
  obtain ⟨z, hQ⟩ := hbQ.isType henv hΓA
  refine ⟨Ra, Rb, ?_⟩
  have RP : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) P)) (.forallE X Y) := by
    rw [EP]
    exact .forallE RX .refl
  have RQ : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) Q)) (.forallE Z W) := by
    rw [EQ]
    exact .forallE RZ .refl
  simpa only [EP, EQ] using
    stage_zero_computed_pi_codomains_compare heq hs hΓ hA hP hQ RP RQ HT

end Lean4Lean.VEnv.Strengthening
