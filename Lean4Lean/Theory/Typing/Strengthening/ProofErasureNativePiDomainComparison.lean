import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiDomainComparison
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStageZeroLambdaRecovery

/-! # Recover written lambda-domain checks from compared native Pi outputs

Native lambda recovery retains forward computation from the written domain to
its selected domain. Comparison of the two selected Pi outputs supplies the
selected-domain check; prefixing the retained histories checks the original
written annotations. Actual type equality alone is not used as a substitute.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : PureObservation.Definitions}

/-- Compared native Pi outputs of two actual lambdas imply an inferred check
of their written domains. Native conversion tails may contain arbitrary
stage-zero control expansions and beta interleavings. No comparison of the
written domains, agreement of assigned types or native-image premise is assumed. -/
theorem stage_zero_native_lambda_domains_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (.lam A a) F) (hg : env.HasType univs Γ (.lam C b) G)
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (.lam A a)) (.forallE X Y))
    (RG : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (.lam C b)) (.forallE Z W))
    (HT : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) mode
      (.forallE X Y) (.forallE Z W)) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) false
      (proofErase Γ A) (proofErase Γ C) := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D 0) :=
    erased_static_structure_eta_expansion_stage_descent heq hs 0
  obtain ⟨P, hfP, EP⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ hf RF
  obtain ⟨Q, hgQ, EQ⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ hg RG
  obtain ⟨D₁, E₁, rfl, _, ED₁, EE₁⟩ := erase_forallE_inv EP
  obtain ⟨D₂, E₂, rfl, _, ED₂, EE₂⟩ := erase_forallE_inv EQ
  obtain ⟨⟨u, hD₁⟩, v, hE₁⟩ := (hfP.isType henv hΓ).forallE_inv henv
  obtain ⟨⟨w, hD₂⟩, z, hE₂⟩ := (hgQ.isType henv hΓ).forallE_inv henv
  have HD := stage_zero_pi_domains_compare heq hs hΓ hD₁ hE₁ hD₂ hE₂
    (by simpa only [EP, EQ] using HT)
  rw [ED₁, ED₂] at HD
  have hnf : ¬ IsProof Γ (.lam A a) := fun H => RF.ne_proof (proofErase_eq_proof.2 H)
  have hng : ¬ IsProof Γ (.lam C b) := fun H => RG.ne_proof (proofErase_eq_proof.2 H)
  obtain ⟨⟨_, hA⟩, _, ha⟩ := hf.lam_inv henv hΓ
  obtain ⟨⟨_, hC⟩, _, hb⟩ := hg.lam_inv henv hΓ
  have RF' := RF
  have RG' := RG
  rw [show proofErase Γ (.lam A a) = .lam _ _ from if_neg hnf] at RF'
  rw [show proofErase Γ (.lam C b) = .lam _ _ from if_neg hng] at RG'
  exact .compute (stage_zero_lambda_native_parts heq hs hΓ hA ha RF').1
    (stage_zero_lambda_native_parts heq hs hΓ hC hb RG').1 HD

/-- Displayed eta between actual lambda endpoints becomes an inferred check
when their natively recovered Pi outputs compare. The needed written-domain
check is derived, rather than assumed or replaced by ordinary type equality. -/
theorem stage_zero_native_eta_lambdas_inferred
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (.lam A a) F) (hg : env.HasType univs Γ (.lam C b) G)
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (.lam A a)) (.forallE X Y))
    (RG : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (.lam C b)) (.forallE Z W))
    (HT : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) mode
      (.forallE X Y) (.forallE Z W))
    (HE : EtaHead (proofErase Γ (.lam A a)) (proofErase Γ (.lam C b)) ∨
      EtaHead (proofErase Γ (.lam C b)) (proofErase Γ (.lam A a))) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A a)) (proofErase Γ (.lam C b)) := by
  have HD := stage_zero_native_lambda_domains_compare heq hs hΓ hf hg RF RG HT
  have hnf : ¬ IsProof Γ (.lam A a) := fun H => RF.ne_proof (proofErase_eq_proof.2 H)
  have hng : ¬ IsProof Γ (.lam C b) := fun H => RG.ne_proof (proofErase_eq_proof.2 H)
  rw [show proofErase Γ (.lam A a) = .lam _ _ from if_neg hnf,
    show proofErase Γ (.lam C b) = .lam _ _ from if_neg hng] at HE ⊢
  exact .etaLams HD HE

end Lean4Lean.VEnv.Strengthening
