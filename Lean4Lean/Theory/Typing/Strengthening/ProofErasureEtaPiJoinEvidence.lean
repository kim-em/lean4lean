import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiJoinDomains
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaConversionEvidence

/-! # Whole Pi computation joins supply the eta consumer's domain evidence

The conversion certificate is given for whole types, not their domains. Its
computation children retain a common output under independent core reductions;
Pi readout extracts the domain evidence required by eta. Each completed consumer
comparison has a finite stage, without a uniform bound over future computations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- A join of whole Pi computation certificates constructs the complete eta
readout for a lambda assigned the first Pi and written with the second domain.
The domain certificate is extracted here, not added as a premise. -/
theorem eta_core_readout_lambda_of_pi_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hC : env.HasType univs Γ C (.sort u)) (hE : env.HasType univs (C :: Γ) E (.sort z))
    (hf : env.HasType univs Γ (.lam C b) (.forallE A B)) (hn : ¬ IsProof Γ (.lam C b))
    (HA : CoreFamilyCast D stage .compute (proofEraseCtx Γ) (proofErase Γ (.forallE A B)) out)
    (HC : CoreFamilyCast D stage .compute (proofEraseCtx Γ) (proofErase Γ (.forallE C E)) out) :
    EtaCoreReadout D (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) u
      (proofErase Γ A) (proofErase Γ (.lam C b)) := by
  apply eta_core_readout_lambda_of_domains hs hΓ hA hC hf hn
  intro X Y RX RY
  obtain ⟨shared, RL, RR⟩ := HA.pi_join_domain_residuals heq hs hl hcon hc hreg hoff hD
    hΓ hA hB hC hE HC RX RY
  exact .compute RL RR (.leaf .refl)

/-- The extracted Pi-join evidence survives the identity wrapper and yields
a finite-stage comparison for every typed eta consumer and independent pair of
full-core residuals. The output bound may depend on those residuals. -/
theorem pi_join_eta_identity_consumer_finite
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hC : env.HasType univs Γ C (.sort u)) (hE : env.HasType univs (C :: Γ) E (.sort z))
    (hf : env.HasType univs Γ (.lam C b) (.forallE A B)) (hn : ¬ IsProof Γ (.lam C b))
    (HA : CoreFamilyCast D stage .compute (proofEraseCtx Γ) (proofErase Γ (.forallE A B)) out)
    (HC : CoreFamilyCast D stage .compute (proofEraseCtx Γ) (proofErase Γ (.forallE C E)) out)
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (RL : Compute (ErasedLevelCore D)
      (proofErase Γ (t.inst (.lam A (.app
        (VExpr.app (.lam (.forallE A B) (.bvar 0)) (.lam C b)).lift (.bvar 0))))) left)
    (RR : Compute (ErasedLevelCore D)
      (proofErase Γ (t.inst (.app (.lam (.forallE A B) (.bvar 0)) (.lam C b)))) right) :
    ∃ later, stage ≤ later ∧
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D later) (proofEraseCtx Γ) mode left right := by
  have H := eta_core_readout_lambda_of_pi_join heq hs hl hcon hc hreg hoff hD
    hΓ hA hB hC hE hf hn HA HC
  have Hcmp : ComputedJointCompare (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) mode left right := H.identity_consumer hs hc
    (fun H => ⟨0, .inl H⟩)
    (fun ⟨n, H⟩ W => ⟨n, erased_static_structure_eta_expansion_stage_rename heq hs n H W⟩)
    hΓ hA hf ht RL RR
  obtain ⟨n, Hn⟩ := Hcmp.finite_stage
    (Stages := ErasedStaticStructureEtaExpansionStage D)
    (fun {stage later} hle {Δ a b} H => erased_static_structure_eta_expansion_stage_mono hle H)
  exact ⟨max stage n, by omega,
    Hn.mono (fun H => erased_static_structure_eta_expansion_stage_mono (by omega) H)⟩

end Lean4Lean.VEnv.Strengthening
