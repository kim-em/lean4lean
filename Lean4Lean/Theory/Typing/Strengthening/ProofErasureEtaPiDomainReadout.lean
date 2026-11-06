import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiCoreDomainReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaConversionEvidence

/-! # Core-exposed Pi domain readout supplies eta conversion evidence

The readout invariant is consumed at actual residual Pis. Its domain checks
construct the complete eta certificate, then pass through the identity consumer.
Only this local invariant is used; global comparison coverage remains open.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Domain-only residuals of two typed Pis are valid observations for the
whole-type readout invariant. Both codomains keep their raw bodies while their
actual binder typings transport along the domain paths. -/
theorem PiCoreDomainReadout.domains
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hC : env.HasType univs Γ C (.sort w)) (hE : env.HasType univs (C :: Γ) E (.sort z))
    (H : PiCoreDomainReadout D (proofEraseCtx Γ)
      (proofErase Γ (.forallE A B)) (proofErase Γ (.forallE C E)))
    (RA : Compute (ErasedLevelCore D) (proofErase Γ A) X)
    (RC : Compute (ErasedLevelCore D) (proofErase Γ C) Y) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) true X Y := by
  obtain ⟨A', hA', hB', EA, RPiA⟩ := proofErase_core_pi_domain_residual hs hΓ hA hB RA
  obtain ⟨C', hC', hE', EC, RPiC⟩ := proofErase_core_pi_domain_residual hs hΓ hC hE RC
  rw [show proofErase Γ (.forallE A' B) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ (HasType.forallE hA' hB'))] at RPiA
  rw [show proofErase Γ (.forallE C' E) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ (HasType.forallE hC' hE'))] at RPiC
  simpa only [EA, EC] using H hΓ hA' hB' hC' hE' rfl RPiA RPiC

/-- Whole-type readout constructs a converted lambda's domain and eta-origin
checks after arbitrary core reductions. No separate domain certificate is an
input, and neither the written body nor its reductions must normalize. -/
theorem PiCoreDomainReadout.eta_lambda
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hC : env.HasType univs Γ C (.sort u)) (hE : env.HasType univs (C :: Γ) E (.sort z))
    (hf : env.HasType univs Γ (.lam C b) (.forallE A B)) (hn : ¬ IsProof Γ (.lam C b))
    (H : PiCoreDomainReadout D (proofEraseCtx Γ)
      (proofErase Γ (.forallE A B)) (proofErase Γ (.forallE C E))) :
    EtaCoreReadout D (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) u
      (proofErase Γ A) (proofErase Γ (.lam C b)) :=
  eta_core_readout_lambda_of_domains hs hΓ hA hC hf hn
    (fun RA RC => H.domains hs hΓ hA hB hC hE RA RC)

/-- Each identity-wrapped eta consumer has a finite-stage comparison once its
assigned and written Pis satisfy core-exposed domain readout. This applies to
the annotation, join, frame and recursive-prefix constructions of that invariant.
No single stage uniform over all consumers or residuals is asserted. -/
theorem PiCoreDomainReadout.eta_identity_consumer_finite
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hC : env.HasType univs Γ C (.sort u)) (hE : env.HasType univs (C :: Γ) E (.sort z))
    (hf : env.HasType univs Γ (.lam C b) (.forallE A B)) (hn : ¬ IsProof Γ (.lam C b))
    (H : PiCoreDomainReadout D (proofEraseCtx Γ)
      (proofErase Γ (.forallE A B)) (proofErase Γ (.forallE C E)))
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (RL : Compute (ErasedLevelCore D)
      (proofErase Γ (t.inst (.lam A (.app
        (VExpr.app (.lam (.forallE A B) (.bvar 0)) (.lam C b)).lift (.bvar 0))))) left)
    (RR : Compute (ErasedLevelCore D)
      (proofErase Γ (t.inst (.app (.lam (.forallE A B) (.bvar 0)) (.lam C b)))) right) :
    ∃ stage, ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D stage)
      (proofEraseCtx Γ) mode left right := by
  have HE := H.eta_lambda hs hΓ hA hB hC hE hf hn
  have Hcmp : ComputedJointCompare (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) mode left right := HE.identity_consumer hs hc
    (fun H => ⟨0, .inl H⟩)
    (fun ⟨n, H⟩ W => ⟨n, erased_static_structure_eta_expansion_stage_rename heq hs n H W⟩)
    hΓ hA hf ht RL RR
  exact Hcmp.finite_stage (Stages := ErasedStaticStructureEtaExpansionStage D)
    (fun {stage later} hle {Δ a b} H => erased_static_structure_eta_expansion_stage_mono hle H)

end Lean4Lean.VEnv.Strengthening
