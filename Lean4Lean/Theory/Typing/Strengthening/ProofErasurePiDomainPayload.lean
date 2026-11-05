import Lean4Lean.Theory.Typing.Strengthening.ProofErasureMarkedPiTrace
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedTypedExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointCertificateDescent

/-! # Domain comparisons retained by marked Pi payloads

Each original Pi retains its own domain and universe. Sort-typed mode conversion
and certificate descent recover an inferred comparison of the computed domains;
prefixing their histories then compares the original domains.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- A comparison of lifted payload domains descends and prefixes the two
original domain histories, regardless of the comparison mode or universes. -/
theorem stage_zero_pi_payload_domain_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n 0 Γ Γ')
    (PA : StageZeroPiOrigin D Γ A B u v X x)
    (PB : StageZeroPiOrigin D Γ C E w z Y y)
    (H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ') mode
      (X.liftN n) (Y.liftN n)) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) false
      (proofErase Γ A) (proofErase Γ C) := by
  obtain ⟨A', _, HA, _, EA, _, RA, _⟩ := PA
  obtain ⟨C', _, HC, _, EC, _, RC, _⟩ := PB
  have hA := HA.hasType.2
  have hC := HC.hasType.2
  have EA' := proofErase_liftN hΓ hΓ' W hA
  have EC' := proofErase_liftN hΓ hΓ' W hC
  rw [EA] at EA'
  rw [EC] at EC'
  have hstep : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D 0) :=
    erased_static_structure_eta_expansion_stage_descent heq hs 0
  have HI := proofErase_computed_joint_types_inferred hstep hΓ' (hA.weakN henv W) (hC.weakN henv W)
    (by simpa only [EA', EC'] using H)
  have HL := (proofErase_computed_joint_compare_certificate_descend
    (erased_static_structure_eta_expansion_stage_certificate_descent heq hs 0)
    hΓ hΓ' W rfl hA hC (by simpa only [EA', EC', EA, EC] using HI)).2
    rfl (not_isProof_of_sort hΓ hA) (not_isProof_of_sort hΓ hC)
  exact .compute RA RC (by simpa only [EA, EC] using HL)

/-- Identical selected payloads already give a common computation of the two
original domains. No agreement of their assigned universes is required. -/
theorem stage_zero_pi_common_payload_domains
    (PA : StageZeroPiOrigin D Γ A B u v X x)
    (PB : StageZeroPiOrigin D Γ C E w z X x) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) false
      (proofErase Γ A) (proofErase Γ C) := by
  obtain ⟨_, _, _, _, _, _, RA, _⟩ := PA
  obtain ⟨_, _, _, _, _, _, RC, _⟩ := PB
  exact .compute RA RC (.leaf .refl)

end Lean4Lean.VEnv.Strengthening
