import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedConvertedHeadBeta
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConvertedStructuralEtaAllStages

/-! # Paired beta at the structural eta recovery boundary

The concrete image recovers at its written type, while its assigned type uses
a different eta-equivalent neutral domain nested inside Pi. The new paired
head-beta theorem applies to every inferred computed-union lambda comparison
at that assigned annotation, including paths that change it further.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private context native assigned context_wf
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary
open private image_conversion
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureConvertedStructuralEtaInstantiation
open private native_recovery
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureConvertedStructuralEtaAllStages
variable [Params]

/-- The structural eta witness satisfies the converted image invariant, using
stage-zero recovery at its written type. Exact assigned recovery is not used. -/
theorem structural_eta_neutral_recovering_image
    (hΓ : OnCtx Γ (env.IsType univs)) :
    NeutralRecoveringImage D (context Γ)
      (.lam (.forallE native (.sort .zero)) (.sort .zero))
      (proofErase (context Γ) (.forallE (.forallE assigned (.sort .zero)) (.sort (.succ .zero)))) := by
  obtain ⟨_, _, HT, hp, _⟩ := image_conversion (D := D) hΓ
  exact .of_converted hp HT (fun _ => (native_recovery (D := D) hΓ).mono (fun H => ⟨0, H⟩))

/-- Every inferred comparison of proposition-valued lambdas at the boundary's
assigned annotation closes paired head beta at its concrete structural eta
image. Arbitrary computed-union paths inside the comparison are permitted. -/
theorem proofErase_computed_union_structural_eta_paired_head_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs (context Γ)
      (.lam (.forallE (.forallE assigned (.sort .zero)) (.sort (.succ .zero))) b)
      (.forallE (.forallE (.forallE assigned (.sort .zero)) (.sort (.succ .zero))) (.sort .zero)))
    (hg : env.HasType univs (context Γ)
      (.lam (.forallE (.forallE assigned (.sort .zero)) (.sort (.succ .zero))) c)
      (.forallE (.forallE (.forallE assigned (.sort .zero)) (.sort (.succ .zero))) (.sort .zero)))
    (H : ComputedJointCompare (ErasedComputedJointUnion D) (proofEraseCtx (context Γ)) false
      (proofErase (context Γ) (.lam (.forallE (.forallE assigned (.sort .zero)) (.sort (.succ .zero))) b))
      (proofErase (context Γ) (.lam (.forallE (.forallE assigned (.sort .zero)) (.sort (.succ .zero))) c))) :
    ComputedJointCompare (ErasedComputedJointUnion D) (proofEraseCtx (context Γ)) true
      (proofErase (context Γ) (b.inst (.lam (.forallE native (.sort .zero)) (.sort .zero))))
      (proofErase (context Γ) (c.inst (.lam (.forallE native (.sort .zero)) (.sort .zero)))) := by
  obtain ⟨_, HTU, _, hp, _⟩ := image_conversion (D := D) hΓ
  have hpT := HTU.symm.defeq hp
  have HI := structural_eta_neutral_recovering_image (D := D) hΓ
  exact proofErase_computed_union_proposition_head_beta_converted heq hs (context_wf hΓ)
    hpT hpT rfl hf hg HI HI H

end Lean4Lean.VEnv.Strengthening
