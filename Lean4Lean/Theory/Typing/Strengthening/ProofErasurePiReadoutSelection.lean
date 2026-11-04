import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedPiExposure

/-! # Native Pi selection retaining the dependent codomain path

The selected Pi is reified at the original function. Uniqueness aligns its
binder with the assigned binder, and erasure invariance moves its codomain
back to the original scope. Both component computation paths are retained.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Native selection from a Pi readout supplies actual Pi representatives and
both component paths. The codomain path ends at C erased under the original A
binder, so subsequent instantiation can use the original argument typing. -/
theorem proofErase_native_pi_readout
    (hstep : ErasedScopedPrimitiveDescent Recovery)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f (.forallE A B))
    (R : ScopedTypeRecovery Recovery (proofEraseCtx Γ) (proofErase Γ f) out)
    (H : PiReadout Step (proofEraseCtx Γ) (proofErase Γ A) (proofErase (A :: Γ) B) out) :
    ∃ D C, env.HasType univs Γ f (.forallE D C) ∧
      ScopedTypeRecovery Recovery (proofEraseCtx Γ) (proofErase Γ f)
        (.forallE (proofErase Γ D) (proofErase (D :: Γ) C)) ∧
      env.IsDefEqU univs Γ A D ∧ env.IsDefEqU univs (A :: Γ) B C ∧
      ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ D) ∧
      ScopedCompute Step (proofEraseCtx (A :: Γ))
        (proofErase (A :: Γ) B) (proofErase (A :: Γ) C) := by
  obtain ⟨X, Y, RA, RB, RBeta⟩ := H
  have RN := R.convert (.beta RBeta)
  obtain ⟨D, C, hfDC, ED, EC⟩ := proofErase_scoped_recovered_pi_descend hstep hΓ hΓ
    (show Ctx.LiftN 0 0 Γ Γ from .zero []) hf
    (by simpa only [ProofShape.liftN_zero] using RN)
  simp only [ProofShape.liftN_zero] at ED EC
  simp only [← ED, ← EC] at RN RA RB
  obtain ⟨⟨u, HAD⟩, v, HBC⟩ := (hf.uniqU henv hΓ hfDC).forallE_inv henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAD.hasType.1⟩
  have EC' := proofErase_defeqCtx hΓA (IsDefEqCtx.succ .zero HAD) HBC.hasType.2
  rw [← EC'] at RB
  exact ⟨D, C, hfDC, RN, ⟨_, HAD⟩, ⟨_, HBC⟩, RA, RB⟩

/-- The selected native Pi retains inferred comparisons of both components,
with the dependent codomain comparison explicitly in the original binder. -/
theorem proofErase_native_pi_readout_comparisons
    (hstep : ErasedScopedPrimitiveDescent Recovery)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f (.forallE A B))
    (R : ScopedTypeRecovery Recovery (proofEraseCtx Γ) (proofErase Γ f) out)
    (H : PiReadout Step (proofEraseCtx Γ) (proofErase Γ A) (proofErase (A :: Γ) B) out) :
    ∃ D C, env.HasType univs Γ f (.forallE D C) ∧
      ScopedTypeRecovery Recovery (proofEraseCtx Γ) (proofErase Γ f)
        (.forallE (proofErase Γ D) (proofErase (D :: Γ) C)) ∧
      ComputedJointCompare Step (proofEraseCtx Γ) false (proofErase Γ A) (proofErase Γ D) ∧
      ComputedJointCompare Step (proofEraseCtx (A :: Γ)) false
        (proofErase (A :: Γ) B) (proofErase (A :: Γ) C) := by
  obtain ⟨D, C, hfDC, RN, _, _, RA, RB⟩ := proofErase_native_pi_readout hstep hΓ hf R H
  exact ⟨D, C, hfDC, RN, .compute RA .refl (.leaf .refl), .compute RB .refl (.leaf .refl)⟩

/-- A reselected native function applies to an argument at its original domain.
Actual uniqueness converts that argument to the selected domain; the resulting
native certificate has the exact actual selected codomain instantiation. -/
theorem proofErase_native_application_selected_pi
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hfDC : env.HasType univs Γ f (.forallE D C))
    (hx : env.HasType univs Γ x A) (hn : ¬ IsProof Γ (.app f x))
    (R : ScopedTypeRecovery Recovery (proofEraseCtx Γ) (proofErase Γ f)
      (.forallE (proofErase Γ D) (proofErase (D :: Γ) C))) :
    env.HasType univs Γ (.app f x) (C.inst x) ∧
      ScopedTypeRecovery Recovery (proofEraseCtx Γ) (proofErase Γ (.app f x))
        (proofErase Γ (C.inst x)) := by
  obtain ⟨⟨u, HAD⟩, _, _⟩ := (hf.uniqU henv hΓ hfDC).forallE_inv henv hΓ
  have hxD := HAD.defeq hx
  have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, HAD.hasType.2⟩
  obtain ⟨_, hPi⟩ := hfDC.isType henv hΓ
  obtain ⟨_, _, hC⟩ := hPi.forallE_inv henv
  refine ⟨hfDC.app hxD, ?_⟩
  rw [show proofErase Γ (.app f x) = .app (proofErase Γ f) (proofErase Γ x) from if_neg hn,
    proofErase_instN hΓD hxD Ctx.InstN.zero hC]
  exact ScopedTypeRecovery.app R

end Lean4Lean.VEnv.Strengthening
