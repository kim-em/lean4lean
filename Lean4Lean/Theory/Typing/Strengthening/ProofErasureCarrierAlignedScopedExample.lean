import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedCorePairedSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedConvertedUnit

/-! # Full scoped body checking at nonjoining aligned images

The converted-unit images still fail the previous checker and have no
computation join. Every common-typed core scoped body comparison now
instantiates at them, including a body that eta-expands a function returning
the substituted parameter.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Under the positive fieldless-structure hypothesis, the nonjoining image
witness supports every core scoped body comparison, in either mode.
This includes all recursive eta and structure-field checks, not just bodies
with a shared reduct or recursively equivalent universe annotations. -/
theorem carrier_aligned_nonjoining_images_scoped_bodies
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs [] (.const family ls) (.sort (.succ u))) :
    ∃ Γ A x y, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ x A ∧ env.HasType univs Γ y A ∧
      (¬ ∃ out, ScopedCompute (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ x) out ∧
        ScopedCompute (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ y) out) ∧
      (¬ CarrierRecoveredCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) true
        (proofErase Γ x) (proofErase Γ y)) ∧
      (∀ {mode b c T}, env.HasType univs (A :: Γ) b T → env.HasType univs (A :: Γ) c T →
        ScopedCompare (ErasedJointStage D 0) (proofEraseCtx (A :: Γ)) mode
          (proofErase (A :: Γ) b) (proofErase (A :: Γ) c) →
        CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) mode
          (proofErase Γ (b.inst x)) (proofErase Γ (c.inst y))) := by
  obtain ⟨Γ, A, a, b, i, j, hΓ, _, _, hiT, hjT, _, _, _, Hno, Hnew⟩ :=
    carrier_aligned_converted_unit_beta_repair (D := D) hi hp hx hf hS
  obtain ⟨v, hA⟩ := hiT.isType henv hΓ
  refine ⟨Γ, A, .bvar i, .bvar j, hΓ, hiT, hjT, ?_, Hno, ?_⟩
  · rintro ⟨out, RX, RY⟩
    exact Hno (.base (.compute RX RY (.leaf .refl)))
  · intro mode b c T hb hc HC
    exact proofErase_carrier_aligned_core_paired_inst heq hs
      ⟨hΓ, v, hA⟩ hiT hjT hb hc (Hnew.mono (fun H => ⟨0, H⟩)) HC

/-- A concrete eta-expanded body returns the substituted parameter beneath a
lambda. Its two parameter images neither join computationally nor compare in
the old checker, but paired substitution produces the enlarged comparison. -/
theorem carrier_aligned_nonjoining_images_eta_body
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs [] (.const family ls) (.sort (.succ u))) :
    ∃ Γ A x y f T, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ x A ∧ env.HasType univs Γ y A ∧
      f = .lam (.sort .zero) (.bvar 1) ∧
      env.HasType univs (A :: Γ) f T ∧
      env.HasType univs (A :: Γ) (.lam (.sort .zero) (.app f.lift (.bvar 0))) T ∧
      (¬ ∃ out, ScopedCompute (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ x) out ∧
        ScopedCompute (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ y) out) ∧
      (¬ CarrierRecoveredCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) true
        (proofErase Γ x) (proofErase Γ y)) ∧
      CarrierAlignedCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) true
        (proofErase Γ ((VExpr.lam (.sort .zero) (.app f.lift (.bvar 0))).inst x))
        (proofErase Γ (f.inst y)) := by
  obtain ⟨Γ, A, x, y, hΓ, hx, hy, Hjoin, Hno, Hbody⟩ :=
    carrier_aligned_nonjoining_images_scoped_bodies heq hs hi hp hx hf hS
  obtain ⟨v, hA⟩ := hx.isType henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, v, hA⟩
  let f : VExpr := .lam (.sort .zero) (.bvar 1)
  have hf : env.HasType univs (A :: Γ) f (.forallE (.sort .zero) A.lift.lift) :=
    .lam (.sort (by trivial)) (.bvar (.succ .zero))
  have hη := (IsDefEq.eta hf).hasType.1
  have HC : ScopedCompare (ErasedJointStage D 0) (proofEraseCtx (A :: Γ)) true
      (proofErase (A :: Γ) (.lam (.sort .zero) (.app f.lift (.bvar 0)))) (proofErase (A :: Γ) f) := by
    rcases proofErase_eta_forward hΓA hf with E | HE
    · rw [E]; exact .leaf .refl
    · exact .leaf (.etaL HE)
  exact ⟨Γ, A, x, y, f, _, hΓ, hx, hy, rfl, hf, hη, Hjoin, Hno, Hbody hη hf HC⟩

end Lean4Lean.VEnv.Strengthening
