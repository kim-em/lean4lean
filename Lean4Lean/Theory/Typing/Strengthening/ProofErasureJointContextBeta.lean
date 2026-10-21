import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointBetaSubstitution

/-! # Context transport from proposition beta stability

Exact computational substitution also transports typed raw paths between
converted contexts, in either direction. This concerns computation, not exact
type recovery or arbitrary joint comparison. It supplies the binder-context
transport needed to assemble component joins.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Under proposition beta stability, interpreted substitution preserves a raw
joint path whenever its source has a typed representative. No typing of the
raw output or recovery of the substituted images is required. -/
theorem proofErase_joint_compute_context_subst_of_prop_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaStability (ErasedJointUnion D))
    (HT : TypedSource Δ a) (W : ContextSubstitution Δ Δ' τ)
    (R : ScopedCompute (ErasedJointUnion D) Δ a b) :
    ScopedCompute (ErasedJointUnion D) Δ' (a.subst τ) (b.subst τ) := by
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ EΓ
  have R' : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ e) b := by
    rwa [EΓ, Ee]
  have H := proofErase_joint_compute_subst_of_prop_beta heq hs hregistry Hbeta hΓ₀ WS ES ht R'
  rwa [proofErase_subst_with hΓ₀ WS ht ES, EΓ₀, Ee] at H

/-- Computation with a typed raw source transports along arbitrary original
context conversion, with both raw endpoints unchanged. The hypothesis remains
proposition beta stability; this does not assert preservation of exact recovery. -/
theorem proofErase_joint_compute_defeqCtx_of_prop_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaStability (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs)) (H : IsDefEqCtx env univs Γ Γ₁ Γ₂)
    (HT : TypedSource (proofEraseCtx Γ₁) a)
    (R : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ₁) a b) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ₂) a b := by
  simpa only [ProofShape.subst_id] using
    proofErase_joint_compute_context_subst_of_prop_beta heq hs hregistry Hbeta HT
      (ContextSubstitution.of_defeqCtx hΓ H) R

end Lean4Lean.VEnv.Strengthening
