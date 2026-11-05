import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCutHistoryLocalSquare
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeBetaResidualBoundary

/-! # Historical cut certificates survive the exact-recovery boundary

The argument step that invalidates the marked outer cut's NativeHeadBeta
certificate nevertheless extends its component history. Thus the historical
square applies to an actual endpoint excluded by exact residual certification.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

/-- The previous argument-beta boundary has a genuine component history from
an exactly native original argument. Its current identity contraction is not
NativeHeadBeta, but the history's contraction and primitive/step squares apply.
This uses the same explicit positive empty-structure environment assumptions;
it is not a counterexample to strengthening or confluence. -/
theorem cut_history_beyond_exact_native_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u))) :
    ∃ Γ A x w v, OnCtx Γ (env.IsType univs) ∧ env.HasType univs Γ x A ∧
      w = .app (.lam A (.bvar 0)) x ∧ env.HasType univs Γ w A ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ w) (proofErase Γ A) ∧
      CutComponentHistory D Γ A (.bvar 0) w v A.lift
        (proofErase Γ A, proofErase (A :: Γ) (.bvar 0), proofErase Γ x) ∧
      ¬ NativeHeadBeta D Γ w x := by
  obtain ⟨Γ, A, x, w, hΓ, ht, rfl, hw, RN, _, _, Hno⟩ :=
    native_outer_cut_argument_beta_failure heq hs hi hp hx hz hS
  obtain ⟨v, hA⟩ := ht.isType henv hΓ
  have hnw : ¬ IsProof Γ (.app (.lam A (.bvar 0)) x) :=
    fun hp => RN.ne_proof (proofErase_eq_proof.2 hp)
  have hnx : ¬ IsProof Γ x := fun hp => hnw ((isProof_congr hΓ (nativeIdentityExpansion_equal ht)).2 hp)
  have RB := proofErase_identity_wrapper_beta hΓ ht hnx
  have Hinit := CutComponentHistory.refl (D := D) hA
    (show env.HasType univs (A :: Γ) (.bvar 0) A.lift from .bvar .zero) hw
  have HH : CutComponentHistory D Γ A (.bvar 0) (.app (.lam A (.bvar 0)) x) v A.lift
      (proofErase Γ A, proofErase (A :: Γ) (.bvar 0), proofErase Γ x) :=
    Hinit.advance heq hs hΓ ⟨.refl, .refl, .beta RB⟩
  exact ⟨Γ, A, x, _, v, hΓ, ht, rfl, hw, RN, HH, Hno⟩

end Lean4Lean.VEnv.Strengthening
