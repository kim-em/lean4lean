import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeBetaLocalSquare
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeFreshTypeBoundary

/-! # Argument beta can erase the certificate of a marked outer cut

The initial argument is an exactly recoverable identity wrapper. Contracting
that argument exposes a value without native recovery at the outer written
domain. Thus the local square cannot be iterated by simply declaring every
residual marked cut to be NativeHeadBeta. The two branches still join here.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

/-- A certified outer identity cut can lose its certificate after one beta
step in its argument. Both initial one-step branches happen to have the same
endpoint, so this is a boundary of certificate propagation, not a failure of
local confluence or strengthening. It uses the established positive empty
structure boundary and remains conditional on that environment data. -/
theorem native_outer_cut_argument_beta_failure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u))) :
    ∃ Γ A x w, OnCtx Γ (env.IsType univs) ∧ env.HasType univs Γ x A ∧
      w = .app (.lam A (.bvar 0)) x ∧ env.HasType univs Γ w A ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ w) (proofErase Γ A) ∧
      NativeHeadBeta D Γ (.app (.lam A (.bvar 0)) w) w ∧
      ScopedStep (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app (.lam A (.bvar 0)) w)) (proofErase Γ w) ∧
      ¬ NativeHeadBeta D Γ w x := by
  obtain ⟨Γ, x, A, hΓ, ht, hn, Hno, _⟩ := descending_native_exact_coverage_failure
    (erased_static_structure_eta_expansion_union_descent heq hs) hi hp hx hz hS
  let w : VExpr := .app (.lam A (.bvar 0)) x
  have hw : env.HasType univs Γ w A := (nativeIdentityExpansion_equal ht).hasType.1
  have hnw : ¬ IsProof Γ w := fun H => hn ((isProof_congr hΓ (nativeIdentityExpansion_equal ht)).1 H)
  have RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ w) (proofErase Γ A) := proofErase_identity_wrapper_native hΓ ht hn
  refine ⟨Γ, A, x, w, hΓ, ht, rfl, hw, RN,
    NativeHeadBeta.identity hΓ hw (fun _ => RN), ?_, ?_⟩
  · have EW := proofErase_nativeIdentityExpansion hΓ ht hn
    have EO := proofErase_nativeIdentityExpansion hΓ hw hnw
    rw [EO, show proofErase Γ w = .app (.lam (proofErase Γ A) (.bvar 0)) (proofErase Γ x) from EW]
    apply ScopedStep.appR
    simpa only [ProofShape.inst, instVar, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self,
      ProofShape.liftN_zero] using
      (ScopedStep.beta (Step := ErasedStaticStructureEtaExpansionUnion D) (Δ := proofEraseCtx Γ)
        (A := proofErase Γ A) (b := .bvar 0) (x := proofErase Γ x))
  · intro H
    exact Hno (H.recovery heq hs hΓ hw RN)

end Lean4Lean.VEnv.Strengthening
