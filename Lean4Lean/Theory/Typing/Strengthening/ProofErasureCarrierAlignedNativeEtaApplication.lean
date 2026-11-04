import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedNativeUnion

/-! # Applying full aligned eta bodies to certified arguments

The fresh eta variable can be replaced by a native argument at any guarded
stage. These consumers return actual endpoint erasures, including proof-valued
instantiations, and do not assume universal native recovery.
-/
namespace Lean4Lean.VEnv.Strengthening.LevelNativeSubstitution
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- An existing eta-body certificate can be instantiated at a native argument,
using the additive stage bound n+k. The conclusion is an actual application. -/
theorem aligned_eta_apply
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hp : env.HasType univs Γ p A)
    (R : ScopedTypeRecovery (ErasedLevelRecoveredStage D k) (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ A))
    (ha : env.HasType univs (A :: Γ) a B) (hf : env.HasType univs Γ f (.forallE A B))
    (hnf : ¬ IsProof Γ f)
    (H : CarrierAlignedCompare (ErasedLevelRecoveredStage D n) (proofEraseCtx (A :: Γ)) true
      (proofErase (A :: Γ) a) (.app ((proofErase Γ f).liftN 1) (etaArgument u))) :
    CarrierAlignedCompare (ErasedLevelRecoveredStage D (n + k)) (proofEraseCtx Γ) true
      (proofErase Γ (a.inst p)) (proofErase Γ (.app f p)) := by
  have hη : env.HasType univs (A :: Γ) (.app f.lift (.bvar 0)) B := by
    simpa only [lift, VExpr.liftN, inst_liftN_bvar] using HasType.app (hf.weak henv (B := A)) (.bvar .zero)
  have Hη := proofErase_eta_body hΓ hA hf hnf
  have HH := aligned_inst heq hs hΓ hA hp R ha hη (by simpa only [Hη] using H)
  have E : (VExpr.app f.lift (.bvar 0)).inst p = .app f p := by
    change VExpr.app (f.lift.inst p) (VExpr.instVar 0 p) = _
    rw [inst_lift, instVar_zero]
  simpa only [E] using HH

/-- An existing eta-body certificate can be instantiated at a native argument,
using the closed union. The conclusion is an actual application. -/
theorem aligned_union_eta_apply
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hp : env.HasType univs Γ p A)
    (R : ScopedTypeRecovery (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ A))
    (ha : env.HasType univs (A :: Γ) a B) (hf : env.HasType univs Γ f (.forallE A B))
    (hnf : ¬ IsProof Γ f)
    (H : CarrierAlignedCompare (ErasedLevelRecoveredUnion D) (proofEraseCtx (A :: Γ)) true
      (proofErase (A :: Γ) a) (.app ((proofErase Γ f).liftN 1) (etaArgument u))) :
    CarrierAlignedCompare (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) true
      (proofErase Γ (a.inst p)) (proofErase Γ (.app f p)) := by
  have hη : env.HasType univs (A :: Γ) (.app f.lift (.bvar 0)) B := by
    simpa only [lift, VExpr.liftN, inst_liftN_bvar] using HasType.app (hf.weak henv (B := A)) (.bvar .zero)
  have Hη := proofErase_eta_body hΓ hA hf hnf
  have HH := aligned_union_inst heq hs hΓ hA hp R ha hη (by simpa only [Hη] using H)
  have E : (VExpr.app f.lift (.bvar 0)).inst p = .app f p := by
    change VExpr.app (f.lift.inst p) (VExpr.instVar 0 p) = _
    rw [inst_lift, instVar_zero]
  simpa only [E] using HH

/-- Exact universe selection supplies the native argument needed to apply
an eta body under a type binder. Both recovery and alignment are existing
certificates; their existence for arbitrary type arguments remains open. -/
theorem aligned_union_sort_eta_apply
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p (.sort u))
    (R : ScopedTypeRecovery (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ p) out)
    (HT : CarrierAlignedCompare (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) nativeMode out (.sort u))
    (ha : env.HasType univs (.sort u :: Γ) a B)
    (hf : env.HasType univs Γ f (.forallE (.sort u) B)) (hnf : ¬ IsProof Γ f)
    (H : CarrierAlignedCompare (ErasedLevelRecoveredUnion D) (proofEraseCtx (.sort u :: Γ)) true
      (proofErase (.sort u :: Γ) a) (.app ((proofErase Γ f).liftN 1) (etaArgument (.succ u)))) :
    CarrierAlignedCompare (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) true
      (proofErase Γ (a.inst p)) (proofErase Γ (.app f p)) := by
  have hU : env.HasType univs Γ (.sort u) (.sort (.succ u)) := .sort (hp.sort_r henv hΓ)
  have EU : proofErase Γ (.sort u) = .sort u := if_neg (not_isProof_of_sort hΓ hU)
  have HR := proofErase_carrier_aligned_level_union_recovered_sort_exact heq hs hΓ hp R HT
  exact aligned_union_eta_apply heq hs hΓ hU hp (by simpa only [EU] using HR) ha hf hnf H

end Lean4Lean.VEnv.Strengthening.LevelNativeSubstitution
