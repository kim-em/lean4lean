import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedNativeImages
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelNativeUnion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedSortSelection

/-! # Full aligned instantiation at finite level-extended stages

All recursive aligned rules transport with the additive image-stage bound.
Sort selection supplies the required exact image from an existing native output
and its aligned comparison, without assuming arbitrary argument coverage.
-/
namespace Lean4Lean.VEnv.Strengthening.LevelNativeSubstitution
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions} {n k : Nat}

/-- The full aligned checker transports to stage n+k for images recovered at k.
Recursive native types keep their exact substituted erasures. -/
theorem aligned (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : CarrierAlignedCompare (ErasedLevelRecoveredStage D n) Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb)
    (W : ImageSubstitution D k Δ Δ' τ) :
    CarrierAlignedCompare (ErasedLevelRecoveredStage D (n + k)) Δ' mode (sa.subst τ) (sb.subst τ) :=
  NativeImageTransport.aligned_of_compute (erased_level_recovered_stage_rename heq hs k)
    (erased_level_recovered_stage_descent heq hs n)
    (fun H => erased_level_recovered_stage_mono (Nat.le_add_left k n) H)
    (fun R => compute heq hs R) H hΓ ha hb EΓ Ea Eb W

/-- Full aligned comparison transports the common native carrier and its guard. -/
theorem aligned_subst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (HI : Images D k Γ Γ₀ τ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : CarrierAlignedCompare (ErasedLevelRecoveredStage D n) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b)) :
    CarrierAlignedCompare (ErasedLevelRecoveredStage D (n + k)) (proofEraseCtx Γ₀) mode
      (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  have HH := aligned heq hs H W.wf ha hb rfl rfl rfl
    (NativeImageTransport.ImageSubstitution.of_typed hΓ₀ W ES HI)
  simpa only [proofErase_subst_with hΓ₀ W ha ES, proofErase_subst_with hΓ₀ W hb ES] using HH

/-- A native argument instantiates the full aligned checker. -/
theorem aligned_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hp : env.HasType univs Γ p A)
    (HR : ScopedTypeRecovery (ErasedLevelRecoveredStage D k) (proofEraseCtx Γ)
      (proofErase Γ p) (proofErase Γ A))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : CarrierAlignedCompare (ErasedLevelRecoveredStage D n) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    CarrierAlignedCompare (ErasedLevelRecoveredStage D (n + k)) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := A)).substEq hΓA hp
  have ES : ErasedSubstAgreement (A :: Γ) Γ (VExpr.Subst.one p)
      (ProofShape.Subst.one (proofErase Γ p)) := erasedSubstAgreement_one hΓA hp
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN] using
    aligned_subst heq hs hΓ W ES (NativeImageTransport.Images.inst HR) ha hb H

/-- A type argument with native output aligned to its assigned universe
instantiates full aligned bodies. Exact image recovery is derived locally,
with no stage increase beyond the existing n+k transport bound. -/
theorem aligned_sort_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p (.sort u))
    (R : ScopedTypeRecovery (ErasedLevelRecoveredStage D k) (proofEraseCtx Γ) (proofErase Γ p) out)
    (HT : CarrierAlignedCompare (ErasedLevelRecoveredStage D k) (proofEraseCtx Γ) nativeMode out (.sort u))
    (ha : env.HasType univs (.sort u :: Γ) a T) (hb : env.HasType univs (.sort u :: Γ) b T)
    (H : CarrierAlignedCompare (ErasedLevelRecoveredStage D n) (proofEraseCtx (.sort u :: Γ)) mode
      (proofErase (.sort u :: Γ) a) (proofErase (.sort u :: Γ) b)) :
    CarrierAlignedCompare (ErasedLevelRecoveredStage D (n + k)) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) := by
  have hU : env.HasType univs Γ (.sort u) (.sort (.succ u)) := .sort (hp.sort_r henv hΓ)
  have EU : proofErase Γ (.sort u) = .sort u := if_neg (not_isProof_of_sort hΓ hU)
  have HR := proofErase_carrier_aligned_level_stage_recovered_sort_exact heq hs hΓ hp R HT
  exact aligned_inst heq hs hΓ hU hp (by simpa only [EU] using HR) ha hb H

end Lean4Lean.VEnv.Strengthening.LevelNativeSubstitution
