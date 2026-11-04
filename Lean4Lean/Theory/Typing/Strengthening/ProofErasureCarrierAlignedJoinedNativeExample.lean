import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedJoinedNativeApplication
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedExpandedNativeJoin

/-! # Joined images strictly relax exact native image recovery

The earlier higher-order input cannot recover its exact beta-expanded assigned
type in the old level union. Its beta-only native output nevertheless supplies
a joined image, sufficient for the new pure-source native substitution theorem.
-/
namespace Lean4Lean.VEnv.Strengthening.TypeFunctionExample
open _root_.Lean4Lean Params ProofShape
open private erasures
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedExpandedNativeJoin
variable [Params]

/-- The actual higher-order image has beta-only native evidence joined to its
assigned type, although the old complete level union cannot recover that type. -/
theorem joined_image_without_exact_recovery (hΓ : OnCtx Γ (env.IsType univs)) :
    (¬ ScopedTypeRecovery (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ)
      (proofErase Γ image) (proofErase Γ assigned)) ∧
    JoinedNativeImages (proofEraseCtx (assigned :: Γ)) (proofEraseCtx Γ)
      (Subst.one (proofErase Γ image)) := by
  obtain ⟨EI, EA⟩ := erasures hΓ
  have RN : ScopedTypeRecovery (fun _ _ _ => False) (proofEraseCtx Γ) (proofErase Γ image)
      (.forallE (.forallE (.sort (.succ .zero)) (.sort .zero)) (.sort .zero)) := by
    rw [EI]
    exact .lam (ScopedTypeRecovery.app (A := .sort (.succ .zero)) (B := .sort .zero) (.bvar (i := 0)))
  have HJ : BetaLevelJoin
      (.forallE (.forallE (.sort (.succ .zero)) (.sort .zero)) (.sort .zero))
      (proofErase Γ assigned) := by
    rw [EA]
    refine ⟨_, .forallE (.forallE (.sort inputLevel) (.sort resultLevel)) (.sort .zero),
      .refl, .forallE .beta .refl, ?_⟩
    exact .forallE (.forallE (.sort VLevel.imax_self.symm) (.sort VLevel.max_self.symm)) .refl
  exact ⟨level_assigned_recovery_failure D hΓ, JoinedNativeImages.inst RN HJ⟩

/-- The previously rejected exact image instantiates every pure expanded
native certificate in a pure context, retaining a joined dependent output.
The resulting evidence uses beta only, regardless of the source guard depth. -/
theorem joined_image_native_inst (hΓ : OnCtx Γ (env.IsType univs))
    (HΔ : PureContext (proofEraseCtx Γ)) (HE : PureLambda e)
    (R : ScopedTypeRecovery (ErasedExpansionUnion D) (proofEraseCtx (assigned :: Γ)) e B) :
    ∃ B', ScopedTypeRecovery (fun _ _ _ => False) (proofEraseCtx Γ)
        (e.inst (proofErase Γ image)) B' ∧ BetaLevelJoin B' (B.inst (proofErase Γ image)) := by
  have HA : PureLambda (proofErase Γ assigned) := by rw [(erasures hΓ).2]; trivial
  simpa only [inst_eq_subst, Subst.liftN] using
    erased_expansion_union_native_joined_subst R (HΔ.cons HA) HE
      (joined_image_without_exact_recovery (D := D) hΓ).2

end Lean4Lean.VEnv.Strengthening.TypeFunctionExample
