import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedExpansionSelection

/-! # Pi selection retaining a domain join under controlled expansion

A raw beta/universe join against a displayed Pi exposes a Pi together with
component joins. Typed domain replay turns its domain join into a computed
comparison, without a no-Pi-root law for the expanded relation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
namespace ProofShape
open private beta_forallE_parts
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin
open private variant_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedPrimitiveVariants

/-- A raw join against a Pi exposes a beta reduct with joins of both components.
The domains need not be syntactically equal or individually beta-normal. -/
theorem BetaLevelJoin.pi_exposure (H : BetaLevelJoin a (.forallE A B)) :
    ∃ X Y, BetaRed a (.forallE X Y) ∧ BetaLevelJoin X A ∧ BetaLevelJoin Y B := by
  obtain ⟨a', b', RA, RB, V⟩ := H
  obtain ⟨A', B', rfl, RAA, RBB⟩ := beta_forallE_parts RB
  obtain ⟨X, Y, rfl, VX, VY⟩ := variant_forallE_inv V.symm
  exact ⟨X, Y, RA, ⟨X, A', .refl, RAA, VX.symm⟩,
    ⟨Y, B', .refl, RBB, VY.symm⟩⟩

end ProofShape
variable [Params]

/-- Raw joins to actual typed endpoints are computed comparisons in every
relation containing explicit level conversion. The inferred mode is allowed. -/
theorem proofErase_carrier_aligned_raw_join_compare
    (hlevel : ∀ {Δ a b}, LevelPrimitive univs a b → Step Δ a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (hb : env.HasType univs Γ b B)
    (HJ : BetaLevelJoin a (proofErase Γ b)) :
    ComputedJointCompare Step (proofEraseCtx Γ) mode a (proofErase Γ b) := by
  obtain ⟨out, RA, RB⟩ := proofErase_carrier_aligned_raw_join_realize hΓ hb HJ
  exact .compute (RA.mono hlevel) (RB.mono hlevel) (.leaf .refl)

/-- Existing native evidence joined to a Pi selects a native Pi with a computed
comparison of its domain to the actual assigned domain. The codomain retains
its raw join at the two original binder annotations. -/
theorem proofErase_carrier_aligned_joined_pi_selection
    (hlevel : ∀ {Δ a b}, LevelPrimitive univs a b → Step Δ a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (RN : ScopedTypeRecovery Step (proofEraseCtx Γ) source native)
    (HJ : BetaLevelJoin native (.forallE (proofErase Γ A) B)) :
    ∃ X Y, ScopedTypeRecovery Step (proofEraseCtx Γ) source (.forallE X Y) ∧
      ComputedJointCompare Step (proofEraseCtx Γ) false X (proofErase Γ A) ∧
      BetaLevelJoin Y B := by
  obtain ⟨X, Y, R, HX, HY⟩ := HJ.pi_exposure
  exact ⟨X, Y, RN.convert (.beta R),
    proofErase_carrier_aligned_raw_join_compare hlevel hΓ hA HX, HY⟩

/-- Every expanded path from a pure assigned Pi to an existing native output
admits native Pi selection with its domain comparison at the original native
stage. The two stages can be unrelated. -/
theorem proofErase_carrier_aligned_expansion_native_pi_selection
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (HΔ : PureContext (proofEraseCtx Γ)) (HA : PureLambda (proofErase Γ A)) (HB : PureLambda B)
    (RN : ScopedTypeRecovery (ErasedExpansionStage D n) (proofEraseCtx Γ) source native)
    (RA : ScopedCompute (ErasedExpansionStage D k) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) B) native) :
    ∃ X Y, ScopedTypeRecovery (ErasedExpansionStage D n) (proofEraseCtx Γ) source (.forallE X Y) ∧
      ComputedJointCompare (ErasedExpansionStage D n) (proofEraseCtx Γ) false X (proofErase Γ A) ∧
      BetaLevelJoin Y B :=
  proofErase_carrier_aligned_joined_pi_selection
    (fun H => erased_level_into_expansion_stage n (erased_level_primitive_into_stage H n))
    hΓ hA RN (erased_expansion_stage_pure_join RA HΔ ⟨HA, HB⟩).symm

/-- The same Pi selection and domain comparison hold for arbitrary expanded
union paths. No guarded confluence or exact assigned-type recovery is needed. -/
theorem proofErase_carrier_aligned_expansion_union_native_pi_selection
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (HΔ : PureContext (proofEraseCtx Γ)) (HA : PureLambda (proofErase Γ A)) (HB : PureLambda B)
    (RN : ScopedTypeRecovery (ErasedExpansionUnion D) (proofEraseCtx Γ) source native)
    (RA : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) B) native) :
    ∃ X Y, ScopedTypeRecovery (ErasedExpansionUnion D) (proofEraseCtx Γ) source (.forallE X Y) ∧
      ComputedJointCompare (ErasedExpansionUnion D) (proofEraseCtx Γ) false X (proofErase Γ A) ∧
      BetaLevelJoin Y B :=
  proofErase_carrier_aligned_joined_pi_selection
    (fun H => ⟨0, erased_level_into_expansion_stage 0 (erased_level_primitive_into_stage H 0)⟩)
    hΓ hA RN (erased_expansion_union_pure_join RA HΔ ⟨HA, HB⟩).symm

end Lean4Lean.VEnv.Strengthening
