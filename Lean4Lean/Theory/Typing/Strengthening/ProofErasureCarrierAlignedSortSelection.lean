import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedSortExposure

/-! # Selecting the assigned universe from existing native evidence

Native recovery and an aligned comparison to the assigned universe suffice
for exact sort recovery. Coverage is still an explicit input: these results
neither create native recovery for arbitrary typed terms nor prove that all
semantically equal types have aligned comparison certificates.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Select the exact assigned sort from an existing native output and its
aligned comparison. Explicit level steps repair syntactically different but
equivalent universes; no global join or native coverage premise is used. -/
theorem proofErase_carrier_aligned_recovered_sort_exact
    (hstep : ErasedScopedPrimitiveDescent Step) (hn : SortRootLevels Step)
    (hlevel : ∀ {Δ a b}, LevelPrimitive univs a b → Step Δ a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e (.sort u))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ e) T)
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode T (.sort u)) :
    ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ e) (.sort u) := by
  obtain ⟨T₀, heT, ET⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ he R
  obtain ⟨v, hT⟩ := heT.isType henv hΓ
  have hu := he.sort_r henv hΓ
  have hU : env.HasType univs Γ (.sort u) (.sort (.succ u)) := .sort hu
  have EU : proofErase Γ (.sort u) = .sort u := if_neg (not_isProof_of_sort hΓ hU)
  obtain ⟨w, RC, HL⟩ := proofErase_carrier_aligned_sort_levels_exposure hstep hn hΓ hU hT
    (by simpa only [EU, ET] using H.symm) EU
  have RC : ScopedCompute Step (proofEraseCtx Γ) T (.sort w) := by simpa only [ET] using RC
  exact R.convert (RC.trans (.base (hlevel (.sort HL.symm hu))))

/-- At a typed type, existence of native evidence aligned with its assigned
universe is equivalent to native recovery of that exact universe. Neither
side is asserted universally. -/
theorem proofErase_carrier_aligned_recovered_sort_exact_iff
    (hstep : ErasedScopedPrimitiveDescent Step) (hn : SortRootLevels Step)
    (hlevel : ∀ {Δ a b}, LevelPrimitive univs a b → Step Δ a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e (.sort u)) :
    (∃ T, ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ e) T ∧
      CarrierAlignedCompare Step (proofEraseCtx Γ) mode T (.sort u)) ↔
    ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ e) (.sort u) := by
  constructor
  · rintro ⟨T, R, H⟩
    exact proofErase_carrier_aligned_recovered_sort_exact hstep hn hlevel hΓ he R H
  · intro R
    exact ⟨_, R, .base (.base (.leaf .refl))⟩

/-- Exact sort selection stays at the original finite level-extended stage. -/
theorem proofErase_carrier_aligned_level_stage_recovered_sort_exact
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e (.sort u))
    (R : ScopedTypeRecovery (ErasedLevelRecoveredStage D stage) (proofEraseCtx Γ) (proofErase Γ e) T)
    (H : CarrierAlignedCompare (ErasedLevelRecoveredStage D stage) (proofEraseCtx Γ) mode T (.sort u)) :
    ScopedTypeRecovery (ErasedLevelRecoveredStage D stage) (proofEraseCtx Γ) (proofErase Γ e) (.sort u) :=
  proofErase_carrier_aligned_recovered_sort_exact (erased_level_recovered_stage_descent heq hs stage)
    (erased_level_recovered_stage_sort_levels stage)
    (fun H => erased_level_primitive_into_stage H stage) hΓ he R H

/-- Exact sort selection also holds in the closed level-extended union. -/
theorem proofErase_carrier_aligned_level_union_recovered_sort_exact
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e (.sort u))
    (R : ScopedTypeRecovery (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ e) T)
    (H : CarrierAlignedCompare (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) mode T (.sort u)) :
    ScopedTypeRecovery (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ e) (.sort u) :=
  proofErase_carrier_aligned_recovered_sort_exact (erased_level_recovered_union_descent heq hs)
    erased_level_recovered_union_sort_levels
    (fun H => ⟨0, erased_level_primitive_into_stage H 0⟩) hΓ he R H

end Lean4Lean.VEnv.Strengthening
