import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionNativeExposure

/-! # Exact universe selection from an observed native sort

Operational exposure supplies an actual sort typing. Ordinary uniqueness then
aligns its universe with the assigned universe, and an explicit level step
selects that exact output. No rigid-sort-root assumption is used.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_sort_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
variable [Params]

/-- A native output with a beta-sort observation can select the actual assigned
universe exactly. Native coverage and the observation remain explicit inputs. -/
theorem proofErase_native_sort_selection_of_headObservation
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hlevel : ∀ {Δ a b}, LevelPrimitive univs a b → Step Δ a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e (.sort u))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ e) out)
    (HO : HeadObservation (fun _ _ => False) out .sort) :
    ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ e) (.sort u) := by
  obtain ⟨v, RB⟩ := HO.sort_exposure
  have RN := R.convert (ScopedCompute.beta RB)
  obtain ⟨A, heA, EA⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ ht RN
  obtain rfl := erase_sort_inv EA
  have HL := (ht.uniqU henv hΓ heA).sort_inv henv hΓ
  exact RN.convert (.base (hlevel (.sort HL.symm (ht.sort_r henv hΓ))))

/-- Exact observed-sort selection at the unchanged expanded stage. -/
theorem proofErase_expansion_stage_native_sort_selection
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e (.sort u))
    (R : ScopedTypeRecovery (ErasedExpansionStage D stage) (proofEraseCtx Γ) (proofErase Γ e) out)
    (HO : HeadObservation (fun _ _ => False) out .sort) :
    ScopedTypeRecovery (ErasedExpansionStage D stage) (proofEraseCtx Γ) (proofErase Γ e) (.sort u) :=
  proofErase_native_sort_selection_of_headObservation (erased_expansion_stage_descent heq hs stage)
    (fun H => erased_level_into_expansion_stage stage (erased_level_primitive_into_stage H stage)) hΓ ht R HO

/-- Exact observed-sort selection over the full expanded union. -/
theorem proofErase_expansion_union_native_sort_selection
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e (.sort u))
    (R : ScopedTypeRecovery (ErasedExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ e) out)
    (HO : HeadObservation (fun _ _ => False) out .sort) :
    ScopedTypeRecovery (ErasedExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ e) (.sort u) :=
  proofErase_native_sort_selection_of_headObservation (erased_expansion_union_descent heq hs)
    (fun H => ⟨0, erased_level_into_expansion_stage 0 (erased_level_primitive_into_stage H 0)⟩) hΓ ht R HO

/-- Any existing native certificate for an actual Pi type recovers its exact
assigned universe, even after arbitrary conversions in the expanded system. -/
theorem proofErase_expansion_stage_native_forallE_sort
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ (.forallE A B) (.sort u))
    (R : ScopedTypeRecovery (ErasedExpansionStage D stage) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A B)) out) :
    ScopedTypeRecovery (ErasedExpansionStage D stage) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A B)) (.sort u) := by
  have E : proofErase Γ (.forallE A B) = .forallE (proofErase Γ A) (proofErase (A :: Γ) B) :=
    if_neg (not_isProof_of_sort hΓ ht)
  exact proofErase_expansion_stage_native_sort_selection heq hs hΓ ht R
    ((E ▸ R).forallE_headObservation (erased_expansion_stage_headObservation stage))

/-- The same exact universe repair holds for union-native Pi evidence. -/
theorem proofErase_expansion_union_native_forallE_sort
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ (.forallE A B) (.sort u))
    (R : ScopedTypeRecovery (ErasedExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A B)) out) :
    ScopedTypeRecovery (ErasedExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A B)) (.sort u) := by
  have E : proofErase Γ (.forallE A B) = .forallE (proofErase Γ A) (proofErase (A :: Γ) B) :=
    if_neg (not_isProof_of_sort hΓ ht)
  exact proofErase_expansion_union_native_sort_selection heq hs hΓ ht R
    ((E ▸ R).forallE_headObservation erased_expansion_union_headObservation)

end Lean4Lean.VEnv.Strengthening
