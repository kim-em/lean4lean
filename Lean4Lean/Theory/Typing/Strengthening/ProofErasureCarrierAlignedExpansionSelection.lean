import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedExpansionJoin

/-! # Native selection across controlled expansions

Pure expanded computations retain native common-reduct evidence at its original
stage. A sort demand can be selected exactly from the raw join certificate.
These statements preserve existing native evidence; they do not assert coverage.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
namespace ProofShape
open private beta_sort from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedSortRoot

/-- A raw join to a well-formed sort yields a forward path to that exact sort.
Beta reduction fixes sorts, so only one final universe step can be needed. -/
theorem BetaLevelJoin.sort_compute (H : BetaLevelJoin a (.sort u)) (hu : u.WF U) :
    ScopedCompute (fun _ => LevelPrimitive U) Δ a (.sort u) := by
  obtain ⟨a', b', RA, RB, V⟩ := H
  obtain rfl := beta_sort RB rfl
  cases V with
  | refl => exact .beta RA
  | sort H => exact (ScopedCompute.beta RA).trans (.base (.sort H hu))

end ProofShape
variable [Params]

/-- Expanded-stage selections of a pure carrier retain a native common reduct
at the original native stage, regardless of the stages used by the two paths. -/
theorem proofErase_carrier_aligned_expansion_native_selection
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (HΔ : PureContext (proofEraseCtx Γ)) (HP : PureLambda (proofErase Γ A))
    (RN : ScopedTypeRecovery (ErasedExpansionStage D n) (proofEraseCtx Γ) source native)
    (RA : ScopedCompute (ErasedExpansionStage D k) (proofEraseCtx Γ) (proofErase Γ A) native)
    (RS : ScopedCompute (ErasedExpansionStage D m) (proofEraseCtx Γ) (proofErase Γ A) selected) :
    ∃ out, ScopedTypeRecovery (ErasedExpansionStage D n) (proofEraseCtx Γ) source out ∧
      ScopedCompute (fun _ => LevelPrimitive univs) (proofEraseCtx Γ) selected out := by
  obtain ⟨out, RN', RS'⟩ := proofErase_carrier_aligned_expansion_stage_confluent
    heq hs hΓ hA HΔ HP RA RS
  exact ⟨out, RN.convert (RN'.mono (fun H => erased_level_into_expansion_stage n
    (erased_level_primitive_into_stage H n))), RS'⟩

/-- The expanded union retains native common-reduct evidence under further
selection of a typed pure carrier in a pure context. -/
theorem proofErase_carrier_aligned_expansion_union_native_selection
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (HΔ : PureContext (proofEraseCtx Γ)) (HP : PureLambda (proofErase Γ A))
    (RN : ScopedTypeRecovery (ErasedExpansionUnion D) (proofEraseCtx Γ) source native)
    (RA : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ A) native)
    (RS : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ A) selected) :
    ∃ out, ScopedTypeRecovery (ErasedExpansionUnion D) (proofEraseCtx Γ) source out ∧
      ScopedCompute (fun _ => LevelPrimitive univs) (proofEraseCtx Γ) selected out := by
  obtain ⟨out, RN', RS'⟩ := proofErase_carrier_aligned_expansion_union_confluent
    heq hs hΓ hA HΔ HP RA RS
  exact ⟨out, RN.convert (RN'.mono (fun H => ⟨0, erased_level_into_expansion_stage 0
    (erased_level_primitive_into_stage H 0)⟩)), RS'⟩

/-- Existing native evidence and any raw beta/universe join to a well-formed
sort suffice for exact native selection whenever the stage includes level steps. -/
theorem proofErase_carrier_aligned_joined_sort_exact
    (hlevel : ∀ {Δ a b}, LevelPrimitive univs a b → Step Δ a b)
    (RN : ScopedTypeRecovery Step Δ source native) (HJ : BetaLevelJoin native (.sort u))
    (hu : u.WF univs) : ScopedTypeRecovery Step Δ source (.sort u) :=
  RN.convert ((HJ.sort_compute hu).mono hlevel)

/-- A pure expanded path from the assigned sort to an existing native output
can be reversed for exact sort selection at the original native stage. The
native source itself need not be pure, and no canonical Eq hypothesis is needed. -/
theorem proofErase_carrier_aligned_expansion_native_sort_exact
    (HΔ : PureContext Δ) (hu : u.WF univs)
    (RN : ScopedTypeRecovery (ErasedExpansionStage D n) Δ source native)
    (RA : ScopedCompute (ErasedExpansionStage D k) Δ (.sort u) native) :
    ScopedTypeRecovery (ErasedExpansionStage D n) Δ source (.sort u) :=
  proofErase_carrier_aligned_joined_sort_exact
    (fun H => erased_level_into_expansion_stage n (erased_level_primitive_into_stage H n))
    RN (erased_expansion_stage_pure_join RA HΔ trivial).symm hu

/-- Exact sort selection also holds for arbitrary expanded union paths. -/
theorem proofErase_carrier_aligned_expansion_union_native_sort_exact
    (HΔ : PureContext Δ) (hu : u.WF univs)
    (RN : ScopedTypeRecovery (ErasedExpansionUnion D) Δ source native)
    (RA : ScopedCompute (ErasedExpansionUnion D) Δ (.sort u) native) :
    ScopedTypeRecovery (ErasedExpansionUnion D) Δ source (.sort u) :=
  proofErase_carrier_aligned_joined_sort_exact
    (fun H => ⟨0, erased_level_into_expansion_stage 0 (erased_level_primitive_into_stage H 0)⟩)
    RN (erased_expansion_union_pure_join RA HΔ trivial).symm hu

end Lean4Lean.VEnv.Strengthening
