import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedExpansionJoin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointChecking

/-! # Returning from non-eta conversion tails at pure normal endpoints

Pure expansion computation gives a beta/universe join. If its source is
beta-normal, the left beta path is fixed; typing of that source supplies the
universe well-formedness needed to reverse the remaining structural variation.
Thus the tail returns to its exact source using only beta and universe steps.
No normalization or confluence of the full guarded language is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- A beta/universe join to an actually typed beta-normal endpoint is a
forward beta/universe computation to that exact endpoint. No typing or normal
form for the other endpoint is required. -/
theorem proofErase_normal_beta_level_join_return
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (HN : NormalSyntax (fun _ _ => False) (proofErase Γ e))
    (HJ : BetaLevelJoin out (proofErase Γ e)) :
    ScopedCompute (fun _ => LevelPrimitive univs) (proofEraseCtx Γ) out (proofErase Γ e) := by
  obtain ⟨a, b, RA, RB, V⟩ := HJ
  have E := RB.fixed_of_normal HN
  rw [E] at V
  exact (ScopedCompute.beta RA).trans
    ((proofErase_carrier_aligned_variant_level_compute V hΓ he).scoped (fun H => .base H))

/-- Every non-eta union tail from a pure beta-normal typed erasure returns
to its exact source. Tails may use any singleton stage and both controlled
expansions; only the source and its context must be pure. This does not assume
canonical Eq, sound definitions, or normalization of intermediate expressions. -/
theorem proofErase_pure_normal_expansion_return
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (HΔ : PureContext (proofEraseCtx Γ)) (HP : PureLambda (proofErase Γ e))
    (HN : NormalSyntax (fun _ _ => False) (proofErase Γ e))
    (R : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ScopedCompute (fun _ => LevelPrimitive univs) (proofEraseCtx Γ) out (proofErase Γ e) :=
  proofErase_normal_beta_level_join_return hΓ he HN
    (erased_expansion_union_pure_join R HΔ HP).symm

/-- A comparison between two pure normal typed endpoints survives independent
non-eta expansion tails. The target checking language only has to contain level
steps. The endpoints can have different types and need not share a core reduct;
the existing comparison is reused after each tail returns independently. -/
theorem proofErase_pure_normal_expansion_tails_compare
    (hlevel : ∀ {Δ a b}, LevelPrimitive univs a b → Step Δ a b)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (HΔ : PureContext (proofEraseCtx Γ))
    (HPa : PureLambda (proofErase Γ a)) (HPb : PureLambda (proofErase Γ b))
    (HNa : NormalSyntax (fun _ _ => False) (proofErase Γ a))
    (HNb : NormalSyntax (fun _ _ => False) (proofErase Γ b))
    (H : ComputedJointCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b))
    (RA : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ a) outA)
    (RB : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ b) outB) :
    ComputedJointCompare Step (proofEraseCtx Γ) mode outA outB :=
  .compute ((proofErase_pure_normal_expansion_return hΓ ha HΔ HPa HNa RA).mono hlevel)
    ((proofErase_pure_normal_expansion_return hΓ hb HΔ HPb HNb RB).mono hlevel) H

end Lean4Lean.VEnv.Strengthening
