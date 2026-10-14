import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrefixKStages
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextPrefixBoundary

/-! # Repairing the partial-recursion composition obstruction

The new prefix computation sends both previously incomparable short endpoints
to their common lambda value. The repair uses stage one, works in every canonical
Eq environment, and proves strict inclusion over the earlier beta/full-K fragment.
General composition and declarative completeness are not asserted.
-/
namespace Lean4Lean.VEnv.Strengthening.ContextPrefixWitness
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Every primitive of the counterexample fragment embeds in the first enriched
stage, so all of its contextual certificates remain available. -/
theorem step_into_prefix (H : Step a b) : ErasedPrefixKStage D 1 a b := by
  cases H with
  | intro HC => exact .inr (.inl (.intro (.base (HC.mono (by intros; contradiction)))))

/-- Both typed partial recursors compute to the same lambda after one layer of
prefix K. Their reflexive endpoint guards require no primitive computation. -/
theorem prefixes_join (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ProofShape.Compute (ErasedPrefixKStage D 1)
      (proofErase Γ (partialRec dependentMotive)) (proofErase Γ bridge) ∧
    ProofShape.Compute (ErasedPrefixKStage D 1)
      (proofErase Γ (partialRec constantMotive)) (proofErase Γ bridge) := by
  constructor
  · have H := proofErase_prefix_K_stage_forward (D := D) (stage := 0) heq hs hΓ
      (dependent_typed heq) (.base .refl)
    simpa only [partialRec, eqRecBeforeMajor, bridge, proofDomain, payload, lift, liftN] using H
  · have H := proofErase_prefix_K_stage_forward (D := D) (stage := 0) heq hs hΓ
      (constant_typed heq hΓ) (.base .refl)
    simpa only [partialRec, eqRecBeforeMajor, bridge, proofDomain, payload, lift, liftN] using H

/-- The repaired comparison also lies in the raw guard fragment, so it can
certify later full or prefix K steps without a contextual-guard extension. -/
theorem prefixes_raw_compare (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ProofShape.RawCheckedCompare (ErasedPrefixKStage D 1) mode
      (proofErase Γ (partialRec dependentMotive)) (proofErase Γ (partialRec constantMotive)) := by
  obtain ⟨HL, HR⟩ := prefixes_join heq hs hΓ
  exact .compute HL HR (.base .refl)

/-- The old nontransitivity endpoints now compare directly through a finite
computational join. No transitivity or composition premise is used. -/
theorem prefixes_compare (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ProofShape.ContextCompare (ErasedPrefixKStage D 1) (proofEraseCtx Γ) mode
      (proofErase Γ (partialRec dependentMotive)) (proofErase Γ (partialRec constantMotive)) := by
  obtain ⟨HL, HR⟩ := prefixes_join heq hs hΓ
  exact .compute HL HR .refl

/-- Stage one strictly extends the earlier contextual beta/full-K fragment at
common-typed originals in the empty context. This records an actual repair of
the checked obstruction, rather than assuming a stronger composition law. -/
theorem prefix_context_strict_extension (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∃ a b T, env.HasType univs [] a T ∧ env.HasType univs [] b T ∧
      ProofShape.ContextCompare (ErasedPrefixKStage D 1) (proofEraseCtx []) true
        (proofErase [] a) (proofErase [] b) ∧
      ¬ ProofShape.ContextCompare Step (proofEraseCtx []) true (proofErase [] a) (proofErase [] b) :=
  ⟨_, _, _, dependent_typed heq, constant_typed heq trivial,
    prefixes_compare heq hs trivial, prefixes_not_compare heq trivial⟩

end Lean4Lean.VEnv.Strengthening.ContextPrefixWitness
