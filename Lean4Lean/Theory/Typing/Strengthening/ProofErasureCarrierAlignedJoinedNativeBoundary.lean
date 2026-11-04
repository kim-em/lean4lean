import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedJoinedNativeApplication
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary

/-! # Eta still prevents universal joined native coverage

Controlled expansions and universe conversion do not make beta/universe joins
complete for assigned types, even in pure contexts. The existing eta-converted
variable example has no native output joined to its assigned neutral type.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private scoped_normal_fixed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
namespace EtaRecoveryJoinBoundary
open private functionType familyType context native assigned nativeRaw assignedRaw
  context_wf source_typed native_typed types_equal erasures normal_forms
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary

private theorem raw_no_join : ¬ BetaLevelJoin nativeRaw assignedRaw := by
  rintro ⟨a, b, RA, RB, V⟩
  have EA := scoped_normal_fixed
    (ScopedCompute.beta (Step := fun _ _ _ => False) (Δ := []) RA)
    (fun Δ => (normal_forms (Step := fun _ _ _ => False) (fun H => H.elim) Δ).1)
  have EB := scoped_normal_fixed
    (ScopedCompute.beta (Step := fun _ _ _ => False) (Δ := []) RB)
    (fun Δ => (normal_forms (Step := fun _ _ _ => False) (fun H => H.elim) Δ).2)
  rw [EA, EB] at V
  cases V with
  | app _ H => cases H

variable [Params]
private theorem context_pure (H : PureContext (proofEraseCtx Γ)) :
    PureContext (proofEraseCtx (context Γ)) := by
  simp only [context, proofEraseCtx]
  apply PureContext.cons
  · apply PureContext.cons
    · apply PureContext.cons H
      simp only [functionType, proofErase]
      repeat' first | split | constructor | trivial
    · simp only [familyType, functionType, proofErase]
      repeat' first | split | constructor | trivial
  · simp only [proofErase]
    repeat' first | split | constructor | trivial

/-- Eta-converted assigned types defeat joined native coverage in the entire
expanded union, even with pure source, assigned type and context erasures.
This holds over every pure well-formed base and every definition collection. -/
theorem expansion_joined_native_failure (D : PureObservation.Definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) (HΓ : PureContext (proofEraseCtx Γ)) :
    ∃ Γ' e A, OnCtx Γ' (env.IsType univs) ∧ env.HasType univs Γ' e A ∧ ¬ IsProof Γ' e ∧
      PureContext (proofEraseCtx Γ') ∧ PureLambda (proofErase Γ' e) ∧ PureLambda (proofErase Γ' A) ∧
      (∃ native, ScopedTypeRecovery (ErasedExpansionStage D 0) (proofEraseCtx Γ') (proofErase Γ' e) native ∧
        CarrierAlignedCompare (ErasedExpansionStage D 0) (proofEraseCtx Γ') false native (proofErase Γ' A)) ∧
      ∀ T, ScopedTypeRecovery (ErasedExpansionUnion D) (proofEraseCtx Γ') (proofErase Γ' e) T →
        ¬ BetaLevelJoin T (proofErase Γ' A) := by
  have hC := context_wf hΓ
  have hn := not_proof_at_positive_type hC native_typed source_typed
  have Ee : proofErase (context Γ) (.bvar 0) = .bvar 0 := if_neg hn
  obtain ⟨EN, EA⟩ := erasures hΓ
  have EO : contextOracle (proofEraseCtx (context Γ)) 0 = nativeRaw := by
    rw [proofEraseCtx_oracle, erasedTypeOracle_valid hC (Lookup.zero (ty := VExpr.app (.bvar 0) (.bvar 1)))]
    exact EN
  refine ⟨context Γ, .bvar 0, assigned, hC, types_equal.symm.defeq source_typed, hn,
    context_pure HΓ, ?_, ?_, ?_, ?_⟩
  · rw [Ee]; trivial
  · rw [EA]; trivial
  · refine ⟨nativeRaw, ?_, ?_⟩
    · rw [Ee, ← EO]; exact .bvar
    · rw [EA]
      exact .symm (.base (.base (.app (.leaf .refl)
        (.leaf (.etaL (.boundVar (f := ProofShape.bvar 2)))))))
  · intro T R HJ
    rw [Ee] at R
    have RC := R.bvar_compute
    rw [EO] at RC
    have HN := erased_expansion_union_pure_join RC (context_pure HΓ) (by trivial)
    exact raw_no_join (HN.trans (by simpa only [EA] using HJ))

/-- The obstruction exists without any extra environment declaration or base
context assumption; in particular it persists when canonical Eq is available. -/
theorem expansion_joined_native_failure_empty (D : PureObservation.Definitions) :
    ∃ Γ e A, OnCtx Γ (env.IsType univs) ∧ env.HasType univs Γ e A ∧ ¬ IsProof Γ e ∧
      PureContext (proofEraseCtx Γ) ∧ PureLambda (proofErase Γ e) ∧ PureLambda (proofErase Γ A) ∧
      (∃ native, ScopedTypeRecovery (ErasedExpansionStage D 0) (proofEraseCtx Γ) (proofErase Γ e) native ∧
        CarrierAlignedCompare (ErasedExpansionStage D 0) (proofEraseCtx Γ) false native (proofErase Γ A)) ∧
      ∀ T, ScopedTypeRecovery (ErasedExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ e) T →
        ¬ BetaLevelJoin T (proofErase Γ A) :=
  expansion_joined_native_failure (Γ := []) D trivial (by intro a ha; cases ha)

end EtaRecoveryJoinBoundary
end Lean4Lean.VEnv.Strengthening
