import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSubsingletonPaired

/-! # The fixed-data loop test in an actual canonical-Eq extension

The recursion is installed by the checked declaration constructor. Its original
and unfolded domain annotations give non-proof looping terms, accepted by the
carrier guard at stage zero. This is a checked positive fragment, not a proof
of general strengthening or consistency of every such extension.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr

/-- The actual fixed-data extension supplies both recursive annotations and
non-proof loops, and the carrier-aware comparison accepts them at stage zero.
The data constant and empty-structure metadata are inherited from the base. -/
theorem canonical_data_loop_carrier {base : VEnv}
    (hbase : base.WF) (heq : base.HasCanonicalEq) (hfresh : base.constants c = none)
    (hd : base.constants d = some ⟨0, .sort (.succ .zero)⟩)
    (hi : base.projections d info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0) :
    letI := (RecursiveData.extended_wf hbase hfresh hd).params 0
    (RecursiveData.extended base c d).HasCanonicalEq ∧
    ∀ {Γ P}, OnCtx Γ ((RecursiveData.extended base c d).IsType 0) →
      (RecursiveData.extended base c d).HasType 0 Γ P (.sort .zero) →
      let D := RecursiveData.domain c P
      let D' := RecursiveData.unfolded c d P
      let T := RecursiveData.result d P
      (RecursiveData.extended base c d).HasType 0 Γ (RecursiveDomain.omegaTerm D) T ∧
      (RecursiveData.extended base c d).HasType 0 Γ (RecursiveDomain.omegaTerm D') T ∧
      ¬ IsProof Γ (RecursiveDomain.omegaTerm D) ∧
      ¬ IsProof Γ (RecursiveDomain.omegaTerm D') ∧
      (RecursiveData.extended base c d).IsDefEq 0 Γ
        (RecursiveDomain.omegaTerm D) (RecursiveDomain.omegaTerm D') T ∧
      ProofShape.StructureCarrierGuard (ErasedStructureSingletonStage ErasedCore.definitions 0)
        (proofEraseCtx Γ) (proofErase Γ T)
        (proofErase Γ (RecursiveDomain.omegaTerm D)) (proofErase Γ (RecursiveDomain.omegaTerm D')) := by
  letI := (RecursiveData.extended_wf hbase hfresh hd).params 0
  refine ⟨RecursiveData.extended_canonicalEq heq hfresh hd, ?_⟩
  intro Γ P hΓ hP
  have hne : c ≠ d := by intro E; subst d; rw [hfresh] at hd; cases hd
  have hd' : (RecursiveData.extended base c d).constants d = some ⟨0, .sort (.succ .zero)⟩ := by
    simpa [RecursiveData.extended, RecursiveData.stub, VEnv.addDefEq, hne] using hd
  have hi' : (RecursiveData.extended base c d).projections d info := hi
  have HP := RecursiveData.recursive (fun Γ => RecursiveData.equation 0 Γ) hΓ hP
  have hT := RecursiveData.result_typed hd' hP
  have HP' := IsDefEq.forallEDF HP (hT.weak (RecursiveData.extended_wf hbase hfresh hd))
  have Hloops := RecursiveData.loop_carrier_compare
    (Step := ErasedStructureSingletonStage ErasedCore.definitions 0)
    hd' hi' hp hx hf hΓ hP HP HP'
  exact ⟨RecursiveType.inhabit_result HP, RecursiveType.inhabit_result HP',
    RecursiveData.loop_not_proof hd' hΓ hP HP,
    RecursiveData.loop_not_proof hd' hΓ hP HP', Hloops⟩

end Lean4Lean.VEnv.Strengthening
