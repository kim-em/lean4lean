import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureBetaSquares

/-! # Instantiation joins through a computed native argument

An argument need not recover its assigned type initially. A forward computation
to an image that does recover it suffices, for arbitrary dependent bodies and
full structure/function-eta computation. The common output is explicit.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- Instantiate at a later recoverable image. The source arm first computes
the argument, then the generic body; the other arm computes the same argument
through the realized body. No native recovery of the original argument or
restriction on the dependent body's type is required. -/
theorem static_structure_inst_join_computed_recovery
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) image)
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) image (proofErase Γ A))
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) (out.inst image) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (out.inst (proofErase Γ x)) (out.inst image) := by
  obtain ⟨y, Hxy, Ey⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓA.1 hx rfl rfl RX
  have HRy : ¬ IsProof Γ y → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ y) (proofErase Γ A) := by
    intro hn
    rw [Ey]
    exact HR (fun hp => hn ((isProof_congr hΓA.1 Hxy).1 hp))
  have Rfirst := proofErase_static_structure_compute_inst_argument heq hs hΓA hb hx RX
  have Rnext := static_structure_union_compute_inst heq hs hΓA.1 Hxy.hasType.2 HRy hb RB
  rw [proofErase_instN hΓA Hxy.hasType.2 Ctx.InstN.zero hb, Ey] at Rnext
  obtain ⟨b', Hbb', Eb⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓA hb rfl rfl RB
  have Rlast := proofErase_static_structure_compute_inst_argument heq hs hΓA Hbb'.hasType.2 hx RX
  rw [proofErase_instN hΓA hx Ctx.InstN.zero Hbb'.hasType.2, Eb] at Rlast
  exact ⟨Rfirst.trans Rnext, Rlast⟩

/-- Independent body and argument computations need no native certificate at
the intermediate argument when it reaches a later exactly recoverable image.
The computed body instance joins the original contractum there. -/
theorem static_structure_body_argument_join_native_pivot
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) image)
    (RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) image pivot)
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) pivot (proofErase Γ A))
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) (out.inst pivot) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (out.inst image) (out.inst pivot) := by
  obtain ⟨y, Hxy, Ey⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓA.1 hx rfl rfl RX
  obtain ⟨b', Hbb', Eb⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓA hb rfl rfl RB
  have Rlast := proofErase_static_structure_compute_inst_argument heq hs hΓA Hbb'.hasType.2
    Hxy.hasType.2 (Ey ▸ RP)
  rw [proofErase_instN hΓA Hxy.hasType.2 Ctx.InstN.zero Hbb'.hasType.2, Eb, Ey] at Rlast
  exact ⟨(static_structure_inst_join_computed_recovery heq hs hΓA hb hx (RX.trans RP) HR RB).1, Rlast⟩

end Lean4Lean.VEnv.Strengthening
