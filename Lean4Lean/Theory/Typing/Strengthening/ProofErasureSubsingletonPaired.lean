import Lean4Lean.Theory.Typing.Strengthening.RecursiveDataCarrier

/-! # Paired instantiation at structurally subsingleton result carriers

The result certificate, rather than endpoint annotation comparison, closes this
fragment of paired substitution. Function results into empty structures are
included and need not be proofs or terminating terms. General paired closure
outside this carrier grammar remains unproved.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Paired instantiation closes at a structurally subsingleton result type,
using only the argument carrier certificate. No body comparison, normalization,
or relation between internal lambda annotations is required. -/
theorem carrier_paired_instantiation_subsingleton
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hb' : env.HasType univs (A :: Γ) b' B)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HX : ProofShape.StructureCarrierGuard Step (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ x) (proofErase Γ y))
    (HS : ProofShape.SubsingletonCarrier (proofErase (A :: Γ) B)) :
    env.IsDefEq univs Γ (b.inst x) (b'.inst y) (B.inst x) ∧
      ProofShape.StructureCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ (B.inst x))
        (proofErase Γ (b.inst x)) (proofErase Γ (b'.inst y)) := by
  have Hxy := proofErase_structure_carrier_reflect hstep hΓ hx hy HX
  have Hbb' := proofErase_subsingleton_carrier_descend hΓA hb hb' (n := 0) (k := 0)
    (by simpa only [ProofShape.liftN_zero] using HS)
  obtain ⟨_, hB⟩ := hb.isType henv hΓA
  have HS' : ProofShape.SubsingletonCarrier (proofErase Γ (B.inst x)) := by
    rw [proofErase_instN hΓA hx Ctx.InstN.zero hB]
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
      HS.subst (ProofShape.Subst.one (proofErase Γ x))
  exact ⟨IsDefEq.instDF henv.ordered hΓ Hbb' Hxy, .subsingleton HS'⟩

/-- The fixed-data function result of the new recursive test lies in the proved
paired fragment, including a proposition parameter depending on the substituted
argument. This uses the carrier-aware output relation, not ScopedCompare. -/
theorem carrier_paired_instantiation_data_result
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hd : env.constants d = some ⟨0, .sort (.succ .zero)⟩)
    (hi : env.projections d info) (hp : info.nparams = 0)
    (hix : info.nindices = 0) (hf : info.numFields = 0)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hP : env.HasType univs (A :: Γ) P (.sort .zero))
    (hb : env.HasType univs (A :: Γ) b (RecursiveData.result d P))
    (hb' : env.HasType univs (A :: Γ) b' (RecursiveData.result d P))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HX : ProofShape.StructureCarrierGuard Step (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ x) (proofErase Γ y)) :
    env.IsDefEq univs Γ (b.inst x) (b'.inst y) ((RecursiveData.result d P).inst x) ∧
      ProofShape.StructureCarrierGuard Step (proofEraseCtx Γ)
        (proofErase Γ ((RecursiveData.result d P).inst x))
        (proofErase Γ (b.inst x)) (proofErase Γ (b'.inst y)) :=
  carrier_paired_instantiation_subsingleton hstep hΓ hΓA hb hb' hx hy HX
    (RecursiveData.result_subsingleton hd hi hp hix hf hΓA hP)

end Lean4Lean.VEnv.Strengthening
