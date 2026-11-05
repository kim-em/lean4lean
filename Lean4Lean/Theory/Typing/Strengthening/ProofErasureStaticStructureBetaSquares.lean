import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureCommonApplication
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeContextJoin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureBackwardContext

/-! # Beta residuals with independently computed bodies and arguments

The original retained argument supplies its native certificate. Instantiate the
body computation first, then compute the argument through the realized body.
The resulting raw argument needs no new recovery, and body paths can be pulled
back from any binder reached by the original domain's computation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Full structure/function-eta body and argument computations have the exact
instantiated residual. Only the original retained argument requires native
recovery; neither the computed body nor the computed argument needs an assigned
native type. Proof arguments discharge the recovery premise vacuously. -/
theorem static_structure_body_argument_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) outB)
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) outX) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (outB.inst outX) := by
  have R₁ := static_structure_union_compute_inst heq hs hΓA.1 hx HR hb RB
  obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓA hb rfl rfl RB
  have R₂ := proofErase_static_structure_compute_inst_argument heq hs hΓA HB.hasType.2 hx RX
  rw [proofErase_instN hΓA hx Ctx.InstN.zero HB.hasType.2, EB] at R₂
  exact R₁.trans R₂

/-- The domain may compute before the body, which then uses the new binder.
Backward context transport returns that body path to the original binder before
instantiation. The argument can compute independently and lose exact recovery.
The final lambda annotation is discarded by the residual beta step. -/
theorem static_structure_changed_binder_beta_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAC : env.IsDefEq univs Γ A C (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ C))
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (C :: Γ))
      (proofErase (C :: Γ) b) outB)
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) outX) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (outB.inst outX) ∧
      ∀ annotation, ProofShape.BetaRed (.app (.lam annotation outB) outX) (outB.inst outX) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAC.hasType.1⟩
  have HC : IsDefEqCtx env univs Γ (A :: Γ) (C :: Γ) := .succ .zero HAC
  have hbC := hb.defeqDFC henv HC
  have RB' := proofErase_static_structure_union_compute_backward_context heq hs hΓ HAC RA hbC RB
  exact ⟨static_structure_body_argument_square heq hs hΓA hb hx HR RB' RX, fun _ => .beta⟩

end Lean4Lean.VEnv.Strengthening
