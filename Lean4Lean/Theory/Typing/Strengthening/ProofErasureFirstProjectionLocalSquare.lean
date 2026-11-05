import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFirstProjectionPivot

/-! # All single-step competitors of a first-projected historical cut

A step either lies in the major or acts at the projection root. The major case
uses the historical cut square; the root case transfers all native outputs
through field zero. Thus this marked context has no additional local premise.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Every single-occurrence competitor beneath or at the first projection of
an evolved beta cut joins contraction of the original cut. This is a local
square, not a strip theorem for arbitrary computation continuations. -/
theorem CutComponentHistory.first_projection_step_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : CutComponentHistory D Γ A b x u B state)
    (hn : ¬ IsProof Γ (.app (.lam A b) x))
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (R : ScopedStep (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.proj s 0 state.redex) out) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (.proj s 0 (proofErase Γ (b.inst x))) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) out shared := by
  cases R with
  | primitive RP =>
    obtain ⟨pivot, _, Rbefore, Rafter, HN⟩ := H.native_pivot_uniform heq hs hΓ hn HR
    obtain ⟨shared, RL, RR⟩ := native_pivot_expansion_square heq hs
      (.proj Rbefore) (.proj Rafter) (NativeOutputTransfer.proj_zero HN s)
      (ProofShape.BetaRed.proj (ProofShape.BetaRed.beta (A := state.1) (b := state.2.1) (a := state.2.2)))
      (static_structure_projection_primitive (fun h => h) RP)
    exact ⟨shared, RL, .beta RR⟩
  | proj RM =>
    obtain ⟨shared, RL, RR⟩ := H.step_square heq hs hΓ hn HR RM
    exact ⟨_, .proj RL, .proj RR⟩

/-- Arbitrarily many domain/body/argument rounds may precede the competing
step at this projection context. The initial native argument certificate is
used historically; no certificate for the computed argument is required. -/
theorem native_cut_first_projection_rounds_step_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.app (.lam A b) x))
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (RC : ReflTransGen (CutComponentRound D (proofEraseCtx Γ))
      (proofErase Γ A, proofErase (A :: Γ) b, proofErase Γ x) state)
    (R : ScopedStep (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.proj s 0 state.redex) out) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (.proj s 0 (proofErase Γ (b.inst x))) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) out shared :=
  ((CutComponentHistory.refl hA hb hx).rounds heq hs hΓ RC).first_projection_step_square
    heq hs hΓ hn HR R

end Lean4Lean.VEnv.Strengthening
