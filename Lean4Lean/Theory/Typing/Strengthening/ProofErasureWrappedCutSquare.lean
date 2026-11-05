import Lean4Lean.Theory.Typing.Strengthening.ProofErasureWrappedCutDevelopment
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCutHistorySpineSquare
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedRawBetaJoin

/-! # Primitive and beta continuations after recursive wrapper developments

The selected pivot is reached throughout the development, so the final native
guards can fire there. Pending arguments may compute independently, and the
expanded branch may take an arbitrary beta continuation before the join.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private beta_spine from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCutHistorySpineSquare

private theorem nonopaque_spine (hH : ¬ PrimitiveHead e) (hS : ∀ u, e ≠ .sort u)
    (args : List ProofShape) : ¬ PrimitiveHead (ProofShape.mkApps e args) ∧
      (∀ u, ProofShape.mkApps e args ≠ .sort u) := by
  induction args using List.snoc_induction with
  | nil => exact ⟨hH, hS⟩
  | snoc args a ih =>
    rw [ProofShape.mkApps_snoc]
    exact ⟨ih.1, fun _ => ProofShape.noConfusion⟩

variable [Params] {D : PureObservation.Definitions}

/-- A final primitive at any surrounding application of the wrapped state
joins a reached pivot. Completed roots are already identical to their pivot;
active roots transfer every expansion guard. The primitive branch uses beta only. -/
theorem WrappedCut.Valid.spine_primitive_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : WrappedCut.Valid D Γ A b x u B s)
    (hn : ¬ IsProof Γ (.app (.lam A b) x))
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (Rbefore : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      original (ProofShape.mkApps (s.pivot Γ x) args))
    (RP : ErasedStaticStructureEtaExpansionUnion D (proofEraseCtx Γ)
      (ProofShape.mkApps s.source args) expanded) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      original shared ∧ ProofShape.BetaRed expanded shared := by
  rcases s.source_root_cases Γ x with E | ⟨hhead, hsort⟩
  · rw [E] at RP
    exact ⟨expanded, Rbefore.trans (.base RP), .refl⟩
  · obtain ⟨hhead, hsort⟩ := nonopaque_spine hhead hsort args
    exact native_pivot_primitive_square heq hs hhead hsort Rbefore
      ((H.compute_readout heq hs hΓ hn HR).mkApps (List.Forall₂.rfl (fun _ _ => .refl)))
      ((H.native heq hs hΓ hn HR).mkApps args) (beta_spine s.beta_readout args) RP

/-- Finite wrapper developments, pending-argument computation, one arbitrary
full-union primitive and an arbitrary beta continuation join the original
contractum. Eta and structure expansion are permitted at the final primitive.
This does not yet permit unrestricted full-union continuation after those two
shape changes, or arbitrary computation of literal wrapper control functions. -/
theorem native_cut_wrapper_development_primitive_beta_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.app (.lam A b) x))
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (R : ReflTransGen (WrappedCutStep D Γ A b x u B)
      (.cut (proofErase Γ A, proofErase (A :: Γ) b, proofErase Γ x) b) t)
    (RA : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)) args₀ args)
    (RP : ErasedStaticStructureEtaExpansionUnion D (proofEraseCtx Γ)
      (ProofShape.mkApps t.source args) expanded)
    (RB : ProofShape.BetaRed expanded out) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (ProofShape.mkApps (proofErase Γ (b.inst x)) args₀) shared ∧ ProofShape.BetaRed out shared := by
  obtain ⟨H, _, Rbefore⟩ := wrapped_cut_steps_simulate heq hs hΓ hn HR R
    (.cut (CutPivotHistory.refl hA hb hx))
  obtain ⟨shared, RL, RR⟩ := H.spine_primitive_square heq hs hΓ hn HR (Rbefore.mkApps RA) RP
  obtain ⟨shared', RO, RL'⟩ := RB.raw_confluent RR
  exact ⟨shared', RL.trans (.beta RL'), RO⟩

end Lean4Lean.VEnv.Strengthening
