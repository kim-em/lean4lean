import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedValueChain
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRetainedArgumentOriginBoundary

/-! # Value histories survive the caller-eta forward-origin boundary

The checked caller-eta example rules out forward argument origins. It has a
scoped value chain, however, and that history survives arbitrary interpreted
substitution. This distinguishes the proposed history invariant from the
previously refuted one; it does not establish general rigid argument readout.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- The existing canonical-Eq caller-eta boundary has a substitution-stable
value history although no beta readout can supply a forward argument history. -/
theorem scoped_value_history_without_forward_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u))) :
    ∃ Γ x y, OnCtx Γ (env.IsType univs) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app (.bvar 0) x)) (proofErase Γ (.app (.bvar 0) y)) ∧
      ScopedValueChain D (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ y) ∧
      (∀ {Δ τ}, ContextSubstitution (proofEraseCtx Γ) Δ τ →
        ScopedValueChain D Δ ((proofErase Γ x).subst τ) ((proofErase Γ y).subst τ)) ∧
      ¬ ∃ arg, BetaRed (proofErase Γ (.app (.bvar 0) y)) (.app (.bvar 0) arg) ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
          (proofErase Γ x) arg := by
  obtain ⟨Γ, x, y, hΓ, hfx, hfy, RF, ⟨shared, RX, RY⟩, HN⟩ :=
    static_structure_retained_argument_origin_failure heq hs hi hp hx hz hS
  obtain ⟨A, B, _, hx⟩ := hfx.app_inv henv hΓ
  obtain ⟨A', B', _, hy⟩ := hfy.app_inv henv hΓ
  have HC := ScopedValueChain.of_join heq hs
    ⟨Γ, x, A, hΓ, rfl, hx, rfl⟩ ⟨Γ, y, A', hΓ, rfl, hy, rfl⟩ RX RY
  exact ⟨Γ, x, y, hΓ, RF, HC, fun W => HC.subst heq hs W, HN⟩

end Lean4Lean.VEnv.Strengthening
