import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextualCastGuard

/-! # Actual context interpretation after full-core binder computation

A context realization supplies the domain typing needed for core replay.
Replaying the domain constructs an identity substitution into the changed
context, without any inverse weakening or arbitrary comparison transport.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Every realized sort witness survives ordinary full-core computation. -/
theorem ProofShape.DomainSort.level_core (hs : D.Sound env univs)
    (S : DomainSort Δ A u) (R : ProofShape.Compute (ErasedLevelCore D) A A') :
    DomainSort Δ A' u := by
  obtain ⟨Γ, X, hΓ, EΓ, hX, EX⟩ := S
  obtain ⟨Y, HY, EY⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ hX EΓ EX (R.scoped (fun H => .base H))
  exact ⟨Γ, Y, hΓ, EΓ, HY.hasType.2, EY⟩

/-- Full-core computation of a binder domain interprets the identity map from
the original raw context into the new one. Only actual source realizations need
a domain typing, and forward replay constructs the required target realization. -/
theorem ProofShape.ContextSubstitution.core_binder (hs : D.Sound env univs)
    (R : ProofShape.Compute (ErasedLevelCore D) A A') :
    ContextSubstitution (A :: Δ) (A' :: Δ) ProofShape.Subst.id := by
  intro Γ hΓ EΓ
  cases Γ with
  | nil => cases EΓ
  | cons B Γ =>
    obtain ⟨hΓ, u, hB⟩ := hΓ
    obtain ⟨EB, EΓ⟩ := List.cons.inj EΓ
    obtain ⟨B', HB, EB'⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
      hΓ hB rfl EB (R.scoped (fun H => .base H))
    have W : ContextSubstitution (proofEraseCtx (B :: Γ)) (proofEraseCtx (B' :: Γ)) ProofShape.Subst.id :=
      ContextSubstitution.of_defeqCtx hΓ (.succ .zero HB)
    have H := W (Γ := B :: Γ) ⟨hΓ, u, hB⟩ rfl
    simpa only [proofEraseCtx, EB', EΓ] using H

end Lean4Lean.VEnv.Strengthening
