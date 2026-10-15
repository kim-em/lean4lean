import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedJoinedApplication

/-! # Eta function guards with independently compared arguments

The long application contracts before argument comparison. This avoids both
comparison composition and paired substitution into arbitrary lambda bodies.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Displayed eta-related functions apply to distinct commonly compared
arguments at the same stage. The long application beta-contracts to the same
short function used by the other side. -/
theorem proofErase_scoped_apply_eta_independent
    (hstep : ErasedScopedPrimitiveDescent Step) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HF : ProofShape.EtaHead (proofErase Γ f) (proofErase Γ g))
    (HX : ProofShape.ScopedCompare Step (proofEraseCtx Γ) true (proofErase Γ x) (proofErase Γ y)) :
    ProofShape.ScopedCompare Step (proofEraseCtx Γ) mode
      (proofErase Γ (.app f x)) (proofErase Γ (.app g y)) :=
  .compute (.beta (proofErase_raw_apply_eta_beta hΓ hf hg hx HF)) .refl
    (proofErase_scoped_apply_independent hstep hΓ hg hg hx hy .refl HX)

/-- Finite computations before displayed eta also accept distinct compared
arguments. Function replay retains the original Pi type; neither argument needs
a common reduct with the other. -/
theorem proofErase_scoped_apply_computed_eta_independent
    (hstep : ErasedScopedPrimitiveDescent Step) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (RF : ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ f) f')
    (RG : ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ g) g')
    (HF : ProofShape.EtaHead f' g')
    (HX : ProofShape.ScopedCompare Step (proofEraseCtx Γ) true (proofErase Γ x) (proofErase Γ y)) :
    ProofShape.ScopedCompare Step (proofEraseCtx Γ) mode
      (proofErase Γ (.app f x)) (proofErase Γ (.app g y)) := by
  have W : Ctx.LiftN 0 0 Γ Γ := .zero []
  obtain ⟨f₀, HF₀, EF⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ W hf rfl
    (by simpa only [ProofShape.liftN_zero] using RF)
  obtain ⟨g₀, HG₀, EG⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ W hg rfl
    (by simpa only [ProofShape.liftN_zero] using RG)
  simp only [ProofShape.liftN_zero] at EF EG
  exact .compute
    (proofErase_scoped_compute_apply_same hΓ hf HF₀.hasType.2 hx (by rwa [EF]))
    (proofErase_scoped_compute_apply_same hΓ hg HG₀.hasType.2 hy (by rwa [EG]))
    (proofErase_scoped_apply_eta_independent hstep hΓ HF₀.hasType.2 HG₀.hasType.2 hx hy
      (by rwa [EF, EG]) HX)

end Lean4Lean.VEnv.Strengthening
