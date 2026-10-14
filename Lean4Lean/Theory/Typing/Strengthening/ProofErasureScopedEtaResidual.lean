import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedBinderComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaClassification

/-! # Residual eta guards after computation of the expanded lambda

Recursive scoped eta can retain the computed opened body directly. Lambda
inversion and context conversion suffice; reflecting the computation into the
short function or assuming computational confluence is unnecessary.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

namespace ProofShape
/-- Computing an eta-expanded lambda preserves a common comparison with its
unchanged short function. The domain-sort witness is sufficient even when no
original representatives of the raw body or short function are supplied. -/
theorem ScopedCompute.eta_residual
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hroot : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (HS : DomainSort Δ A u)
    (R : ScopedCompute Step Δ (.lam A (.app (f.liftN 1) (etaArgument u))) out) :
    ScopedCompare Step Δ true out f := by
  obtain ⟨Γ, A₀, hΓ, rfl, hA, rfl⟩ := HS
  obtain ⟨A', body', rfl, RA, RB⟩ := R.lam_inv_typed hstep hsubst hroot hΓ hA rfl
  have WI : Ctx.LiftN 0 0 Γ Γ := .zero []
  obtain ⟨A₁, HA, EA⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ WI hA rfl
    (by simpa only [liftN_zero] using RA)
  simp only [liftN_zero] at EA
  have HC : IsDefEqCtx env univs Γ (A₀ :: Γ) (A₁ :: Γ) := .succ .zero HA
  have RB' := (show ScopedCompute Step (proofEraseCtx (A₀ :: Γ))
    (.app (f.liftN 1) (etaArgument u)) body' from RB).defeqCtx hsubst hΓ HC
  have HS' : DomainSort (proofEraseCtx Γ) A' u := EA ▸ DomainSort.of_typed hΓ HA.hasType.2
  apply ScopedCompare.etaBodyL HS'
  apply ScopedCompare.compute .refl (show ScopedCompute Step (A' :: proofEraseCtx Γ)
    (.app (f.liftN 1) (etaArgument u)) body' from by
      simpa only [proofEraseCtx, EA] using RB')
  exact .refl
end ProofShape

/-- A typed displayed eta guard survives arbitrary finite scoped computation
of its expanded endpoint. Typing classifies the fresh argument exactly. -/
theorem proofErase_scoped_eta_head_left
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hroot : ∀ {Δ a b}, Step Δ a b → ProofShape.PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs Γ e T) (hf : env.HasType univs Γ f T)
    (H : ProofShape.EtaHead (proofErase Γ e) (proofErase Γ f))
    (R : ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ e) out) :
    ProofShape.ScopedCompare Step (proofEraseCtx Γ) true out (proofErase Γ f) := by
  obtain ⟨A, B, u, hA, _, _, E⟩ := proofErase_eta_head_classified hΓ he hf H
  exact (E ▸ R).eta_residual hstep hsubst hroot (.of_typed hΓ hA)

/-- Eta residuals stay in the same finite contextual prefix stage, including
when the expanded body or its annotation contains prefix computations. -/
theorem proofErase_scoped_prefix_eta_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HS : ProofShape.DomainSort Δ A u)
    (R : ProofShape.ScopedCompute (ErasedScopedPrefixStage D stage) Δ
      (.lam A (.app (f.liftN 1) (ProofShape.etaArgument u))) out) :
    ProofShape.ScopedCompare (ErasedScopedPrefixStage D stage) Δ true out f :=
  R.eta_residual (erased_scoped_prefix_stage_descent heq hs stage)
    (erased_scoped_prefix_stage_subst stage) (erased_scoped_prefix_stage_head stage) HS

end Lean4Lean.VEnv.Strengthening
