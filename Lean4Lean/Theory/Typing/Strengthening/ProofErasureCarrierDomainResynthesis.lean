import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierApplication

/-! # The coupled re-synthesis obligation for application substitution

Exact chosen-type recovery is not stable under arbitrary typed substitution.
The application rule needs some recovered Pi whose domain supports the
substituted argument comparison. This file names that obligation and checks
its use for application substitution. `ProofErasureCarrierResynthesisBoundary`
refutes it for ordinary-core recovery, independently of comparison strength.
Higher and finite-stage variants remain open; none is claimed strictly smaller
than the proposition front.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Missing joint re-synthesis law. A typed substitution may change both the
recovered domain and codomain; the resulting argument guard must use the new
domain. Ordinary-core recovery is refuted in
`ProofErasureCarrierResynthesisBoundary`; higher stages remain unproved. This
law neither requires nor asserts exact preservation of the selected type. -/
def CarrierDomainResynthesis
    (Recovery : ProofShape → ProofShape → Prop)
    (Step : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ Γ₀ σ f x y D C A B}, OnCtx Γ₀ (env.IsType univs) →
    Ctx.SubstEq env univs Γ₀ σ σ Γ →
    env.HasType univs Γ f (.forallE D C) →
    env.HasType univs Γ x D → env.HasType univs Γ y D →
    ProofShape.TypeRecovery Recovery (ProofShape.contextOracle (proofEraseCtx Γ))
      (proofErase Γ f) (.forallE A B) →
    ProofShape.StructureCarrierGuard Step (proofEraseCtx Γ) A (proofErase Γ x) (proofErase Γ y) →
    ∃ A' B', ProofShape.TypeRecovery Recovery (ProofShape.contextOracle (proofEraseCtx Γ₀))
      (proofErase Γ₀ (f.subst σ)) (.forallE A' B') ∧
      ProofShape.StructureCarrierGuard Step (proofEraseCtx Γ₀) A'
        (proofErase Γ₀ (x.subst σ)) (proofErase Γ₀ (y.subst σ))

/-- Joint domain/guard re-synthesis supplies typed substitution of the
application root. Function comparison transports independently. This theorem
does not assume that either recovered output equals its substituted old value. -/
theorem proofErase_carrier_application_subst_of_resynthesis
    (hres : CarrierDomainResynthesis Recovery Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (hf : env.HasType univs Γ f (.forallE D C)) (hg : env.HasType univs Γ g (.forallE D C))
    (hx : env.HasType univs Γ x D) (hy : env.HasType univs Γ y D)
    (hnl : ¬ IsProof Γ (.app f x)) (hnr : ¬ IsProof Γ (.app g y))
    (R : ProofShape.TypeRecovery Recovery (ProofShape.contextOracle (proofEraseCtx Γ))
      (proofErase Γ f) (.forallE A B))
    (HF : ProofShape.ScopedCompare Step (proofEraseCtx Γ) false (proofErase Γ f) (proofErase Γ g))
    (HX : ProofShape.StructureCarrierGuard Step (proofEraseCtx Γ) A (proofErase Γ x) (proofErase Γ y)) :
    ProofShape.RecoveredCarrierApplication Recovery Step (proofEraseCtx Γ₀)
      (proofErase Γ₀ ((VExpr.app f x).subst σ)) (proofErase Γ₀ ((VExpr.app g y).subst σ)) := by
  obtain ⟨A', B', R', HX'⟩ := hres hΓ₀ W hf hx hy R HX
  have HF' := proofErase_scoped_compare_subst hsubst hΓ₀ W hf hg HF
  have hnl' := mt (isProof_subst hΓ₀ W (hf.app hx)).1 hnl
  have hnr' := mt (isProof_subst hΓ₀ W (hg.app hy)).1 hnr
  rw [show proofErase Γ₀ ((VExpr.app f x).subst σ) = .app _ _ from if_neg hnl',
    show proofErase Γ₀ ((VExpr.app g y).subst σ) = .app _ _ from if_neg hnr']
  exact .app R' HF' HX'

end Lean4Lean.VEnv.Strengthening
