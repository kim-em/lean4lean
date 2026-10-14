import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSubstitutionImages

/-! # Realizing computed dependent substitution images

A finite typed source context suffices to reconstruct a typed substitution
from raw computational outputs. Proof-valued variables impose no raw agreement
condition; retained variables use typed replay at their source-substituted type.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Dropping the newest source variable drops the first erased image. Reflection
of proofness through ordinary weakening supplies the retained-variable test. -/
theorem ErasedSubstAgreement.tail (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (E : ErasedSubstAgreement (A :: Γ) Γ₀ σ ρ) :
    ErasedSubstAgreement Γ Γ₀ σ.tail (fun i => ρ (i + 1)) := by
  intro i B hl hn
  apply E (.succ hl)
  intro hp
  apply hn
  have H := isProof_liftN hΓA.1 hΓA Ctx.LiftN.one
    (show env.HasType univs Γ (.bvar i) B from .bvar hl)
  apply H.1
  simpa only [VExpr.liftN, liftVar, Nat.not_lt_zero, if_false, Nat.add_comm] using hp

/-- Raw computations of all images of a typed substitution admit a related
typed realization. The agreement ignores proof-valued source variables, so no
original representative of an arbitrary proof-marker image is required. -/
theorem proofErase_scoped_substitution_realize
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ ρ)
    (R : ∀ i, ProofShape.ScopedCompute Step (proofEraseCtx Γ₀) (ρ i) (τ i)) :
    ∃ σ', Ctx.SubstEq env univs Γ₀ σ σ' Γ ∧ ErasedSubstAgreement Γ Γ₀ σ' τ := by
  classical
  induction Γ generalizing σ ρ τ with
  | nil => exact ⟨σ, .nil, fun hl => nomatch hl⟩
  | cons A Γ ih =>
    have hΓA := W.wf
    cases W with
    | cons W hA hx =>
      obtain ⟨σ', HW, HE⟩ := ih W (E.tail hΓA) (fun i => R (i + 1))
      have HZ : ∃ z, env.IsDefEq univs Γ₀ σ.head z (A.subst σ.tail) ∧
          (¬ IsProof (A :: Γ) (.bvar 0) → proofErase Γ₀ z = τ 0) := by
        by_cases hp : IsProof (A :: Γ) (.bvar 0)
        · exact ⟨σ.head, hx, fun hn => (hn hp).elim⟩
        have RR : ProofShape.ScopedCompute Step (proofEraseCtx Γ₀) (proofErase Γ₀ σ.head) (τ 0) := by
          rw [show proofErase Γ₀ σ.head = ρ 0 from E Lookup.zero hp]
          exact R 0
        have WI : Ctx.LiftN 0 0 Γ₀ Γ₀ := .zero []
        obtain ⟨z, HZ, EZ⟩ := proofErase_scoped_compute_descend hstep hΓ₀ hΓ₀ WI hx.hasType.1
          rfl (by simpa only [ProofShape.liftN_zero] using RR)
        exact ⟨z, HZ, fun _ => by simpa only [ProofShape.liftN_zero] using EZ⟩
      obtain ⟨z, HZ, EZ⟩ := HZ
      refine ⟨σ'.cons z, .cons HW hA HZ, ?_⟩
      intro i B hl hn
      cases hl with
      | zero => exact EZ hn
      | succ hl =>
        apply HE hl
        intro hp
        exact hn (IsProof.lift' (Ctx.Lift'.skip .refl) hp)

namespace ProofShape
/-- A contextual substitution remains interpretable after pointwise scoped
computation. Each source realization constructs its own typed output map. -/
theorem ContextSubstitution.compute_images
    (hstep : ErasedScopedPrimitiveDescent Step) (W : ContextSubstitution Δ Δ' ρ)
    (R : ∀ i, ScopedCompute Step Δ' (ρ i) (τ i)) : ContextSubstitution Δ Δ' τ := by
  intro Γ hΓ EΓ
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, HW, HE⟩ := W hΓ EΓ
  obtain ⟨σ', HW', HE'⟩ := proofErase_scoped_substitution_realize hstep hΓ₀ HW HE
    (fun i => by simpa only [EΓ₀] using R i)
  exact ⟨Γ₀, σ', hΓ₀, EΓ₀, Model.SubstEq.right henv.orderedStrong hΓ₀ HW', HE'⟩
end ProofShape

end Lean4Lean.VEnv.Strengthening
