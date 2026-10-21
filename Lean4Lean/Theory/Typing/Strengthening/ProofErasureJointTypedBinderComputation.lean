import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointDomainPullback
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqNativeCarrierRecovery

/-! # Typed Pi inversion for the full joint union

Recoverable identity substitutions pull typed codomain paths back across
computed domains. This avoids unrestricted substitution of union primitives.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private beta_forallE_parts
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin
variable [Params]

/-- A typed union computation under a computed domain pulls back to the
original domain. Finite bounds on the two paths suffice independently. -/
theorem proofErase_joint_union_compute_domain_pullback
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs Γ B (.sort v))
    (RA : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ B))
    (he : env.HasType univs (B :: Γ) e T)
    (R : ScopedCompute (ErasedJointUnion D) (proofEraseCtx (B :: Γ))
      (proofErase (B :: Γ) e) out) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (B :: Γ) e) out := by
  obtain ⟨r, RA⟩ := RA.finite_stage erased_joint_stage_mono
  obtain ⟨s, R⟩ := R.finite_stage erased_joint_stage_mono
  exact (proofErase_joint_compute_domain_pullback heq hs hΓ hA hB RA he R).mono
    (fun H => ⟨r + s, H⟩)

/-- Typed Pi computation in the full union retains its body path in the
original context. Both initial components have actual typings; no primitive
substitution closure or recovery completeness is assumed. -/
theorem proofErase_joint_union_forallE_inv
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (hB : env.HasType univs (A :: Γ) B (.sort v))
    (EΔ : proofEraseCtx Γ = Δ)
    (R : ScopedCompute (ErasedJointUnion D) Δ
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) out) :
    ∃ A' B', out = .forallE A' B' ∧
      ScopedCompute (ErasedJointUnion D) Δ (proofErase Γ A) A' ∧
      ScopedCompute (ErasedJointUnion D) (proofErase Γ A :: Δ)
        (proofErase (A :: Γ) B) B' := by
  generalize E : ProofShape.forallE (proofErase Γ A) (proofErase (A :: Γ) B) = source at R
  induction R generalizing Γ A B u v with
  | base H => exact (E ▸ erased_joint_union_head H).elim
  | beta H =>
    cases E
    obtain ⟨A', B', HE, HA, HB⟩ := beta_forallE_parts H
    exact ⟨_, _, HE, .beta HA, .beta HB⟩
  | trans R₁ R₂ ih₁ ih₂ =>
    obtain ⟨A₁, B₁, rfl, RA, RB⟩ := ih₁ hΓ hA hB EΔ E
    obtain ⟨A₀, HA, EA⟩ := proofErase_scoped_compute_realize
      (erased_joint_union_descent heq hs) hΓ hA EΔ rfl RA
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    obtain ⟨B₀, HB, EB⟩ := proofErase_scoped_compute_realize
      (erased_joint_union_descent heq hs) hΓA hB
      (by simp only [proofEraseCtx, EΔ]) rfl RB
    have W : IsDefEqCtx env univs Γ (A :: Γ) (A₀ :: Γ) := .succ .zero HA
    have hB₀ := HB.hasType.2.defeqDFC henv W
    have EB₀ := (proofErase_defeqCtx hΓA W HB.hasType.2).symm.trans EB
    obtain ⟨A₂, B₂, HE, RA₂, RB₂⟩ := ih₂ hΓ HA.hasType.2 hB₀ EΔ
      (by rw [EA, EB₀])
    have RP : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
        (proofErase Γ A) (proofErase Γ A₀) := by simpa only [EΔ, EA] using RA
    have RB₂' : ScopedCompute (ErasedJointUnion D) (proofEraseCtx (A₀ :: Γ))
        (proofErase (A₀ :: Γ) B₀) B₂ := by simpa only [proofEraseCtx, EΔ] using RB₂
    have RPBody := proofErase_joint_union_compute_domain_pullback heq hs hΓ hA
      HA.hasType.2 RP hB₀ RB₂'
    refine ⟨_, _, HE, RA.trans (EA ▸ RA₂), RB.trans ?_⟩
    simpa only [proofEraseCtx, EΔ, EB₀] using RPBody
  | forallE RA RB => cases E; exact ⟨_, _, rfl, RA, RB⟩
  | app | proj | lam => cases E

end Lean4Lean.VEnv.Strengthening
