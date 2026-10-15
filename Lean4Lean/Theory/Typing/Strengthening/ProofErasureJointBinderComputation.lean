import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointDomainPullback
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUnion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBinderComputation

/-! # Inverting joint computation beneath changing lambda annotations

Typed replay realizes intermediate lambdas. Contravariant domain transport
then returns their body paths to the initial binder context. Stage bounds may
grow; neither joint confluence nor arbitrary substitution closure is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

private theorem union_domain_pullback
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs Γ B (.sort v))
    (RA : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ B))
    (he : env.HasType univs (B :: Γ) e T)
    (R : ScopedCompute (ErasedJointUnion D) (proofEraseCtx (B :: Γ)) (proofErase (B :: Γ) e) out) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx (A :: Γ)) (proofErase (B :: Γ) e) out := by
  obtain ⟨domainStage, RA⟩ := RA.finite_stage erased_joint_stage_mono
  obtain ⟨stage, R⟩ := R.finite_stage erased_joint_stage_mono
  exact (proofErase_joint_compute_domain_pullback heq hs hΓ hA hB RA he R).mono
    (fun H => ⟨_, H⟩)

private theorem lam_inv_aux
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (R : ScopedCompute (ErasedJointUnion D) Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hn : ¬ IsProof Γ (.lam A b))
    (EΓ : proofEraseCtx Γ = Δ)
    (E : ProofShape.lam (proofErase Γ A) (proofErase (A :: Γ) b) = source) :
    ∃ A' b', out = .lam A' b' ∧
      ScopedCompute (ErasedJointUnion D) Δ (proofErase Γ A) A' ∧
      ScopedCompute (ErasedJointUnion D) (proofEraseCtx (A :: Γ))
        (proofErase (A :: Γ) b) b' := by
  induction R generalizing Γ A u b B with
  | base H => exact (E ▸ erased_joint_union_head H).elim
  | beta H =>
    cases E
    obtain ⟨A', b', HE, HA, HB⟩ := H.lam_inv
    exact ⟨_, _, HE, .beta HA, .beta HB⟩
  | trans R₁ R₂ ih₁ ih₂ =>
    obtain ⟨A₁, b₁, rfl, RA, RB⟩ := ih₁ hΓ hA hb hn EΓ E
    have Ef := (show proofErase Γ (.lam A b) = .lam _ _ from if_neg hn).trans E
    have WI : Ctx.LiftN 0 0 Γ Γ := .zero []
    obtain ⟨f₁, HF, EF⟩ := proofErase_scoped_compute_descend
      (erased_joint_union_descent heq hs) hΓ hΓ WI (HasType.lam hA hb) EΓ
      (by simpa only [ProofShape.liftN_zero, Ef] using R₁)
    simp only [ProofShape.liftN_zero] at EF
    obtain ⟨A₀, b₀, rfl, hn₀, EA₀, Eb₀⟩ := erase_lam_inv EF
    obtain ⟨⟨v, hA₀⟩, C₀, hb₀⟩ := HF.hasType.2.lam_inv henv hΓ
    obtain ⟨A₂, b₂, HE, RA₂, RB₂⟩ := ih₂ hΓ hA₀ hb₀ hn₀ EΓ
      (by rw [EA₀, Eb₀])
    have RA₀ : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
        (proofErase Γ A) (proofErase Γ A₀) := by simpa only [EΓ, EA₀] using RA
    have RB₂' := union_domain_pullback heq hs hΓ hA hA₀ RA₀ hb₀ RB₂
    refine ⟨_, _, HE, RA.trans (EA₀ ▸ RA₂), RB.trans ?_⟩
    simpa only [Eb₀] using RB₂'
  | lam RA RB =>
    cases E
    exact ⟨_, _, rfl, RA, by simpa only [proofEraseCtx, EΓ] using RB⟩
  | app | proj | forallE => cases E

/-- Finite joint computation of a typed non-proof lambda has a lambda output
and separate annotation/body paths in some finite later stage. The body path
uses the original binder, despite all intermediate annotation changes. -/
theorem proofErase_joint_lam_inv_later
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hn : ¬ IsProof Γ (.lam A b))
    (R : ScopedCompute (ErasedJointStage D stage) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) out) :
    ∃ later A' b', stage ≤ later ∧ out = .lam A' b' ∧
      ScopedCompute (ErasedJointStage D later) (proofEraseCtx Γ) (proofErase Γ A) A' ∧
      ScopedCompute (ErasedJointStage D later) (proofEraseCtx (A :: Γ))
        (proofErase (A :: Γ) b) b' := by
  obtain ⟨A', b', HE, RA, RB⟩ := lam_inv_aux heq hs (R.mono (fun H => ⟨stage, H⟩))
    hΓ hA hb hn rfl rfl
  obtain ⟨n, RA⟩ := RA.finite_stage erased_joint_stage_mono
  obtain ⟨m, RB⟩ := RB.finite_stage erased_joint_stage_mono
  refine ⟨max stage (max n m), A', b', Nat.le_max_left _ _, HE, ?_, ?_⟩
  · exact RA.mono (erased_joint_stage_mono (by omega))
  · exact RB.mono (erased_joint_stage_mono (by omega))

end Lean4Lean.VEnv.Strengthening
