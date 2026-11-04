import Lean4Lean.Theory.Typing.Strengthening.NeutralRecoveringImage

/-! # Contracting lambda paths while carrying converted image recovery

The induction follows the actual lambda computation. At each intermediate
annotation it carries the image's converted recovery forward, then substitutes
the next body path in that annotation's own context. No backward binder-context
transport or arbitrary primitive substitution is required.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- A typed lambda computation contracts at a converted recoverable argument.
The output stays lambda-shaped, its body instantiates exactly, and its new
annotation retains the image criterion for subsequent computation or checking. -/
theorem proofErase_computed_union_lam_compute_inst_converted
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (R : ScopedCompute (ErasedComputedJointUnion D) Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hn : ¬ IsProof Γ (.lam A b))
    (hp : env.HasType univs Γ p A)
    (HI : NeutralRecoveringImage D Γ p (proofErase Γ A))
    (EΓ : proofEraseCtx Γ = Δ)
    (E : ProofShape.lam (proofErase Γ A) (proofErase (A :: Γ) b) = source) :
    ∃ A' b', out = .lam A' b' ∧ NeutralRecoveringImage D Γ p A' ∧
      ScopedCompute (ErasedComputedJointUnion D) Δ
        ((proofErase (A :: Γ) b).inst (proofErase Γ p)) (b'.inst (proofErase Γ p)) := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedComputedJointUnion D) :=
    erased_computed_joint_union_descent heq hs
  induction R generalizing Γ A u b B p with
  | base H => exact (E ▸ erased_computed_joint_union_head H).elim
  | beta H =>
    cases E
    obtain ⟨A', b', HE, HA, HB⟩ := H.lam_inv
    refine ⟨A', b', HE, HI.compute heq hs hΓ hp (by simpa only [EΓ] using ScopedCompute.beta HA), ?_⟩
    exact .beta (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
      (HB.subst (σ := ProofShape.Subst.one (proofErase Γ p))))
  | trans R₁ R₂ ih₁ ih₂ =>
    obtain ⟨A₁, b₁, rfl, HI₁, RB₁⟩ := ih₁ hΓ hA hb hn hp HI EΓ E
    have Ef := (show proofErase Γ (.lam A b) = .lam _ _ from if_neg hn).trans E
    obtain ⟨f₁, HF, EF⟩ := proofErase_scoped_compute_realize hstep hΓ (HasType.lam hA hb) EΓ Ef R₁
    obtain ⟨A₀, b₀, rfl, hn₀, EA₀, Eb₀⟩ := erase_lam_inv EF
    obtain ⟨⟨v, hA₀⟩, C₀, hb₀⟩ := HF.hasType.2.lam_inv henv hΓ
    have hp₀ := argument_at_displayed_domain hΓ HF.hasType.2 (HasType.lam hA₀ hb₀) hp
    obtain ⟨A₂, b₂, HE, HI₂, RB₂⟩ := ih₂ hΓ hA₀ hb₀ hn₀ hp₀ (EA₀.symm ▸ HI₁) EΓ
      (by rw [EA₀, Eb₀])
    exact ⟨A₂, b₂, HE, HI₂, RB₁.trans (by simpa only [Eb₀] using RB₂)⟩
  | lam RA RB =>
    cases E
    refine ⟨_, _, rfl, HI.compute heq hs hΓ hp (by simpa only [EΓ] using RA), ?_⟩
    have HC := HI.compute_inst heq hs hΓ hp hb (by simpa only [proofEraseCtx, EΓ] using RB)
    simpa only [EΓ] using HC
  | app | proj | forallE => cases E

end Lean4Lean.VEnv.Strengthening
