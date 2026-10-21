import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecursiveRigid

/-! # Future carrier transport through recursive rigid changes

Target beta paths are matched on the source. Typed replay supplies residual
carrier and endpoint typings, and the ordinary simultaneous transport theorem
adapts the argument guards. Substitution preserves the raw type relation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

private theorem recursive_rigid_beta_readout
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (HE : env.IsDefEq univs Γ A B (.sort u))
    (HT : RigidTypeChange (proofErase Γ A) (proofErase Γ B))
    (H : BetaStableCarrier Step (proofEraseCtx Γ) (proofErase Γ A)
      (proofErase Γ a) (proofErase Γ b))
    (RB : ProofShape.BetaRed (proofErase Γ B) target)
    (RP : ProofShape.BetaRed (proofErase Γ a) p)
    (RQ : ProofShape.BetaRed (proofErase Γ b) q) :
    JointCarrierGuard Step (proofEraseCtx Γ) target p q := by
  obtain ⟨source, RA, HT'⟩ := HT.beta_target RB
  obtain ⟨A', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ HE.hasType.1 rfl rfl (.beta RA)
  obtain ⟨B', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ HE.hasType.2 rfl rfl (.beta RB)
  obtain ⟨a', HP, EP⟩ := proofErase_scoped_compute_realize hstep hΓ ha rfl rfl (.beta RP)
  obtain ⟨b', HQ, EQ⟩ := proofErase_scoped_compute_realize hstep hΓ hb rfl rfl (.beta RQ)
  have HE' := (HA.symm.trans HE).trans HB
  have HG := proofErase_joint_recursive_rigid_carrier hstep hsubst hhead hΓ
    (HA.defeq HP.hasType.2) (HA.defeq HQ.hasType.2) HE'.toU
    (by simpa only [EA, EB] using HT') (by simpa only [EA, EP, EQ] using H.1 RA RP RQ)
  simpa only [EB, EP, EQ] using HG

/-- Full future carrier guards survive recursive rigid changes of actually
equal types. The target need not be beta fixed: each target carrier path is
matched by a source path, and all endpoint paths keep their actual typings.
Arbitrary dependent unchanged subtrees and nested Pi changes are permitted. -/
theorem proofErase_future_recursive_rigid
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (HE : env.IsDefEq univs Γ A B (.sort u))
    (HT : RigidTypeChange (proofErase Γ A) (proofErase Γ B))
    (H : BetaStableCarrier Step (proofEraseCtx Γ) (proofErase Γ A)
      (proofErase Γ a) (proofErase Γ b)) :
    BetaStableCarrier Step (proofEraseCtx Γ) (proofErase Γ B)
      (proofErase Γ a) (proofErase Γ b) := by
  constructor
  · intro target p q RB RP RQ
    exact recursive_rigid_beta_readout hstep hhead hsubst hΓ ha hb HE HT H RB RP RQ
  · intro Δ' τ target p q W RB RP RQ
    have H' := H.subst W
    have HT' := HT.subst (σ := τ)
    obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
    have EA := proofErase_subst_with hΓ₀ WS HE.hasType.1 ES
    have EB := proofErase_subst_with hΓ₀ WS HE.hasType.2 ES
    have EP := proofErase_subst_with hΓ₀ WS ha ES
    have EQ := proofErase_subst_with hΓ₀ WS hb ES
    rw [← EA, ← EB] at HT'
    rw [← EA, ← EP, ← EQ, ← EΓ₀] at H'
    rw [← EB] at RB
    rw [← EP] at RP
    rw [← EQ] at RQ
    rw [← EΓ₀]
    exact recursive_rigid_beta_readout hstep hhead hsubst hΓ₀
      (ha.subst henv WS) (hb.subst henv WS) (HE.subst henv WS) HT' H' RB RP RQ

/-- Certified primitives discharge the recursive future-transport premises.
This retains the certified relation and assumes no whole-union substitution
or proposition beta principle. -/
theorem proofErase_certified_future_recursive_rigid
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (HE : env.IsDefEq univs Γ A B (.sort u))
    (HT : RigidTypeChange (proofErase Γ A) (proofErase Γ B))
    (H : BetaStableCarrier (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ A)
      (proofErase Γ a) (proofErase Γ b)) :
    BetaStableCarrier (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ B)
      (proofErase Γ a) (proofErase Γ b) :=
  proofErase_future_recursive_rigid (erased_beta_stable_joint_descent heq hs)
    erased_beta_stable_joint_head (erased_beta_stable_joint_subst heq hs) hΓ ha hb HE HT H

end Lean4Lean.VEnv.Strengthening
