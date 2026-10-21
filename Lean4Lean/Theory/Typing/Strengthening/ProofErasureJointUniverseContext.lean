import Lean4Lean.Theory.Typing.Strengthening.ProofErasureUniverseOracleRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointTransport

/-! # Typed checking through a binder change to a universe

The existing shared checking induction is instantiated with equal-context
interpretations and universe-changing type oracles. Typed recovery preserves
application domains even though recovered universe levels may change.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

private structure UniverseContext (Δ Δ' : List ProofShape) : Prop where
  interpretation : ∀ {Γ}, OnCtx Γ (env.IsType univs) → proofEraseCtx Γ = Δ →
    ∃ Γ', OnCtx Γ' (env.IsType univs) ∧ proofEraseCtx Γ' = Δ' ∧ IsDefEqCtx env univs [] Γ Γ'
  lookup : ∀ i, UniverseResultChange (contextOracle Δ i) (contextOracle Δ' i)

private theorem UniverseContext.of_defeqCtx
    (hΓ : OnCtx Γ (env.IsType univs)) (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : ∀ i, UniverseResultChange (contextOracle (proofEraseCtx Γ) i)
      (contextOracle (proofEraseCtx Γ') i)) : UniverseContext (proofEraseCtx Γ) (proofEraseCtx Γ') := by
  refine ⟨?_, HO⟩
  intro Γ₀ hΓ₀ EΓ₀
  exact ⟨Γ', (W.symm henv.ordered).isType, rfl, (proofEraseCtx_defeq hΓ₀ hΓ EΓ₀).trans_empty henv W⟩

private theorem UniverseContext.cons (W : UniverseContext Δ Δ') :
    UniverseContext (A :: Δ) (A :: Δ') := by
  constructor
  · intro Γ hΓ EΓ
    cases Γ with
    | nil => cases EΓ
    | cons D Γ =>
      obtain ⟨ED, EΓ⟩ := List.cons.inj EΓ
      obtain ⟨hΓ, u, hD⟩ := hΓ
      obtain ⟨Γ', hΓ', EΓ', HC⟩ := W.interpretation hΓ EΓ
      have ED' := (proofErase_defeqCtx hΓ HC hD).symm.trans ED
      exact ⟨D :: Γ', ⟨hΓ', u, hD.defeqDFC henv HC⟩,
        by simp only [proofEraseCtx, ED', EΓ'], .succ HC hD⟩
  · intro i
    cases i with
    | zero => exact .refl
    | succ i => exact (W.lookup i).liftN

private theorem UniverseContext.interprets (W : UniverseContext Δ Δ') :
    ContextSubstitution Δ Δ' ProofShape.Subst.id := by
  intro Γ hΓ EΓ
  obtain ⟨Γ', hΓ', EΓ', HC⟩ := W.interpretation hΓ EΓ
  have H := (ContextSubstitution.of_defeqCtx (by trivial) HC) hΓ rfl
  simpa only [EΓ, EΓ'] using H

private def UniverseTransport (Δ Δ' : List ProofShape) (τ : ProofShape.Subst) : Prop :=
  τ = ProofShape.Subst.id ∧ UniverseContext Δ Δ'

private theorem joint_universe_transport
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (H : JointCheck Step Δ kind sa sb) : JointTransportResult UniverseTransport Step Δ kind sa sb := by
  apply H.transport UniverseTransport hstep
  · intro Δ Δ' τ A WT
    obtain ⟨rfl, W⟩ := WT
    have Eid : ProofShape.Subst.id.lift = ProofShape.Subst.id := by
      funext i
      cases i <;> simp [ProofShape.Subst.lift, ProofShape.Subst.id, ProofShape.liftN]
    exact ⟨Eid, by simpa only [ProofShape.subst_id] using W.cons (A := A)⟩
  · intro Δ Δ' τ A u WT HS
    obtain ⟨rfl, W⟩ := WT
    exact ContextSubstitution.sort W.interprets HS
  · intro Γ Δ Δ' τ e T source out R hΓ ht EΓ Ee WT
    obtain ⟨rfl, W⟩ := WT
    obtain ⟨Γ', hΓ', EΓ', HC⟩ := W.interpretation hΓ EΓ
    have R' := (EΓ ▸ R).defeqCtx hsubst (by trivial) HC
    simpa only [ProofShape.subst_id, EΓ'] using R'
  · intro Γ Δ' τ f x y D C A B hΓ hf hx hy R HG WT HG'
    obtain ⟨rfl, W⟩ := WT
    obtain ⟨Γ', hΓ', EΓ', HC⟩ := W.interpretation hΓ rfl
    obtain ⟨B', R'⟩ := proofErase_recovery_universe_oracles_pi hstep hhead hsubst hΓ hf HC
      (by simpa only [EΓ'] using W.lookup) R
    exact ⟨A, B', by simpa only [ProofShape.subst_id, EΓ'] using R', by simpa only [ProofShape.subst_id] using HG'⟩

/-- Replacing an actual binder type by an equal literal sort preserves both
typed joint modes. Recovered universe levels may change, but each application
keeps the exact domain needed by its recursively transported argument guard. -/
theorem proofErase_joint_universe_binder
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (HE : env.IsDefEq univs Γ A (.sort v) (.sort u))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T) :
    (JointCompare Step (proofEraseCtx (A :: Γ)) mode
        (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) →
      JointCompare Step (proofEraseCtx (.sort v :: Γ)) mode
        (proofErase (.sort v :: Γ) a) (proofErase (.sort v :: Γ) b)) ∧
    (JointCarrierGuard Step (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) T)
        (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) →
      JointCarrierGuard Step (proofEraseCtx (.sort v :: Γ)) (proofErase (.sort v :: Γ) T)
        (proofErase (.sort v :: Γ) a) (proofErase (.sort v :: Γ) b)) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HE.hasType.1⟩
  have W : IsDefEqCtx env univs [] (A :: Γ) (.sort v :: Γ) := .succ (.refl hΓ) HE
  have HO : ∀ i, UniverseResultChange (contextOracle (proofEraseCtx (A :: Γ)) i)
      (contextOracle (proofEraseCtx (.sort v :: Γ)) i) := by
    intro i
    cases i with
    | zero =>
      change UniverseResultChange ((proofErase Γ A).liftN 1) ((proofErase Γ (.sort v)).liftN 1)
      rw [show proofErase Γ (.sort v) = .sort v from if_neg (not_isProof_of_sort hΓ HE.hasType.2)]
      exact .toSort
    | succ i => exact .refl
  have WT : UniverseTransport (proofEraseCtx (A :: Γ)) (proofEraseCtx (.sort v :: Γ))
      ProofShape.Subst.id := ⟨rfl, UniverseContext.of_defeqCtx hΓA W HO⟩
  constructor
  · intro H
    have H' := joint_universe_transport hstep hhead hsubst H hΓA ha hb rfl rfl rfl WT
    simp only [ProofShape.subst_id] at H'
    rwa [proofErase_defeqCtx hΓA W ha, proofErase_defeqCtx hΓA W hb] at H'
  · intro H
    have H' := joint_universe_transport hstep hhead hsubst H hΓA ha hb rfl rfl rfl rfl WT
    simp only [ProofShape.subst_id] at H'
    rwa [proofErase_defeqCtx hΓA W (ha.isType henv hΓA).choose_spec,
      proofErase_defeqCtx hΓA W ha, proofErase_defeqCtx hΓA W hb] at H'

/-- Certified primitives discharge all universe-binder transport premises. -/
theorem proofErase_certified_universe_binder
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HE : env.IsDefEq univs Γ A (.sort v) (.sort u))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T) :
    (JointCompare (ErasedBetaStableJoint D) (proofEraseCtx (A :: Γ)) mode
        (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) →
      JointCompare (ErasedBetaStableJoint D) (proofEraseCtx (.sort v :: Γ)) mode
        (proofErase (.sort v :: Γ) a) (proofErase (.sort v :: Γ) b)) ∧
    (JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) T)
        (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) →
      JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx (.sort v :: Γ))
        (proofErase (.sort v :: Γ) T)
        (proofErase (.sort v :: Γ) a) (proofErase (.sort v :: Γ) b)) :=
  proofErase_joint_universe_binder (erased_beta_stable_joint_descent heq hs)
    erased_beta_stable_joint_head (erased_beta_stable_joint_subst heq hs) hΓ HE ha hb

end Lean4Lean.VEnv.Strengthening
