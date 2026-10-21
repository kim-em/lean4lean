import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralOracleRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCertifiedChecking

/-! # Joint checking through neutral changes to context type oracles

Recovery outputs may change at protected neutral results. Every application
still recovers the same domain, so its recursive carrier check is reusable.
This transports the full joint judgment, including nested carrier guards.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private oracle_cons_change compute_context
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralOracleRecovery
open private identity_cons
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointOracleBetaTransport
variable [Params]

private theorem sort_context (W : ContextSubstitution Δ Δ' ProofShape.Subst.id)
    (S : DomainSort Δ A u) : DomainSort Δ' A u := by
  simpa only [ProofShape.subst_id] using W.sort S

/-- Full joint checking survives interpreted context changes whose oracle
entries differ only at protected neutral results. Both endpoints and the
carrier, if present, stay exact. Application recovery may choose a different
codomain, but its domain is unchanged. Primitive substitution is the only
closure premise; neither comparison completeness nor a beta law is assumed. -/
theorem ProofShape.JointCheck.neutral_oracle
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (H : JointCheck Step Δ kind a b)
    (W : ContextSubstitution Δ Δ' ProofShape.Subst.id)
    (HO : ∀ i, NeutralResultChange k (contextOracle Δ i) (contextOracle Δ' i)) :
    JointCheck Step Δ' kind a b := by
  induction H generalizing Δ' k with
  | leaf H => exact .leaf H
  | app HF HX ihf ihx => exact .app (ihf W HO) (ihx W HO)
  | appCarrier R HF HX ihf ihx =>
    obtain ⟨T', R', HT⟩ := R.neutral_oracle hhead hsubst W HO
    obtain ⟨B', rfl, _⟩ := HT.forallE_inv
    exact .appCarrier R' (ihf W HO) (ihx W HO)
  | proj H ih => exact .proj (ih W HO)
  | lam HA HB ihA ihB =>
    exact .lam (ihA W HO) (ihB (identity_cons W) (oracle_cons_change HO))
  | forallE HA HB ihA ihB =>
    exact .forallE (ihA W HO) (ihB (identity_cons W) (oracle_cons_change HO))
  | lamSorted SA SA' HA HB ihA ihB =>
    exact .lamSorted (sort_context W SA) (sort_context W SA') (ihA W HO)
      (ihB (identity_cons W) (oracle_cons_change HO))
  | forallSorted SA SA' HA SB SB' HB ihA ihB =>
    exact .forallSorted (sort_context W SA) (sort_context W SA') (ihA W HO)
      (sort_context (identity_cons W) SB) (sort_context (identity_cons W) SB')
      (ihB (identity_cons W) (oracle_cons_change HO))
  | lamCommon H ih => exact .lamCommon (ih (identity_cons W) (oracle_cons_change HO))
  | etaBodyL S H ih =>
    exact .etaBodyL (sort_context W S) (ih (identity_cons W) (oracle_cons_change HO))
  | etaBodyR S H ih =>
    exact .etaBodyR (sort_context W S) (ih (identity_cons W) (oracle_cons_change HO))
  | structFields hi hx hp hf hadm HF ih =>
    exact .structFields hi hx hp hf hadm (fun i hj hn => ih i hj hn W HO)
  | etaLams H HE ih => exact .etaLams (ih W HO) HE
  | compute RA RB H ih =>
    exact .compute (compute_context hsubst W RA) (compute_context hsubst W RB) (ih W HO)
  | symm H ih => exact .symm (ih W HO)
  | carrierIntro hi hx hp hadm HF ih =>
    exact .carrierIntro hi hx hp hadm (fun i hj hn => ih i hj hn W HO)
  | carrierChecked H ih => exact .carrierChecked (ih W HO)
  | carrierSubsingleton H => exact .carrierSubsingleton H
  | carrierFunction S H ih =>
    exact .carrierFunction (sort_context W S) (ih (identity_cons W) (oracle_cons_change HO))
  | carrierSymm H ih => exact .carrierSymm (ih W HO)
  | carrierCompute R H ih => exact .carrierCompute (compute_context hsubst W R) (ih W HO)
  | carrierReduce RA RB H ih =>
    exact .carrierReduce (compute_context hsubst W RA) (compute_context hsubst W RB) (ih W HO)
  | carrierNested hi hx hp hadm HT HF ih =>
    exact .carrierNested hi hx hp hadm HT (fun i hj hn => ih i hj hn W HO)

/-- Replacing an actual binder type by a convertible neutral type preserves
every joint comparison and carrier guard in its body. Neither binder type
needs a computational join with the other; the unchanged tail stays exact. -/
theorem proofErase_joint_neutral_context
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (EA : proofErase Γ A = ProofShape.mkApps (.bvar i) args)
    (EB : proofErase Γ B = ProofShape.mkApps (.bvar j) args')
    (H : JointCheck Step (proofEraseCtx (A :: Γ)) kind a b) :
    JointCheck Step (proofEraseCtx (B :: Γ)) kind a b := by
  apply H.neutral_oracle hhead hsubst
    (ContextSubstitution.of_defeqCtx hΓ (.succ .zero HAB)) (k := 0)
  intro n
  cases n with
  | zero =>
    change NeutralResultChange 0 ((proofErase Γ A).liftN 1) ((proofErase Γ B).liftN 1)
    rw [EA, EB, ProofShape.liftN_mkApps, ProofShape.liftN_mkApps]
    exact .neutral (Nat.zero_le _) (Nat.zero_le _)
  | succ n => exact .refl

/-- Certified joint checking supports the entire neutral-context transport
without any lower-stage proposition beta hypothesis. The relation stays
certified, with its primitive future certificates intact. -/
theorem proofErase_certified_neutral_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (EA : proofErase Γ A = ProofShape.mkApps (.bvar i) args)
    (EB : proofErase Γ B = ProofShape.mkApps (.bvar j) args')
    (H : JointCheck (ErasedBetaStableJoint D) (proofEraseCtx (A :: Γ)) kind a b) :
    JointCheck (ErasedBetaStableJoint D) (proofEraseCtx (B :: Γ)) kind a b :=
  proofErase_joint_neutral_context erased_beta_stable_joint_head
    (erased_beta_stable_joint_subst heq hs) hΓ HAB EA EB H

end Lean4Lean.VEnv.Strengthening
