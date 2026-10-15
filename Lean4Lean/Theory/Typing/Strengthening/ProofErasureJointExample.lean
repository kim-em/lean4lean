import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierApplication
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointStages

/-! # The known paired-instantiation witness now has a joint carrier guard

The propositions f x and f y for distinct unit variables have a joint carrier
certificate at Prop. No old carrier certificate exists even with all the new
joint-stage computations. This repairs the concrete old witness, not the
unrestricted paired-instantiation or joint re-synthesis laws.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private not_proof_at_positive_type from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params]

/-- A neutral function into Prop accepts carrier-compared empty-structure
arguments. The joint carrier succeeds at stage zero, while the old carrier
language fails at every stage of the same enlarged computation family. -/
theorem joint_unit_neutral_application
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : info.nparams = 0) (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs Γ (.const family ls) (.sort (.succ u)))
    (hl : Lookup Γ f (.forallE (.const family ls) (.sort .zero)))
    (hiT : env.HasType univs Γ (.bvar i) (.const family ls))
    (hjT : env.HasType univs Γ (.bvar j) (.const family ls)) (hne : i ≠ j) :
    env.IsDefEq univs Γ (.app (.bvar f) (.bvar i)) (.app (.bvar f) (.bvar j)) (.sort .zero) ∧
    JointCarrierGuard (ErasedJointStage D 0)
      (proofEraseCtx Γ) (proofErase Γ (.sort .zero)) (proofErase Γ (.app (.bvar f) (.bvar i)))
      (proofErase Γ (.app (.bvar f) (.bvar j))) ∧
    ∀ stage, ¬ StructureCarrierGuard (ErasedJointStage D stage) (proofEraseCtx Γ)
      (proofErase Γ (.sort .zero)) (proofErase Γ (.app (.bvar f) (.bvar i)))
      (proofErase Γ (.app (.bvar f) (.bvar j))) := by
  have hfun : env.HasType univs Γ (.bvar f) (.forallE (.const family ls) (.sort .zero)) := .bvar hl
  have hleft := hfun.app hiT
  have hright := hfun.app hjT
  have hnl := not_isProof_of_sort hΓ hleft
  have hnr := not_isProof_of_sort hΓ hright
  have hnfun := not_isProof_fn hΓ hfun hiT hnl
  have Ef : proofErase Γ (.bvar f) = .bvar f := if_neg hnfun
  have Ei : proofErase Γ (.bvar i) = .bvar i := if_neg (not_proof_at_positive_type hΓ hS hiT)
  have Ej : proofErase Γ (.bvar j) = .bvar j := if_neg (not_proof_at_positive_type hΓ hS hjT)
  have ES : proofErase Γ (.const family ls) = .const family ls := if_neg (not_isProof_of_sort hΓ hS)
  have hΓS : OnCtx (.const family ls :: Γ) (env.IsType univs) := ⟨hΓ, _, hS⟩
  have hPi := HasType.forallE hS (HasType.sort (l := .zero) (by trivial))
  have EPi : proofErase Γ (.forallE (.const family ls) (.sort .zero)) =
      .forallE (proofErase Γ (.const family ls)) (.sort .zero) := by
    rw [show proofErase Γ (.forallE (.const family ls) (.sort .zero)) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ hPi),
      show proofErase (.const family ls :: Γ) (.sort .zero) = .sort .zero from
        if_neg (not_isProof_of_sort hΓS (HasType.sort (by trivial)))]
  have R : ProofShape.TypeRecovery (fun _ _ => False) (contextOracle (proofEraseCtx Γ))
      (proofErase Γ (.bvar f)) (.forallE (proofErase Γ (.const family ls)) (.sort .zero)) := by
    rw [Ef, ← EPi, proofEraseCtx_oracle, ← erasedTypeOracle_valid hΓ hl]
    exact .bvar
  have HX : StructureCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (.const family ls)) (proofErase Γ (.bvar i)) (proofErase Γ (.bvar j)) := by
    rw [ES]
    exact .subsingleton (.unit hi hx hf (ps := []) hp.symm)
  have HC : ScopedRecoveredCarrierApplication (ErasedJointStage D 0) (ErasedJointStage D 0)
      (proofEraseCtx Γ) (proofErase Γ (.app (.bvar f) (.bvar i)))
      (proofErase Γ (.app (.bvar f) (.bvar j))) :=
    (proofErase_recovered_carrier_application_forward hΓ hfun hfun hiT hjT hnl hnr R .refl HX).scoped
      (fun H => H.elim)
  refine ⟨IsDefEq.appDF hfun (IsDefEq.unitLike hi (params := []) hp.symm hx hf hiT hjT),
    .carrierChecked HC.application.joint, ?_⟩
  intro stage H
  rw [show proofErase Γ (.sort .zero) = .sort .zero from
    if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial)))] at H
  have HC := H.sort_checked (erased_joint_stage_head stage)
  rw [show proofErase Γ (.app (.bvar f) (.bvar i)) = .app _ _ from if_neg hnl,
    show proofErase Γ (.app (.bvar f) (.bvar j)) = .app _ _ from if_neg hnr, Ef, Ei, Ej] at HC
  exact hne (HC.bvar_app_argument_injective (erased_joint_stage_head stage))

/-- The exact three-variable context used by the paired-closure refutation
supplies a joint carrier certificate at stage zero. Its two instantiated bodies
remain outside the old carrier language at every joint stage. -/
theorem joint_neutral_application_context
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs [] (.const family ls) (.sort (.succ u))) :
    ∃ Γ, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ (.app (.bvar 2) (.bvar 0)) (.sort .zero) ∧
      env.HasType univs Γ (.app (.bvar 2) (.bvar 1)) (.sort .zero) ∧
      JointCarrierGuard (ErasedJointStage D 0)
        (proofEraseCtx Γ) (proofErase Γ (.sort .zero)) (proofErase Γ (.app (.bvar 2) (.bvar 0)))
        (proofErase Γ (.app (.bvar 2) (.bvar 1))) ∧
      ∀ stage, ¬ StructureCarrierGuard (ErasedJointStage D stage) (proofEraseCtx Γ)
        (proofErase Γ (.sort .zero)) (proofErase Γ (.app (.bvar 2) (.bvar 0)))
        (proofErase Γ (.app (.bvar 2) (.bvar 1))) := by
  let S := VExpr.const family ls
  let F := VExpr.forallE S (.sort .zero)
  let Γ := [S, S, F]
  have hF : env.HasType univs [] F (.sort (.imax (.succ u) (.succ .zero))) :=
    HasType.forallE hS (HasType.sort (by trivial))
  have hΓ : OnCtx Γ (env.IsType univs) :=
    ⟨⟨⟨trivial, _, hF⟩, _, hS.weak0 henv.ordered⟩, _, hS.weak0 henv.ordered⟩
  have hSΓ : env.HasType univs Γ S (.sort (.succ u)) := hS.weak0 henv.ordered
  have h₀ : env.HasType univs Γ (.bvar 0) S := .bvar .zero
  have h₁ : env.HasType univs Γ (.bvar 1) S := .bvar (.succ .zero)
  have hl : Lookup Γ 2 F := .succ (.succ .zero)
  have hfun : env.HasType univs Γ (.bvar 2) F := .bvar hl
  have H := joint_unit_neutral_application (D := D) hΓ hi hp hx hf hSΓ hl h₀ h₁ (by decide)
  exact ⟨Γ, hΓ, hfun.app h₀, hfun.app h₁, H.2⟩

end Lean4Lean.VEnv.Strengthening
