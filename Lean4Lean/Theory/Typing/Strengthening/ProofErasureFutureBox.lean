import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureRecord
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCommonBetaBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointBoxAlignment

/-! # Nonempty records with recursive future field certificates

A one-field Box carries its parameter as the field type. A future field
certificate therefore supplies a full future Box guard. Box Unit distinguishes
this construction from common comparison and the structural subsingleton
grammar: two distinct variables have the guard but neither alternative applies.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private BoxCarrierAlignment.projection_recipe
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointBoxAlignment
open private ProofShape.const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params]

/-- The structural subsingleton grammar can recognize a displayed registered
record only when it has no fields. Nonempty recursive field certificates are
additional information, even when every field is itself subsingleton. -/
theorem ProofShape.SubsingletonCarrier.record_numFields
    (hi : env.projections family info)
    (H : SubsingletonCarrier (ProofShape.mkApps (.const family ls) ps)) : info.numFields = 0 := by
  generalize E : ProofShape.mkApps (.const family ls) ps = A at H
  cases H with
  | unit hi' hx hf hp =>
    obtain ⟨rfl, rfl, rfl⟩ := ProofShape.const_spine_inj E
    cases henv.ordered.projections_unique hi hi'
    exact hf
  | forallE =>
    have HE := congrArg ProofShape.constHead E
    simp only [constHead_mkApps, ProofShape.constHead] at HE
    cases HE

/-- A Box field's full future certificate supplies the full future record
certificate. The field carrier need not be structurally subsingleton or a
literal computational normal form; it is kept as the exact parameter. -/
theorem BetaStableCarrier.box
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : info.nparams = 1) (hf : info.numFields = 1)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const family []) (.bvar 1))))
    (hadm : (info.resultLevel.inst []).IsNeverZero)
    (H : BetaStableCarrier Step Δ param (.proj family 0 a) (.proj family 0 b)) :
    BetaStableCarrier Step Δ (.app (.const family []) param) a b := by
  obtain ⟨doms, result, HT⟩ := projection_telescope_exists (ls := []) hi (by simp)
  apply BetaStableCarrier.record_nested hi hx (ps := [param]) (by simp [hp]) (.inl hadm) HT
  intro i hj hn
  have hi0 : i = 0 := by omega
  subst i
  rw [BoxCarrierAlignment.projection_recipe hp hf hshape HT]
  exact H

/-- A nonempty Box of a closed positive unit supports full future checking
between distinct actual variables. Its carrier is outside the structural
subsingleton grammar, and its endpoints admit no common future comparison.
They are definitionally equal: this is a checking-language separation, not a
strengthening counterexample. All registrations remain explicit hypotheses. -/
theorem boxed_unit_future_beyond_common
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : info.nparams = 1) (hf : info.numFields = 1)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const family []) (.bvar 1))))
    (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hc : env.constants family = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hiS : env.projections unit infoS) (hpS : infoS.nparams = 0)
    (hxS : infoS.nindices = 0) (hfS : infoS.numFields = 0)
    (hS : env.HasType univs [] (.const unit levels) (.sort (.succ .zero))) :
    ∃ Γ T, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ (.bvar 0) T ∧ env.HasType univs Γ (.bvar 1) T ∧
      env.IsDefEq univs Γ (.bvar 0) (.bvar 1) T ∧
      BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ T)
        (proofErase Γ (.bvar 0)) (proofErase Γ (.bvar 1)) ∧
      (¬ SubsingletonCarrier (proofErase Γ T)) ∧
      ¬ BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true)
        (proofEraseCtx Γ) (proofErase Γ (.bvar 0)) (proofErase Γ (.bvar 1)) := by
  let S := VExpr.const unit levels
  let T := VExpr.app (.const family []) S
  have hBox {Γ} : env.HasType univs Γ (.const family [])
      (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) := .const hc (by simp) rfl
  have hT : env.HasType univs [] T (.sort (.succ .zero)) := hBox.app hS
  let Γ := [T, T]
  have hΓ : OnCtx Γ (env.IsType univs) := ⟨⟨trivial, _, hT⟩, _, hT.weak0 henv.ordered⟩
  have hTΓ : env.HasType univs Γ T (.sort (.succ .zero)) := hT.weak0 henv.ordered
  have h₀ : env.HasType univs Γ (.bvar 0) T := .bvar .zero
  have h₁ : env.HasType univs Γ (.bvar 1) T := .bvar (.succ .zero)
  have E₀ : proofErase Γ (.bvar 0) = .bvar 0 := if_neg (not_proof_at_positive_type hΓ hTΓ h₀)
  have E₁ : proofErase Γ (.bvar 1) = .bvar 1 := if_neg (not_proof_at_positive_type hΓ hTΓ h₁)
  have ET : proofErase Γ T = .app (.const family []) (.const unit levels) := by
    rw [show proofErase Γ T = .app _ _ from if_neg (not_isProof_of_sort hΓ hTΓ),
      show proofErase Γ (.const family []) = .const family [] from
        if_neg (not_isProof_function_to_sort hΓ hBox),
      show proofErase Γ S = .const unit levels from
        if_neg (not_isProof_of_sort hΓ (hS.weak0 henv.ordered))]
  have H : BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ T)
      (proofErase Γ (.bvar 0)) (proofErase Γ (.bvar 1)) := by
    rw [ET]
    apply BetaStableCarrier.box hi hx hp hf hshape hadm
    exact .subsingleton (.unit hiS hxS hfS (ps := []) hpS.symm)
  refine ⟨Γ, T, hΓ, h₀, h₁,
    proofErase_joint_carrier_reflect (erased_joint_union_descent heq hs) hΓ h₀ h₁ H.base, H, ?_, ?_⟩
  · intro HS
    rw [ET] at HS
    have hzero := SubsingletonCarrier.record_numFields (ps := [.const unit levels]) hi HS
    omega
  · intro HC
    have HC := HC.base
    rw [E₀, E₁] at HC
    have := HC.bvar_injective erased_joint_union_head
    omega

end Lean4Lean.VEnv.Strengthening
