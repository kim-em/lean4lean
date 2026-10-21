import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureBox
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureDependentRecord
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureTypeComparison

/-! # Recursive record fields from certified type conversion

A certified comparison from a structural subsingleton constructs a future
carrier guard at its target. That target can be the actual parameter of a
nonempty Box or the first projection determining a dependent record's value
field. Neither field requires common comparison of its two values.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- A certified type comparison transports structural subsingleton checking
into the parameter of a nonempty Box. The resulting whole-record carrier is
outside the structural subsingleton grammar. The target parameter may require
computation and need not join the source type. Actual endpoint typings are
required when this raw future guard is reflected. -/
theorem proofErase_future_box_compared_subsingleton
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hD : ∀ {family info}, env.projections family info → ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : info.nparams = 1) (hf : info.numFields = 1)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const family []) (.bvar 1))))
    (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hc : env.constants family = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ T (.sort u)) (hU : env.HasType univs Γ U (.sort (.succ .zero)))
    (HC : JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ) mode (proofErase Γ T) (proofErase Γ U))
    (HS : SubsingletonCarrier (proofErase Γ T)) :
    BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.const family []) U)) a b ∧
      ¬ SubsingletonCarrier (proofErase Γ (.app (.const family []) U)) := by
  have hBox : env.HasType univs Γ (.const family [])
      (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) := .const hc (by simp) rfl
  have hBU := hBox.app hU
  have E : proofErase Γ (.app (.const family []) U) = .app (.const family []) (proofErase Γ U) := by
    rw [show proofErase Γ (.app (.const family []) U) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ hBU),
      show proofErase Γ (.const family []) = .const family [] from
        if_neg (not_isProof_function_to_sort hΓ hBox)]
  rw [E]
  constructor
  · exact (proofErase_certified_compared_subsingleton_future heq hs hD hΓ hT hU HC HS).box
      hi hx hp hf hshape hadm
  · intro H
    have Hzero := SubsingletonCarrier.record_numFields (ps := [proofErase Γ U]) hi H
    omega

/-- The value field of a dependent pair can be checked at a converted first
projection. A certified comparison from a structural subsingleton supplies its
full future guard, while a separate future comparison checks the type fields.
This handles the actual earlier-field dependency without assuming arbitrary
carrier conversion or future common comparison of the value fields. -/
theorem proofErase_future_dependent_pair_compared_field
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hD : ∀ {family info}, env.projections family info → ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ T (.sort u)) (hU : env.HasType univs Γ U (.sort (.succ .zero)))
    (EU : proofErase Γ U = .proj family 0 a)
    (HC : JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ) mode (proofErase Γ T) (proofErase Γ U))
    (HS : SubsingletonCarrier (proofErase Γ T))
    (HTy : BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true)
      (proofEraseCtx Γ) (.proj family 0 a) (.proj family 0 b)) :
    BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ) (.const family []) a b := by
  have HV := proofErase_certified_compared_subsingleton_future heq hs hD hΓ hT hU HC HS
    (a := ProofShape.proj family 1 a) (b := ProofShape.proj family 1 b)
  rw [EU] at HV
  exact BetaStableCarrier.dependent_pair hi hx hp hf hshape hadm HTy HV

end Lean4Lean.VEnv.Strengthening
