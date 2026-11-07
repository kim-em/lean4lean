import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertProjectionContraction

/-! # Discharge dependent-pair type selection at Pi-inert stage zero

The full carrier guard first supplies comparison of the two type projections.
Proved projection contraction supports independent keep/select outcomes. The
existing residual and world-history consumers therefore need no selection
hypothesis at stage zero for a constructor without definition-table unfolding.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- The full stage-zero carrier checker supports one-sided type-field
selection of an actual dependent pair. The opposite result may retain its
projection or select its field too. Structure eta, carrierChecked and nested
carrier certificates are all included through typed field readout followed by
the proved sort-typed projection contraction. No extra selection obligation,
confluence or forward beta-closure premise is supplied. -/
theorem proofErase_pi_inert_zero_pair_type_field_selection
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x (.const family []))
    (hy : env.HasType univs Γ y (.const family []))
    (H : ComputedJointCarrierGuard (PiInertStage D 0) (proofEraseCtx Γ) (.const family [])
      (proofErase Γ x) (proofErase Γ y))
    (RI : Primitive D (.proj family 0 (proofErase Γ x)) left)
    (RR : ProjectionResult family 0 (proofErase Γ y) right) :
    ComputedJointCompare (PiInertStage D 0) (proofEraseCtx Γ) true left right := by
  have hstep : ErasedScopedPrimitiveDescent (PiInertStage D 0) :=
    ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs 0)
  have hprim : ∀ {Δ a b}, Primitive D a b → ScopedCompute (PiInertStage D 0) Δ a b :=
    fun R => .base (pi_inert_stage_core (.inl (.inl (.inl R))))
  have HC := (proofErase_computed_dependent_pair_fields @hstep @hprim hi hp hf hz hadm hshape hΓ hx hy H).1
  have hpx := (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hx).1
  have hpy := (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hy).1
  have TX : ControlTyping (proofEraseCtx Γ) (.proj family 0 (proofErase Γ x)) (.sort (.succ .zero)) :=
    ⟨Γ, .proj family 0 x, hΓ, rfl, hpx, if_neg (not_isProof_of_sort hΓ hpx)⟩
  have TY : ControlTyping (proofEraseCtx Γ) (.proj family 0 (proofErase Γ y)) (.sort (.succ .zero)) :=
    ⟨Γ, .proj family 0 y, hΓ, rfl, hpy, if_neg (not_isProof_of_sort hΓ hpy)⟩
  have TL : ControlTyping (proofEraseCtx Γ) left (.sort (.succ .zero)) :=
    TX.compute (Step := PiInertStage D 0) @hstep (hprim RI)
  obtain ⟨value, EX⟩ := proofErase_closed_pair_selection_shape hi hp hf hz hadm hΓ hx RI
  rw [EX] at TX HC
  have HL := pi_inert_zero_pair_type_projection_contract heq hs hi hp hf hD TX TY HC
  rcases RR.keep_or_primitive (D := D) with rfl | RR
  · exact HL
  · obtain ⟨other, EY⟩ := proofErase_closed_pair_selection_shape hi hp hf hz hadm hΓ hy RR
    rw [EY] at TY HL
    exact .symm (pi_inert_zero_pair_type_projection_contract heq hs hi hp hf hD TY TL (.symm HL))

/-- The previously isolated type-field selection obligation holds at stage
zero for the registered closed pair when its constructor is not unfolded.
This covers the full recursive carrier checker, not just inferred major checks. -/
theorem pi_inert_zero_pair_type_field_selection
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs) :
    PiInertPairTypeFieldSelection D 0 family := by
  intro Γ x y left right hΓ hx hy H RI RR
  exact proofErase_pi_inert_zero_pair_type_field_selection heq hs hi hp hf hz hadm hshape hD
    hΓ hx hy H RI RR

/-- The actual environment definition table supplies soundness and constructor
stability, discharging stage-zero pair selection without auxiliary premises. -/
theorem EnvironmentCore.pi_inert_zero_pair_type_field_selection
    (heq : env.HasCanonicalEq)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family []))) :
    PiInertPairTypeFieldSelection EnvironmentCore.definitions 0 family :=
  _root_.Lean4Lean.VEnv.Strengthening.pi_inert_zero_pair_type_field_selection
    heq EnvironmentCore.sound hi hp hf hz hadm hshape
    (EnvironmentCore.no_rigid (henv.projectionCtorRigid hi))

/-- Every actual stage-zero pair residual supplies its type-field interpretation.
Independent field reductions and selected constructor majors need no separate
selection law: the registered pair theorem supplies it. -/
theorem PiInertCarrierResidual.zero_dependent_type_field
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x (.const family []))
    (hy : env.HasType univs Γ y (.const family []))
    (H : PiInertCarrierResidual D 0 (proofEraseCtx Γ) (.const family [])
      (proofErase Γ x) (proofErase Γ y)) :
    PiInertInterpret D 0 (.compare true) (proofEraseCtx Γ)
      (.proj family 0 (proofErase Γ x)) (.proj family 0 (proofErase Γ y)) :=
  PiInertCarrierResidual.dependent_type_field_of_selection heq hs hi hp hf hz hadm hshape
    (pi_inert_zero_pair_type_field_selection heq hs hi hp hf hz hadm hshape hD) hΓ hx hy H

/-- Stage-zero pair histories preserve their type field in every allowed world,
with all independent reductions included and no selection hypothesis. -/
theorem PiInertWorldHistory.zero_dependent_type_field
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x (.const family []))
    (hy : env.HasType univs Γ y (.const family []))
    (H : PiInertWorldHistory D 0 (proofEraseCtx Γ) (.const family [])
      (proofErase Γ x) (proofErase Γ y)) :
    PiInertWorldHistory D 0 (proofEraseCtx Γ) (.sort (.succ .zero))
      (.proj family 0 (proofErase Γ x)) (.proj family 0 (proofErase Γ y)) :=
  PiInertWorldHistory.dependent_type_field_of_selection heq hs hi hp hf hz hadm hshape
    (pi_inert_zero_pair_type_field_selection heq hs hi hp hf hz hadm hshape hD) hΓ hx hy H

end Lean4Lean.VEnv.Strengthening
