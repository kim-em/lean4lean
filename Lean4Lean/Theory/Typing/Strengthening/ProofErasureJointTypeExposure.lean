import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRigidExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedPiExposure

/-! # Typed comparison modes and empty-structure carrier conversion

Sort-typed endpoints cannot enter the lambda or structure-eta cases that
require common-mode checking. Typed replay preserves this exclusion through
computation, so either joint comparison mode yields inferred checking. Rigid
family exposure then transfers empty-structure guards along typed comparison.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private sort_not_lam sort_not_constructor
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedPiExposure
variable [Params]

private theorem types_inferred_raw
    (hstep : ErasedScopedPrimitiveDescent Step)
    (H : JointCompare Step Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb) :
    JointCompare Step Δ false sa sb := by
  change JointCheck Step Δ (.compare mode) sa sb at H
  generalize E : JointCheckKind.compare mode = kind at H
  induction H generalizing Γ a b u v mode with
  | leaf H =>
    cases E
    cases H with
    | refl => exact .leaf .refl
    | sort H => exact .leaf (.sort H)
    | const H => exact .leaf (.const H)
    | etaL H =>
      obtain ⟨_, _, HE, _⟩ := H.shape
      exact (sort_not_lam hΓ ha (Ea.trans HE)).elim
    | etaR H =>
      obtain ⟨_, _, HE, _⟩ := H.shape
      exact (sort_not_lam hΓ hb (Eb.trans HE)).elim
  | app HF HX => exact .app HF HX
  | appCarrier R HF HX => exact .appCarrier R HF HX
  | proj H => exact .proj H
  | forallE HA HB => exact .forallE HA HB
  | forallSorted S S' HA T T' HB => exact .forallSorted S S' HA T T' HB
  | lam | lamSorted | lamCommon | etaBodyL | etaLams => exact (sort_not_lam hΓ ha Ea).elim
  | etaBodyR => exact (sort_not_lam hΓ hb Eb).elim
  | structFields hi hx hp hf => exact (sort_not_constructor hΓ ha hi hx hp hf Ea).elim
  | compute Ra Rb HC ih =>
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea Ra
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb Rb
    exact .compute Ra Rb (ih hΓ HA.hasType.2 HB.hasType.2 EΓ EA EB E)
  | symm H ih => exact .symm (ih hΓ hb ha EΓ Eb Ea E)
  | carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases E

/-- At independently sort-typed endpoints, either joint comparison mode can be
read in inferred mode without changing computation, raw endpoints or stage.
This is conversion of an existing certificate, not comparison completeness. -/
theorem proofErase_joint_types_inferred
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (H : JointCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b)) :
    JointCompare Step (proofEraseCtx Γ) false (proofErase Γ a) (proofErase Γ b) :=
  types_inferred_raw hstep H hΓ ha hb rfl rfl rfl

/-- Typed comparison with an empty structure carrier exposes that family on
the other side and supplies a guard there. No common reduct of the two full
types or alignment of their parameter syntax is required. -/
theorem proofErase_joint_unit_carrier_target
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (ProofShape.mkApps (.const family ls) args) out)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hf : info.numFields = 0) (hp : ps.length = info.nparams)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ T (.sort u)) (hU : env.HasType univs Γ U (.sort v))
    (H : JointCompare Step (proofEraseCtx Γ) mode (proofErase Γ T) (proofErase Γ U))
    (ET : proofErase Γ T = ProofShape.mkApps (.const family ls) ps) :
    JointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ U) a b := by
  have HC := proofErase_joint_types_inferred hstep hΓ hT hU H
  rw [ET] at HC
  exact HC.unit_carrier_target hn hi hx hf hp

/-- The quotient-repaired concrete joint stages support empty-structure carrier
conversion at the same stage, with no extra core-head or re-synthesis premise.
The only conversion evidence required is the supplied typed joint comparison. -/
theorem proofErase_joint_quot_unit_carrier_target
    (heq : env.HasCanonicalEq) (hq : QuotRegistered env)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hf : info.numFields = 0) (hp : ps.length = info.nparams)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ T (.sort u)) (hU : env.HasType univs Γ U (.sort v))
    (H : JointCompare (ErasedJointStage (ErasedQuotCore.definitions hq) stage)
      (proofEraseCtx Γ) mode (proofErase Γ T) (proofErase Γ U))
    (ET : proofErase Γ T = ProofShape.mkApps (.const family ls) ps) :
    JointCarrierGuard (ErasedJointStage (ErasedQuotCore.definitions hq) stage)
      (proofEraseCtx Γ) (proofErase Γ U) a b := by
  apply proofErase_joint_unit_carrier_target
    (erased_joint_stage_descent heq (ErasedQuotCore.sound hq) stage) ?_ hi hx hf hp hΓ hT hU H ET
  intro Δ ls args out HR
  exact erased_joint_stage_no_rigid heq (henv.projectionRigid hi)
    (ErasedQuotCore.no_rigid hq (henv.projectionRigid hi)) stage HR (ProofShape.constHead_mkApps _ _)

end Lean4Lean.VEnv.Strengthening
