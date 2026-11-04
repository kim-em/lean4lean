import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedCarrierTypeChecking
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecoveryExposure

/-! # Typed head exposure for the computed comparison grammar -/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private sort_not_lam sort_not_constructor
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedPiExposure
open private ProofShape.typeHead ProofShape.typeHead_compute
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecoveryExposure
variable [Params]

private theorem types_inferred_raw
    (hstep : ErasedScopedPrimitiveDescent Step)
    (H : ComputedJointCompare Step Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb) :
    ComputedJointCompare Step Δ false sa sb := by
  change ComputedJointCheck Step Δ (.compare mode) sa sb at H
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
  | appComputed R HF HX => exact .appComputed R HF HX
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
theorem proofErase_computed_joint_types_inferred
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (H : ComputedJointCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b)) :
    ComputedJointCompare Step (proofEraseCtx Γ) false (proofErase Γ a) (proofErase Γ b) :=
  types_inferred_raw hstep H hΓ ha hb rfl rfl rfl

private theorem computed_type_exposure_pair
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : ComputedJointCompare Step Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb) :
    (∀ tag, ProofShape.typeHead sa = some tag → ∃ out, ScopedCompute Step Δ sb out ∧ ProofShape.typeHead out = some tag) ∧
    (∀ tag, ProofShape.typeHead sb = some tag → ∃ out, ScopedCompute Step Δ sa out ∧ ProofShape.typeHead out = some tag) := by
  change ComputedJointCheck Step Δ (.compare mode) sa sb at H
  generalize EK : JointCheckKind.compare mode = kind at H
  induction H generalizing Γ a b u v mode with
  | leaf H =>
    cases EK
    cases H with
    | refl | sort => exact ⟨fun _ E => ⟨_, .refl, E⟩, fun _ E => ⟨_, .refl, E⟩⟩
    | const => constructor <;> intro _ E <;> cases E
    | etaL H =>
      obtain ⟨_, _, E, _⟩ := H.shape
      exact (sort_not_lam hΓ ha (Ea.trans E)).elim
    | etaR H =>
      obtain ⟨_, _, E, _⟩ := H.shape
      exact (sort_not_lam hΓ hb (Eb.trans E)).elim
  | forallE | forallSorted => exact ⟨fun _ E => ⟨_, .refl, E⟩, fun _ E => ⟨_, .refl, E⟩⟩
  | app | appCarrier | appComputed | proj => constructor <;> intro _ E <;> cases E
  | lam | lamSorted | lamCommon | etaBodyL | etaLams => exact (sort_not_lam hΓ ha Ea).elim
  | etaBodyR => exact (sort_not_lam hΓ hb Eb).elim
  | structFields hi hx hp hf => exact (sort_not_constructor hΓ ha hi hx hp hf Ea).elim
  | compute RA RB H ih =>
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea RA
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb RB
    have IH := ih hΓ HA.hasType.2 HB.hasType.2 EΓ EA EB EK
    constructor
    · intro tag E
      obtain ⟨out, R, HE⟩ := IH.1 tag (ProofShape.typeHead_compute hhead RA E)
      exact ⟨out, RB.trans R, HE⟩
    · intro tag E
      obtain ⟨out, R, HE⟩ := IH.2 tag (ProofShape.typeHead_compute hhead RB E)
      exact ⟨out, RA.trans R, HE⟩
  | symm H ih => exact (ih hΓ hb ha EΓ Eb Ea EK).symm
  | carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases EK

/-- At independently sort-typed endpoints, comparison with a displayed Pi
exposes a Pi using the same primitive computation relation. -/
theorem proofErase_computed_joint_pi_exposure
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (H : ComputedJointCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b))
    (Ea : proofErase Γ a = .forallE A B) :
    ∃ A' B', ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ b) (.forallE A' B') := by
  obtain ⟨out, R, HE⟩ := (computed_type_exposure_pair hstep hhead H hΓ ha hb rfl rfl rfl).1 true
    (by rw [Ea]; rfl)
  cases out <;> try cases HE
  exact ⟨_, _, R⟩

end Lean4Lean.VEnv.Strengthening
