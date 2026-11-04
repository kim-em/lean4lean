import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedTypedExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecoveryExposure

/-! # Retaining comparisons while exposing typed heads

The exposed endpoint keeps an inferred comparison with the original other
endpoint. Existing computation constructors supply the residual certificate;
no contraction stability or common computational join is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private sort_not_lam sort_not_constructor
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedPiExposure
open private ProofShape.typeHead ProofShape.typeHead_compute
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecoveryExposure
variable [Params]

private theorem computed_type_residual_pair
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : ComputedJointCompare Step Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb) :
    (∀ tag, ProofShape.typeHead sa = some tag → ∃ out, ScopedCompute Step Δ sb out ∧ ProofShape.typeHead out = some tag ∧
      ComputedJointCompare Step Δ false sa out) ∧
    (∀ tag, ProofShape.typeHead sb = some tag → ∃ out, ScopedCompute Step Δ sa out ∧ ProofShape.typeHead out = some tag ∧
      ComputedJointCompare Step Δ false out sb) := by
  change ComputedJointCheck Step Δ (.compare mode) sa sb at H
  generalize EK : JointCheckKind.compare mode = kind at H
  induction H generalizing Γ a b u v mode with
  | leaf H =>
    cases EK
    cases H with
    | refl => exact ⟨fun _ E => ⟨_, .refl, E, .leaf .refl⟩, fun _ E => ⟨_, .refl, E, .leaf .refl⟩⟩
    | sort H => exact ⟨fun _ E => ⟨_, .refl, E, .leaf (.sort H)⟩, fun _ E => ⟨_, .refl, E, .leaf (.sort H)⟩⟩
    | const => constructor <;> intro _ E <;> cases E
    | etaL H =>
      obtain ⟨_, _, E, _⟩ := H.shape
      exact (sort_not_lam hΓ ha (Ea.trans E)).elim
    | etaR H =>
      obtain ⟨_, _, E, _⟩ := H.shape
      exact (sort_not_lam hΓ hb (Eb.trans E)).elim
  | forallE HA HB =>
    exact ⟨fun _ E => ⟨_, .refl, E, .forallE HA HB⟩, fun _ E => ⟨_, .refl, E, .forallE HA HB⟩⟩
  | forallSorted S S' HA T T' HB =>
    exact ⟨fun _ E => ⟨_, .refl, E, .forallSorted S S' HA T T' HB⟩,
      fun _ E => ⟨_, .refl, E, .forallSorted S S' HA T T' HB⟩⟩
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
      obtain ⟨out, R, HE, HX⟩ := IH.1 tag (ProofShape.typeHead_compute hhead RA E)
      exact ⟨out, RB.trans R, HE, .compute RA .refl HX⟩
    · intro tag E
      obtain ⟨out, R, HE, HX⟩ := IH.2 tag (ProofShape.typeHead_compute hhead RB E)
      exact ⟨out, RA.trans R, HE, .compute .refl RB HX⟩
  | symm H ih =>
    have IH := ih hΓ hb ha EΓ Eb Ea EK
    constructor
    · intro tag E
      obtain ⟨out, R, HE, HX⟩ := IH.2 tag E
      exact ⟨out, R, HE, .symm HX⟩
    · intro tag E
      obtain ⟨out, R, HE, HX⟩ := IH.1 tag E
      exact ⟨out, R, HE, .symm HX⟩
  | carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases EK

/-- Computed comparison with an actual assigned Pi exposes a native Pi while
retaining an inferred certificate against the original assigned type. -/
theorem proofErase_computed_joint_pi_residual
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (H : ComputedJointCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b))
    (Eb : proofErase Γ b = .forallE A B) :
    ∃ A' B', ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ a) (.forallE A' B') ∧
      ComputedJointCompare Step (proofEraseCtx Γ) false (.forallE A' B') (proofErase Γ b) := by
  obtain ⟨out, R, HE, HX⟩ := (computed_type_residual_pair hstep hhead H hΓ ha hb rfl rfl rfl).2 true
    (by rw [Eb]; rfl)
  cases out <;> try cases HE
  exact ⟨_, _, R, HX⟩

end Lean4Lean.VEnv.Strengthening
