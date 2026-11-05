import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorDemandNative
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorDemandRegistration
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAtomicUnitTransport

/-! # Actual structure guards for the joint constructor observer

Ordinary type uniqueness fixes the registered family and universe instance.
The dependent parameter itself is read from the native type observation, not
inferred from ordinary equality of the assigned record type.
-/
namespace Lean4Lean.VEnv.Strengthening.ConstructorDemand
open _root_.Lean4Lean Params ProofShape
variable [Params]

/-- A control arrow or universe cannot be the major of a registered structure
expansion. This uses ordinary native replay and rigid head separation. -/
theorem no_structure_control (hstep : ErasedScopedPrimitiveDescent Step)
    (H : HeterogeneousControl.ControlTyping Δ e t)
    (ht : (∃ A B, t = .arrow A B) ∨ (∃ u, t = .sort u))
    (R : NativeMaskedStructureExpansion Step Δ e out) : False := by
  obtain ⟨Γ, f, hΓ, rfl, hf, rfl⟩ := H
  cases R with
  | intro hi hx ha hp RN =>
    obtain ⟨T, hFT, ET⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ hf RN
    obtain ⟨ps, rfl, _⟩ := proofErase_const_spine_inv ET
    obtain ⟨_, hT⟩ := hFT.isType henv hΓ
    rcases ht with ⟨A, B, rfl⟩ | ⟨u, rfl⟩
    · exact IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hi) hT (hFT.uniqU henv hΓ hf)
    · exact henv.headInversion.sort_rigid hΓ (henv.projectionRigid hi)
        ((hFT.uniqU henv hΓ hf).typeChain henv hΓ hT).symm

variable (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
variable (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
variable (hTag : env.projections t (PositiveHeaderRegistration.info 0 [.const s []] t c))
variable (hF : env.HasType univs [] (.const t []) (.forallE (.const s []) (.sort (.succ .zero))))
local notation "U" => unitCarrier hi hS
local notation "T" => recordCarrier hi hTag hF

/-- A unit-key structure major expands to the actual registered unit constructor. -/
theorem unit_structure_output (hstep : ErasedScopedPrimitiveDescent Step)
    (H : HeterogeneousControl.ControlTyping Δ e (.atom U))
    (R : NativeMaskedStructureExpansion Step Δ e out) : out = .const uc [] := by
  letI := U
  have H' : AtomicControl.ControlTyping Δ e .atom := H
  exact (AtomicUnitObservation.masked_structure_terminal hstep hi rfl rfl H' R).2

/-- A record-key structure major selects the original monomorphic family and
one retained parameter. The expansion output is its fieldless constructor at
that same selected parameter, without any assumption about the parameter. -/
theorem record_structure_output (hstep : ErasedScopedPrimitiveDescent Step)
    (H : HeterogeneousControl.ControlTyping Δ e (.atom T))
    (R : NativeMaskedStructureExpansion Step Δ e out) :
    ∃ p, ScopedTypeRecovery Step Δ e (.app (.const t []) p) ∧ out = .app (.const c []) p := by
  obtain ⟨Γ, f, hΓ, rfl, hf, rfl⟩ := H
  change env.HasType univs Γ f (.app (.const t []) (.const uc [])) at hf
  cases R with
  | @intro r info ls _ ps hi' hx ha hp RN =>
    obtain ⟨A, hfA, EA⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ hf RN
    obtain ⟨args, rfl, _⟩ := proofErase_const_spine_inv EA
    obtain ⟨_, hA⟩ := hf.isType henv hΓ
    obtain ⟨E, HL, _⟩ := henv.headInversion.rigid_rigid (args := [VExpr.const uc []]) hΓ
      (henv.projectionRigid hTag) (henv.projectionRigid hi')
      ((hf.uniqU henv hΓ hfA).typeChain henv hΓ hA)
    cases E
    cases HL
    cases henv.ordered.projections_unique hTag hi'
    have hp : ps.length = 1 := hp
    cases ps with
    | nil => simp at hp
    | cons p ps =>
      have E : ps = [] := List.length_eq_zero_iff.1 (by simp only [List.length_cons] at hp; omega)
      subst ps
      refine ⟨p, ?_, ?_⟩
      · simpa only [ProofShape.mkApps, List.foldl_cons, List.foldl_nil] using RN
      · simp [nativeStructureOutput, PositiveHeaderRegistration.info,
          PositiveHeaderRegistration.constructor, VProjectionInfo.numFields, ProofShape.mkApps, etaOpen, VExpr.forallArity]

end Lean4Lean.VEnv.Strengthening.ConstructorDemand
