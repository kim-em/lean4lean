import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorDemandStructure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFunctionRecordNative
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFunctionRecordRegistration
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAtomicUnitTransport

/-! # Actual structure guards for the joint constructor observer

Ordinary type uniqueness fixes the registered family and universe instance.
The dependent parameter itself is read from the native type observation, not
inferred from ordinary equality of the assigned record type.
-/
namespace Lean4Lean.VEnv.Strengthening.FunctionRecordDemand
open _root_.Lean4Lean Params ProofShape
open ConstructorDemand (Key TypeEquality Sets unitCarrier no_structure_control unit_structure_output)
variable [Params]

variable (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
variable (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
variable (hTag : env.projections t (PositiveHeaderRegistration.info 0 [.forallE (.const s []) (.const s [])] t c))
variable (hF : env.HasType univs [] (.const t []) (.forallE (.forallE (.const s []) (.const s [])) (.sort (.succ .zero))))
local notation "U" => unitCarrier hi hS
local notation "T" => recordCarrier hi hS hTag hF

/-- A record-key structure major selects the original monomorphic family and
one retained parameter. The expansion output is its fieldless constructor at
that same selected parameter, without any assumption about the parameter. -/
theorem record_structure_output (hstep : ErasedScopedPrimitiveDescent Step)
    (H : HeterogeneousControl.ControlTyping Δ e (.atom T))
    (R : NativeMaskedStructureExpansion Step Δ e out) :
    ∃ p, ScopedTypeRecovery Step Δ e (.app (.const t []) p) ∧ out = .app (.const c []) p := by
  obtain ⟨Γ, f, hΓ, rfl, hf, rfl⟩ := H
  change env.HasType univs Γ f (.app (.const t []) (.lam (.const s []) (.const uc []))) at hf
  cases R with
  | @intro r info ls _ ps hi' hx ha hp RN =>
    obtain ⟨A, hfA, EA⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ hf RN
    obtain ⟨args, rfl, _⟩ := proofErase_const_spine_inv EA
    obtain ⟨_, hA⟩ := hf.isType henv hΓ
    obtain ⟨E, HL, _⟩ := henv.headInversion.rigid_rigid (args := [VExpr.lam (.const s []) (.const uc [])]) hΓ
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

end Lean4Lean.VEnv.Strengthening.FunctionRecordDemand
