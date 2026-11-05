import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorDemandStructure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIgnoredRecordNative
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIgnoredRecordRegistration
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAtomicUnitTransport

/-! # Full native preservation with ignored record parameters

Only the registered constructor and family heads carry operational evidence.
The supplied parameter needs no observation; its ordinary singleton carrier
fixes the control typing used by the joint native induction.
-/
namespace Lean4Lean.VEnv.Strengthening.IgnoredRecordDemand
open _root_.Lean4Lean Params ProofShape
open ConstructorDemand (Key TypeEquality Sets unitCarrier no_structure_control unit_structure_output UnitArrows)
variable [Params]

variable (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
variable (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
variable (Q : UnitArrows)
variable (hTag : env.projections t (PositiveHeaderRegistration.info 0 [(Q.control (unitCarrier hi hS)).expr] t c))
variable (hF : env.HasType univs [] (.const t []) (.forallE (Q.control (unitCarrier hi hS)).expr (.sort (.succ .zero))))
local notation "U" => unitCarrier hi hS
local notation "T" => recordCarrier hi hS Q hTag hF

/-- A record-key structure major selects the original monomorphic family and
one retained parameter. The expansion output is its fieldless constructor at
that same selected parameter, without any assumption about the parameter. -/
theorem record_structure_output (hstep : ErasedScopedPrimitiveDescent Step)
    (H : HeterogeneousControl.ControlTyping Δ e (.atom T))
    (R : NativeMaskedStructureExpansion Step Δ e out) :
    ∃ p, ScopedTypeRecovery Step Δ e (.app (.const t []) p) ∧ out = .app (.const c []) p := by
  obtain ⟨Γ, f, hΓ, rfl, hf, rfl⟩ := H
  change env.HasType univs Γ f (.app (.const t []) (Q.value hi hS)) at hf
  cases R with
  | @intro r info ls _ ps hi' hx ha hp RN =>
    obtain ⟨A, hfA, EA⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ hf RN
    obtain ⟨args, rfl, _⟩ := proofErase_const_spine_inv EA
    obtain ⟨_, hA⟩ := hf.isType henv hΓ
    obtain ⟨E, HL, _⟩ := henv.headInversion.rigid_rigid (args := [Q.value hi hS]) hΓ
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

end Lean4Lean.VEnv.Strengthening.IgnoredRecordDemand
