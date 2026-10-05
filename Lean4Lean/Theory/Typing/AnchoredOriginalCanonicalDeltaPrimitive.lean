import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalDeltaStep
import Lean4Lean.Theory.Typing.AnchoredOriginalEndpoints

/-! Canonical unfolding at both actual primitive constant endpoints. The
right endpoint may display different equivalent universes from its assigned
type. Those universes are read from the retained constDF derivation; the
caller does not supply a type-alignment or semantic comparison answer. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
open OriginalEndpointFactor EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CanonicalDeltaPacket
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
  {strata : EquationStratification env} {name : Name} {levels : List VLevel} {profile : Profile n}

theorem primitiveAssigned
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (below : sourceEnv ≤ env)
    (reference : EndpointRef sourceEnv U source expression assigned)
    (expressionEq : expression = .const name levels) (primitive : reference.Primitive) :
    ∃ assignedLevels : List VLevel,
      (∀ level ∈ assignedLevels, level.WF U) ∧
      List.Forall₂ (· ≈ ·) packet.seedLevels assignedLevels ∧
      assigned = packet.value.type.instL assignedLevels := by
  have registered : env.constants name = some packet.value.toVConstant := by
    simpa only [packet.nameEq] using packet.registered.1
  cases reference with
  | left original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expressionEq
    case constDF.refl otherWF levelWF lookup wf count equiv closed ambient =>
      have same := Option.some.inj (registered.symm.trans (below.constants lookup))
      cases same
      exact ⟨_, wf, packet.equivalent, rfl⟩
  | right original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expressionEq
    case constDF.refl wf count levelWF lookup otherWF equiv closed ambient =>
      have same := Option.some.inj (registered.symm.trans (below.constants lookup))
      cases same
      have reverse := Lean4Lean.List.Forall₂.imp (fun _ _ h => h.symm)
        (Lean4Lean.List.Forall₂.flip equiv)
      exact ⟨_, wf, Lean4Lean.List.Forall₂.trans (T := (· ≈ ·))
        (fun _ _ _ first second => first.trans second) packet.equivalent reverse, rfl⟩

/-- Both lower body calls, all type transport and the bounds on the SAME
returned packets are supplied by the canonical step. The only additional
work is inspecting the actual primitive endpoint's declaration lookup. -/
theorem primitiveStep
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (below : sourceEnv ≤ env)
    (reference : EndpointRef sourceEnv U source (.const name levels) assigned)
    (primitive : reference.Primitive)
    (locals : List Nat) (σ τ : Subst)
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length)
    (fuel : Nat → Nat) (constants schedule : Nat)
    (bounded : WithinAbove cutoff fuel packet.stratifiedDepth)
    (lower : packet.ComputationalBelow
      (EquationControlMeasure.key strata.rules.length cutoff fuel constants schedule)) :
    ∃ answer : RichComputationalValue packet.selected.origin.source env U registry target packet.bodyNode
        [] packet.bodyRealization packet.bodyRealization (fun _ => []) profile,
      ∃ _raw : RichComputationalValue packet.selected.origin.source env U registry target packet.bodyNode
          [] packet.bodyRealization packet.bodyRealization (fun _ => []) answer.rightQuery.raw,
        ∃ result : CanonicalDeltaReturnResult packet (.ref reference) locals σ τ answer,
          WithinAbove cutoff fuel result.rightQuery.packet.stratifiedDepth ∧
          WithinAbove cutoff fuel result.typeQuery.packet.stratifiedDepth := by
  obtain ⟨assignedLevels, assignedWF, seedAssigned, assignedEq⟩ :=
    packet.primitiveAssigned below reference rfl primitive
  cases assignedEq
  exact packet.step henv hscoped formed assignedWF seedAssigned (.ref reference)
    locals σ τ cutoff cutoffBound fuel constants schedule bounded lower

end CanonicalDeltaPacket
end Lean4Lean.AnchoredSource.Adapted
