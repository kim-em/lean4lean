import Lean4Lean.Theory.Typing.AnchoredOriginalRigidConstantPrototype
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCapturePreservation
import Lean4Lean.Theory.Typing.AnchoredOriginalRetainedHeaderWorldCalls

/-! Install the actual rigid constant input with its unchanged header query
annotation. The one new opening is the genuine earlier header in a nil frame;
its sponsorship is supplied by the actual declaration decrease. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace RichRigidConstantInput

noncomputable def observationProvenance
    (input : RichRigidConstantInput sourceEnv env U registry target name frozenLevels levels plan support)
    (controls : OriginalWorldControls strata sourceEnv)
    (node : EndpointState sourceEnv U source (.const name levels) assigned)
    (locals : List Nat) (σ : Subst)
    (annotation : WorldCertProvenance strata input.certificate) :
    WorldObsProvenance strata (input.observation node locals σ) :=
  .rigidFamily input.origin input.lookup input.inert input.seedWF input.seedLength
    input.frozenWF input.levelsWF input.seedFrozen input.frozenLevelsEq input.typeClosed
    plan input.certificate input.ready input.typed annotation
    (controls.atHeader input.origin) (EndpointProvenance.ofLocation .here .nil)

@[simp] theorem observation_depth
    (input : RichRigidConstantInput sourceEnv env U registry target name frozenLevels levels plan support)
    (node : EndpointState sourceEnv U source (.const name levels) assigned)
    (locals : List Nat) (σ : Subst) (policy : Name → Nat → Nat) :
    (input.observation node locals σ).headDepth policy = input.certificate.headDepth policy := by
  simp only [observation, RichObs.headDepth]

theorem observationProvenance_worlds
    (input : RichRigidConstantInput sourceEnv env U registry target name frozenLevels levels plan support)
    (controls : OriginalWorldControls strata sourceEnv)
    (node : EndpointState sourceEnv U source (.const name levels) assigned)
    (locals : List Nat) (σ : Subst)
    (annotation : WorldCertProvenance strata input.certificate) :
    (input.observationProvenance controls node locals σ annotation).worlds =
      [originalCallWorld (controls.atHeader input.origin) .fundamental
        (.ref (input.origin.familyHeader input.seedWF).reference) .nil] ++ annotation.worlds := rfl

/-- The stored code supplies its actual depth and all nested opening worlds.
Only the real header F world is added; the constructor receives no fabricated
annotation or replacement resource table. -/
noncomputable def observationControlled
    (input : RichRigidConstantInput sourceEnv env U registry target name frozenLevels levels plan support)
    (controls : OriginalWorldControls strata sourceEnv)
    (node : EndpointState sourceEnv U source (.const name levels) assigned)
    (locals : List Nat) (σ : Subst)
    (ready : ControlledStoredQuery (controls.atHeader input.origin) frontier
      (.certificate input.certificate))
    (headerPaid : Sponsored frontier
      [originalCallWorld (controls.atHeader input.origin) .fundamental
        (.ref (input.origin.familyHeader input.seedWF).reference) .nil]) :
    ControlledStoredQuery controls frontier (.observation (input.observation node locals σ)) where
  annotation := input.observationProvenance controls node locals σ ready.annotation
  within := by
    intro control active
    simpa only [StoredOriginalQuery.headDepth, observation, RichObs.headDepth,
      OriginalWorldControls.atHeader] using
      ready.within control active
  sponsored := by
    change Sponsored frontier (input.observationProvenance controls node locals σ ready.annotation).worlds
    rw [observationProvenance_worlds]
    exact headerPaid.merge ready.sponsored

end RichRigidConstantInput
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
