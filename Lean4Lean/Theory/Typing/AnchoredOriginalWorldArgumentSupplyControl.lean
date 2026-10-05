import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCapturePreservation
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionSortableSubstitution

/-! Control evidence follows every actual observer in a finite argument supply. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false

/-- Controls refer to each actual raw observer in the constructed supply. -/
def RichArgumentSupply.Controlled
    {available : Valuation}
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata controlSource)
    (frontier : List (World strata.rules.length))
    (supply : RichArgumentSupply sourceEnv env U registry target node locals σ available needs) : Prop :=
  match supply with
  | .nil => True
  | .cons query tail =>
      Nonempty (ControlledStoredQuery controls frontier (.observation query.observation)) ∧
      tail.Controlled controls frontier

theorem RichArgumentSupply.lookup_controlled
    {available : Valuation}
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    (supply : RichArgumentSupply sourceEnv env U registry target node locals σ available needs)
    (ready : supply.Controlled controls frontier) (member : need ∈ needs) :
    ∃ query : RichGradedResult sourceEnv env U registry target node locals σ available need.profile,
      Nonempty (ControlledStoredQuery controls frontier (.observation query.observation)) := by
  induction supply with
  | nil => cases member
  | cons query tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨query, ready.1⟩
    · exact ih ready.2 member

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
