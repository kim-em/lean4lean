import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRouteExecutionFrames
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplyPiSeedHistory

/-! Exact finite occurrence adapters between stored controlled histories and
execution boundaries. Repeated boxes retain separate occurrence annotations. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace RawGeneratedTypeRoute.WorldBoundary

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target common : List VExpr}
  {commonLeft commonRight : Subst} {strata : EquationStratification env}
  {left : OriginalNestedDisplay U common leftExpression leftAssigned}
  {right : OriginalNestedDisplay U common rightExpression rightAssigned}
  {route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final}
  {inputs : route.WorldInputs strata}
  {leftControls : OriginalWorldControls strata left.sourceEnv}
  {rightControls : OriginalWorldControls strata right.sourceEnv}
  {leftWorld : WorldEnvironmentProvenance strata U initial}
  {rightWorld : WorldEnvironmentProvenance strata U final}
  {P : VEnv → Prop} {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
  {frontier : List (World strata.rules.length)}


theorem frame_prefix
    (boundary : route.WorldBoundary inputs leftControls rightControls leftWorld rightWorld)
    (occurrence) (member : occurrence ∈ boundary.frames) :
    occurrence.controls.HasPrefix leftControls.cutoff leftControls.fuel := by
  induction boundary generalizing occurrence with
  | identity | equality => simp only [frames, List.not_mem_nil] at member
  | same _ _ _ _ _ _ _ _ _ same
  | assigned _ _ _ _ _ _ _ _ _ same
  | typedEquality _ _ _ _ _ _ _ _ _ _ _ _ same =>
    simp only [frames, List.mem_singleton] at member
    subst occurrence
    exact ⟨same.1.symm, same.2.symm⟩
  | trans before after ihBefore ihAfter =>
    rcases List.mem_append.mp member with member | member
    · exact ihBefore occurrence member
    · have next := ihAfter occurrence member
      have same := before.controls_match
      exact ⟨next.1.trans same.1.symm, next.2.trans same.2.symm⟩
  | piDomain _ _ _ _ ih => exact ih occurrence member
  | applyPi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ boundary _ ih =>
    simp only [frames, List.mem_cons] at member
    rcases member with rfl | rfl | member
    · exact ⟨rfl, rfl⟩
    · exact ⟨boundary.controls_match.1.symm, boundary.controls_match.2.symm⟩
    · exact ih occurrence member

noncomputable def executionFramesOfData
    (data : route.ControlledWorldData P base caps cutoff fuel frontier)
    (boundary : route.WorldBoundary data.inputs leftControls rightControls leftWorld rightWorld)
    (coherent : boundary.FrameOccurrenceCoherent data.controls data.frames) :
    boundary.ExecutionFrames P base caps frontier := by
  intro occurrence member
  let witness := Classical.indefiniteDescription _ (List.getElem_of_mem member)
  let index := witness.val
  have bound := (Classical.choose witness.property)
  have equal := Classical.choose_spec witness.property
  let position : Fin route.frames.length := ⟨index, by rw [← boundary.frames_length]; exact bound⟩
  have selected := boundary.executionFrameAt data.controls data.frames coherent
    data.ready data.compatible data.replayable data.hereditary position
  have same : boundary.frameAt position = occurrence := equal
  exact same ▸ selected

/-- Reindex one selected occurrence without identifying its baseline with the
worlds computed by its generation. -/
private structure Reboxed
    (occurrence : WorldBoundaryFrame env U registry target common commonLeft commonRight strata)
    (boxed : OriginalTypeRouteFrameBox env U registry target common commonLeft commonRight)
    (P : VEnv → Prop) (base : OriginalCaptureBase env U registry target) (caps : CaptureCaps)
    (frontier : List (World strata.rules.length)) (cutoff : Nat) (fuel : Nat → Nat) where
  controls : OriginalWorldControls strata boxed.sourceEnv
  generation : WorldGenerated strata P base caps commonLeft commonRight boxed.graph
    boxed.frame.realization.frame.raw controls
  ready : generation.Controlled frontier
  compatible : generation.UsesControlPrefix cutoff fuel
  replayable : generation.Replayable
  hereditary : generation.Hereditary frontier
  sameControls : HEq controls occurrence.controls
  covered : Covered (@EquationControlMeasure.Less strata.rules.length) generation.worlds occurrence.world.worlds

private noncomputable def rebox
    (occurrence : WorldBoundaryFrame env U registry target common commonLeft commonRight strata)
    (boxed : OriginalTypeRouteFrameBox env U registry target common commonLeft commonRight)
    (sameBox : occurrence.box = boxed)
    (data : occurrence.ExecutionData P base caps frontier)
    (matched : occurrence.controls.HasPrefix cutoff fuel) :
    Reboxed occurrence boxed P base caps frontier cutoff fuel := by
  cases sameBox
  exact ⟨occurrence.controls, data.generation, data.controlled,
    by simpa only [matched.1, matched.2] using data.compatible,
    data.replayable, data.hereditary, HEq.rfl, data.covered⟩

/-- Recover the finite stored table from the SAME occurrence-indexed execution
witnesses. Source generation is structural evidence, not a semantic supplier. -/
noncomputable def controlledDataOfExecution
    (boundary : route.WorldBoundary inputs leftControls rightControls leftWorld rightWorld)
    (generated : route.SourceGenerated P base caps)
    (execution : boundary.ExecutionFrames P base caps frontier) :
    route.ControlledWorldData P base caps leftControls.cutoff leftControls.fuel frontier := by
  let packet := fun i : Fin route.frames.length =>
    rebox (boundary.frameAt i) (route.frames[i]) (boundary.frameAt_box i)
      (execution (boundary.frameAt i) (boundary.frameAt_mem i))
      (boundary.frame_prefix _ (boundary.frameAt_mem i))
  exact {
    generated := generated, inputs := inputs
    controls := fun i => (packet i).controls
    frames := fun i => (packet i).generation
    ready := fun i => (packet i).ready
    compatible := fun i => (packet i).compatible
    replayable := fun i => (packet i).replayable
    hereditary := fun i => (packet i).hereditary }

theorem controlledDataOfExecution_inputs
    (boundary : route.WorldBoundary inputs leftControls rightControls leftWorld rightWorld)
    (generated : route.SourceGenerated P base caps)
    (execution : boundary.ExecutionFrames P base caps frontier) :
    (boundary.controlledDataOfExecution generated execution).inputs = inputs := rfl

theorem controlledDataOfExecution_coherent
    (boundary : route.WorldBoundary inputs leftControls rightControls leftWorld rightWorld)
    (generated : route.SourceGenerated P base caps)
    (execution : boundary.ExecutionFrames P base caps frontier) :
    boundary.FrameOccurrenceCoherent
      (boundary.controlledDataOfExecution generated execution).controls
      (boundary.controlledDataOfExecution generated execution).frames := by
  intro i
  let packet := rebox (boundary.frameAt i) (route.frames[i]) (boundary.frameAt_box i)
      (execution (boundary.frameAt i) (boundary.frameAt_mem i))
      (boundary.frame_prefix _ (boundary.frameAt_mem i))
  exact ⟨packet.sameControls, packet.covered⟩

end RawGeneratedTypeRoute.WorldBoundary
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
