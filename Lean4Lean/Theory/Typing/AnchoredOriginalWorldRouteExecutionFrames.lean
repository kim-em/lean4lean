import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBaseHistory
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRouteFrameCalls

/-! Execution reads annotated frame occurrences. Two equal raw frame boxes
may have different world baselines, so a composed interpreter must retain
the annotation when selecting its generated frame. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

structure WorldBoundaryFrame.ExecutionData
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target common : List VExpr}
    {strata : EquationStratification env} (P : VEnv → Prop)
    (base : OriginalCaptureBase env U registry target) (caps : CaptureCaps)
    (frontier : List (World strata.rules.length))
    (occurrence : WorldBoundaryFrame env U registry target common commonLeft commonRight strata) where
  generation : WorldGenerated strata P base caps commonLeft commonRight occurrence.box.graph
    occurrence.box.frame.realization.frame.raw occurrence.controls
  replayable : generation.Replayable
  controlled : generation.Controlled frontier
  compatible : generation.UsesControlPrefix occurrence.controls.cutoff occurrence.controls.fuel
  covered : Covered (@EquationControlMeasure.Less strata.rules.length)
    generation.worlds occurrence.world.worlds
  hereditary : generation.Hereditary frontier

/-- Transport a positively stored occurrence along its exact box/control
equalities. World coverage remains a separate required proof. -/
noncomputable def WorldBoundaryFrame.ExecutionData.ofOccurrence
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {frontier : List (World strata.rules.length)}
    (occurrence : WorldBoundaryFrame env U registry target common commonLeft commonRight strata)
    (boxed : OriginalTypeRouteFrameBox env U registry target common commonLeft commonRight)
    (controls : OriginalWorldControls strata boxed.sourceEnv)
    (generated : WorldGenerated strata P base caps commonLeft commonRight boxed.graph
      boxed.frame.realization.frame.raw controls)
    (sameBox : boxed = occurrence.box) (sameControls : HEq controls occurrence.controls)
    (replayable : generated.Replayable) (ready : generated.Controlled frontier)
    (compatible : generated.UsesControlPrefix controls.cutoff controls.fuel)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length)
      generated.worlds occurrence.world.worlds)
    (hereditary : generated.Hereditary frontier) :
    WorldBoundaryFrame.ExecutionData P base caps frontier occurrence := by
  cases occurrence
  cases sameBox
  cases eq_of_heq sameControls
  exact ⟨generated, replayable, ready, compatible, covered, hereditary⟩

noncomputable def WorldBoundaryFrame.ExecutionData.callFrame
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {frontier : List (World strata.rules.length)}
    (display : OriginalNestedDisplay U common expression assignedType)
    (frame : OriginalTypeRouteFrame env registry target display.graph commonLeft commonRight)
    (controls : OriginalWorldControls strata display.sourceEnv)
    (world : WorldEnvironmentProvenance strata U (frame.realization.frame.dependencyEnvironment controls.ordered))
    (data : WorldBoundaryFrame.ExecutionData P base caps frontier ⟨frame.box, controls, world⟩) :
    WorldCallFrameData (P := P) (base := base) (caps := caps) (display := display)
      controls world frontier frame.realization where
  generation := data.generation
  replayable := data.replayable
  controlled := data.controlled
  compatible := data.compatible
  closed := frame.closed
  capacity := Nat.le_refl _
  covered := data.covered
  hereditary := data.hereditary

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

abbrev ExecutionFrames
    (boundary : route.WorldBoundary inputs leftControls rightControls leftWorld rightWorld)
    (P : VEnv → Prop) (base : OriginalCaptureBase env U registry target) (caps : CaptureCaps)
    (frontier : List (World strata.rules.length)) :=
  ∀ occurrence ∈ boundary.frames, WorldBoundaryFrame.ExecutionData P base caps frontier occurrence

/-- A stored positive child is selected by its position, including duplicate
raw boxes. This is the entry point used when reopening a history group. -/
noncomputable def executionFrameAt
    (boundary : route.WorldBoundary inputs leftControls rightControls leftWorld rightWorld)
    (controls : ∀ i : Fin route.frames.length, OriginalWorldControls strata (route.frames[i]).sourceEnv)
    (generated : ∀ i : Fin route.frames.length,
      WorldGenerated strata P base caps commonLeft commonRight (route.frames[i]).graph
        (route.frames[i]).frame.realization.frame.raw (controls i))
    (coherent : boundary.FrameOccurrenceCoherent controls generated)
    (ready : ∀ i, (generated i).Controlled frontier)
    (compatible : ∀ i, (generated i).UsesControlPrefix cutoff fuel)
    (replayable : ∀ i, (generated i).Replayable)
    (hereditary : ∀ i, (generated i).Hereditary frontier)
    (index : Fin route.frames.length) :
    WorldBoundaryFrame.ExecutionData P base caps frontier (boundary.frameAt index) := by
  apply WorldBoundaryFrame.ExecutionData.ofOccurrence (boundary.frameAt index)
    (route.frames[index]) (controls index) (generated index) (boundary.frameAt_box index).symm
    (coherent index).1 (replayable index) (ready index)
  · have matched := (compatible index).controls_match
    simpa only [matched.1, matched.2] using compatible index
  · exact (coherent index).2
  · exact hereditary index

/-- Read the exact occurrence alignment retained by a dormant history. -/
noncomputable def executionFramesOfCoherent
    (boundary : route.WorldBoundary inputs leftControls rightControls leftWorld rightWorld)
    (controls : ∀ boxed ∈ route.frames, OriginalWorldControls strata boxed.sourceEnv)
    (generated : ∀ boxed (member : boxed ∈ route.frames),
      WorldGenerated strata P base caps commonLeft commonRight boxed.graph
        boxed.frame.realization.frame.raw (controls boxed member))
    (coherent : boundary.FrameCoherent controls generated)
    (ready : ∀ boxed member, (generated boxed member).Controlled frontier)
    (compatible : ∀ boxed member, (generated boxed member).UsesControlPrefix cutoff fuel)
    (replayable : ∀ boxed member, (generated boxed member).Replayable)
    (hereditary : ∀ boxed member, (generated boxed member).Hereditary frontier) :
    boundary.ExecutionFrames P base caps frontier := by
  intro occurrence member
  have rawMember := boundary.frame_member occurrence member
  have facts := coherent occurrence member
  let chosen : WorldBoundaryFrame env U registry target common commonLeft commonRight strata :=
    ⟨occurrence.box, controls occurrence.box rawMember, occurrence.world⟩
  let result : WorldBoundaryFrame.ExecutionData P base caps frontier chosen := {
    generation := generated occurrence.box rawMember
    replayable := replayable occurrence.box rawMember
    controlled := ready occurrence.box rawMember
    compatible := by
      have controlsPrefix := (compatible occurrence.box rawMember).controls_match
      simpa only [chosen, controlsPrefix.1, controlsPrefix.2] using compatible occurrence.box rawMember
    covered := facts.2
    hereditary := hereditary occurrence.box rawMember }
  have same : chosen = occurrence := by
    exact congrArg (fun control => (⟨occurrence.box, control, occurrence.world⟩ :
      WorldBoundaryFrame env U registry target common commonLeft commonRight strata)) facts.1
  exact same ▸ result

noncomputable def ExecutionFrames.trans_left
    {middle : OriginalNestedDisplay U common middleExpression middleAssigned}
    {first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate}
    {second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final}
    {firstInputs : first.WorldInputs strata} {secondInputs : second.WorldInputs strata}
    {middleControls : OriginalWorldControls strata middle.sourceEnv}
    {middleWorld : WorldEnvironmentProvenance strata U intermediate}
    {before : first.WorldBoundary firstInputs leftControls middleControls leftWorld middleWorld}
    {after : second.WorldBoundary secondInputs middleControls rightControls middleWorld rightWorld}
    (data : (before.trans after).ExecutionFrames P base caps frontier) :
    before.ExecutionFrames P base caps frontier :=
  fun occurrence member => data occurrence (List.mem_append_left _ member)

noncomputable def ExecutionFrames.trans_right
    {middle : OriginalNestedDisplay U common middleExpression middleAssigned}
    {first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate}
    {second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final}
    {firstInputs : first.WorldInputs strata} {secondInputs : second.WorldInputs strata}
    {middleControls : OriginalWorldControls strata middle.sourceEnv}
    {middleWorld : WorldEnvironmentProvenance strata U intermediate}
    {before : first.WorldBoundary firstInputs leftControls middleControls leftWorld middleWorld}
    {after : second.WorldBoundary secondInputs middleControls rightControls middleWorld rightWorld}
    (data : (before.trans after).ExecutionFrames P base caps frontier) :
    after.ExecutionFrames P base caps frontier :=
  fun occurrence member => data occurrence (List.mem_append_right _ member)

end RawGeneratedTypeRoute.WorldBoundary
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
