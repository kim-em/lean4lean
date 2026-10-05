import Lean4Lean.Theory.Typing.AnchoredOriginalSeedArgumentProvenance
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRouteBoundary
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldGeneration
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldOwnerEnvironment

/-! Operative finite histories carry exact boundary annotations. This property
is separate from numerical generation and query control: neither of those
identifies the annotated frames used when a dormant route is executed. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

theorem RawGeneratedTypeRoute.WorldBoundary.frame_member
    {strata : EquationStratification env}
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    {route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final}
    {inputs : route.WorldInputs strata}
    {leftControls : OriginalWorldControls strata left.sourceEnv}
    {rightControls : OriginalWorldControls strata right.sourceEnv}
    {leftWorld : WorldEnvironmentProvenance strata U initial}
    {rightWorld : WorldEnvironmentProvenance strata U final}
    (boundary : route.WorldBoundary inputs leftControls rightControls leftWorld rightWorld)
    (occurrence : WorldBoundaryFrame env U registry target common commonLeft commonRight strata)
    (member : occurrence ∈ boundary.frames) : occurrence.box ∈ route.frames := by
  rw [← boundary.frames_boxes]
  exact List.mem_map_of_mem member

/-- Each occurrence is admitted by its own actual execution baseline.
Repeated raw boxes must satisfy every corresponding annotated occurrence. -/
noncomputable def RawGeneratedTypeRoute.WorldBoundary.FrameCoherent
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    {route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final}
    {inputs : route.WorldInputs strata}
    {leftControls : OriginalWorldControls strata left.sourceEnv}
    {rightControls : OriginalWorldControls strata right.sourceEnv}
    {leftWorld : WorldEnvironmentProvenance strata U initial}
    {rightWorld : WorldEnvironmentProvenance strata U final}
    (boundary : route.WorldBoundary inputs leftControls rightControls leftWorld rightWorld)
    (controls : ∀ boxed ∈ route.frames, OriginalWorldControls strata boxed.sourceEnv)
    (generated : ∀ boxed (member : boxed ∈ route.frames),
      WorldGenerated strata P base caps commonLeft commonRight boxed.graph
        boxed.frame.realization.frame.raw (controls boxed member)) : Prop :=
  ∀ occurrence (member : occurrence ∈ boundary.frames),
    controls occurrence.box (boundary.frame_member occurrence member) = occurrence.controls ∧
    Covered (@EquationControlMeasure.Less strata.rules.length)
      (generated occurrence.box (boundary.frame_member occurrence member)).worlds occurrence.world.worlds

namespace RawGeneratedTypeRoute.WorldBoundary
variable {strata : EquationStratification env}
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    {route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final}
    {inputs : route.WorldInputs strata}
    {leftControls : OriginalWorldControls strata left.sourceEnv}
    {rightControls : OriginalWorldControls strata right.sourceEnv}
    {leftWorld : WorldEnvironmentProvenance strata U initial}
    {rightWorld : WorldEnvironmentProvenance strata U final}

theorem frames_length
    (boundary : route.WorldBoundary inputs leftControls rightControls leftWorld rightWorld) :
    boundary.frames.length = route.frames.length := by
  have lengths := congrArg List.length boundary.frames_boxes
  simpa only [List.length_map] using lengths

/-- The occurrence at the same finite position as the raw frame table. -/
noncomputable def frameAt
    (boundary : route.WorldBoundary inputs leftControls rightControls leftWorld rightWorld)
    (index : Fin route.frames.length) : WorldBoundaryFrame env U registry target common commonLeft commonRight strata :=
  boundary.frames[index.val]'(by rw [boundary.frames_length]; exact index.isLt)

theorem frameAt_box
    (boundary : route.WorldBoundary inputs leftControls rightControls leftWorld rightWorld)
    (index : Fin route.frames.length) : (boundary.frameAt index).box = route.frames[index] := by
  have same := congrArg (fun frames => frames[index.val]?) boundary.frames_boxes
  have bound : index.val < boundary.frames.length := by rw [boundary.frames_length]; exact index.isLt
  simp only [List.getElem?_map, List.getElem?_eq_getElem bound,
    List.getElem?_eq_getElem index.isLt, Option.map_some] at same
  exact Option.some.inj same

theorem frameAt_mem
    (boundary : route.WorldBoundary inputs leftControls rightControls leftWorld rightWorld)
    (index : Fin route.frames.length) : boundary.frameAt index ∈ boundary.frames := by
  exact List.getElem_mem _

noncomputable def FrameOccurrenceCoherent
    {P : VEnv → Prop} {base : OriginalCaptureBase env U registry target}
    (boundary : route.WorldBoundary inputs leftControls rightControls leftWorld rightWorld)
    (controls : ∀ index : Fin route.frames.length, OriginalWorldControls strata (route.frames[index]).sourceEnv)
    (generated : ∀ index : Fin route.frames.length,
      WorldGenerated strata P base caps commonLeft commonRight (route.frames[index]).graph
        (route.frames[index]).frame.realization.frame.raw (controls index)) : Prop :=
  ∀ index, HEq (controls index) (boundary.frameAt index).controls ∧
    Covered (@EquationControlMeasure.Less strata.rules.length)
      (generated index).worlds (boundary.frameAt index).world.worlds

/-- A coherent initial dictionary can populate every actual occurrence. Later
compositions may instead select distinct generations at repeated raw boxes. -/
theorem FrameCoherent.occurrences
    {P : VEnv → Prop} {base : OriginalCaptureBase env U registry target}
    {boundary : route.WorldBoundary inputs leftControls rightControls leftWorld rightWorld}
    {controls : ∀ boxed ∈ route.frames, OriginalWorldControls strata boxed.sourceEnv}
    {generated : ∀ boxed (member : boxed ∈ route.frames),
      WorldGenerated strata P base caps commonLeft commonRight boxed.graph
        boxed.frame.realization.frame.raw (controls boxed member)}
    (coherent : boundary.FrameCoherent controls generated) :
    boundary.FrameOccurrenceCoherent
      (fun index => controls (route.frames[index]) (List.getElem_mem _))
      (fun index => generated (route.frames[index]) (List.getElem_mem _)) := by
  have transfer (occurrence : WorldBoundaryFrame env U registry target common commonLeft commonRight strata)
      (member : occurrence ∈ boundary.frames)
      (boxed : OriginalTypeRouteFrameBox env U registry target common commonLeft commonRight)
      (boxedMember : boxed ∈ route.frames) (same : occurrence.box = boxed) :
      HEq (controls boxed boxedMember) occurrence.controls ∧
        Covered (@EquationControlMeasure.Less strata.rules.length)
          (generated boxed boxedMember).worlds occurrence.world.worlds := by
    rcases occurrence with ⟨box, occurrenceControls, occurrenceWorld⟩
    dsimp only at same ⊢
    cases same
    have matched := coherent ⟨boxed, occurrenceControls, occurrenceWorld⟩ member
    exact ⟨heq_of_eq matched.1, matched.2⟩
  intro index
  exact transfer (boundary.frameAt index) (boundary.frameAt_mem index)
    (route.frames[index]) (List.getElem_mem _) (boundary.frameAt_box index)

end RawGeneratedTypeRoute.WorldBoundary

/-- Positive generation can reopen dormant histories only when their
computed seed/prior worlds and every stored frame agree with an actual route
boundary. Each selected owner's actual frame must also be covered by that
owner's location-derived envelope in the group ledger. Numeric frame cost
alone does not identify the captured worlds. The dormant seed keeps the same
admission: reconstructing its stored query must use its actual owner reserve. -/
noncomputable def WorldGenerated.Replayable
    {base : OriginalCaptureBase env U registry target}
    (generated : WorldGenerated strata P base caps left right graph frame controls) : Prop := by
  induction generated with
  | identity | empty => exact True
  | weaken _ _ _ _ _ ih => exact ih
  | merge first second ihFirst ihSecond => exact ihFirst ∧ ihSecond
  | bind generated baseline capacity domain annotation displayed certificate resources typed arguments needs bounded covered ih =>
    exact ih ∧ Covered (@EquationControlMeasure.Less strata.rules.length) generated.worlds baseline.worlds
  | capture generated baseline capacity domain initial argument location lineage query queryAvailable queryBound queryAdapter
      certificate resources typed arguments needs bounded covered ih =>
    exact ih ∧ Covered (@EquationControlMeasure.Less strata.rules.length) generated.worlds baseline.worlds
  | historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
      historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
      tailIH seedIH priorIH historyIH ownerIH =>
    exact tailIH ∧ seedIH ∧ priorIH ∧
      (∀ index, historyIH index) ∧ (∀ entry member, ownerIH entry member) ∧
      (∀ entry member, Covered (@EquationControlMeasure.Less strata.rules.length)
        (owners entry member).worlds
        (entry.owner.worldEnvironment ownerControls initialProvenance).worlds) ∧
      (seed.owner.Argument ∧ Covered (@EquationControlMeasure.Less strata.rules.length)
        baselines.1.worlds
        (seed.owner.worldEnvironment seedControls initialProvenance).worlds) ∧
      Covered (@EquationControlMeasure.Less strata.rules.length) seedGenerated.worlds baselines.1.worlds ∧
      Covered (@EquationControlMeasure.Less strata.rules.length) priorGenerated.worlds baselines.2.worlds ∧
      (∃ boundary : history.route.WorldBoundary routeInputs seedControls priorGenerated.callControls
          baselines.1 baselines.2,
        boundary.FrameOccurrenceCoherent historyControls historyGenerated) ∧
      Covered (@EquationControlMeasure.Less strata.rules.length) generated.worlds baselines.2.worlds

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
