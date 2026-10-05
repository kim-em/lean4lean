import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBoundedCallBank

/-! Recover executable primitive frame inputs from the exact annotated
occurrence in a retained route. No inference from numeric frame equality is
used: FrameCoherent supplies the actual controls and world coverage. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem RawGeneratedTypeRoute.WorldBoundary.callFrame
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target common : List VExpr}
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
        boxed.frame.realization.frame.raw (controls boxed member))
    (coherent : boundary.FrameCoherent controls generated)
    (frontier : List (World strata.rules.length))
    (ready : ∀ boxed member, (generated boxed member).Controlled frontier)
    (compatible : ∀ boxed member, (generated boxed member).UsesControlPrefix cutoff fuel)
    (replayable : ∀ boxed member, (generated boxed member).Replayable)
    (hereditary : ∀ boxed member, (generated boxed member).Hereditary frontier)
    (display : OriginalNestedDisplay U common expression assignedType)
    (frame : OriginalTypeRouteFrame env registry target display.graph commonLeft commonRight)
    (selectedControls : OriginalWorldControls strata display.sourceEnv)
    (selectedWorld : WorldEnvironmentProvenance strata U
      (frame.realization.frame.dependencyEnvironment selectedControls.ordered))
    (member : (⟨frame.box, selectedControls, selectedWorld⟩ :
      WorldBoundaryFrame env U registry target common commonLeft commonRight strata) ∈ boundary.frames) :
    Nonempty (WorldCallFrameData (P := P) (base := base) (caps := caps) (display := display)
      selectedControls selectedWorld frontier frame.realization) := by
  let occurrence : WorldBoundaryFrame env U registry target common commonLeft commonRight strata :=
    ⟨frame.box, selectedControls, selectedWorld⟩
  have rawMember := boundary.frame_member occurrence member
  have facts := coherent occurrence member
  have same : controls frame.box rawMember = selectedControls := facts.1
  have covered : Covered (@EquationControlMeasure.Less strata.rules.length)
      (generated frame.box rawMember).worlds selectedWorld.worlds := facts.2
  let result : WorldCallFrameData (P := P) (base := base) (caps := caps) (display := display)
      (controls frame.box rawMember) selectedWorld frontier frame.realization := {
    generation := generated frame.box rawMember
    hereditary := hereditary frame.box rawMember
    replayable := replayable frame.box rawMember
    controlled := ready frame.box rawMember
    compatible := by
      have controlsPrefix := (compatible frame.box rawMember).controls_match
      simpa only [controlsPrefix.1, controlsPrefix.2] using compatible frame.box rawMember
    closed := frame.closed
    capacity := Nat.le_refl _
    covered := covered }
  exact ⟨(congrArg (fun control => WorldCallFrameData (P := P) (base := base) (caps := caps)
    (display := display) control selectedWorld frontier frame.realization) same).mp result⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
