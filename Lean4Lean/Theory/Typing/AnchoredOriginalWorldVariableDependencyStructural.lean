import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDependencyReindexData
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDependencyScope
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBaseHistorySelection
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCaptureMergePreservation

/-! Structural demand recursion retains the actual outer caller. The
weakening arm composes common insertions for its IH, then restores only the
original weakening constructor; it never recurses on a newly built frame. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

theorem WorldGenerated.ReindexDependencyAt.merge
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {firstFrame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ firstAvailable}
    {secondFrame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ secondAvailable}
    {controls : OriginalWorldControls strata sourceEnv}
    {first : WorldGenerated strata P base caps commonLeft commonRight graph firstFrame controls}
    {second : WorldGenerated strata P base caps commonLeft commonRight graph secondFrame controls}
    (firstIH : first.ReindexDependencyAt index) :
    (first.merge second).ReindexDependencyAt index := by
  intro frontier inRange replayable compatible ready hereditary valid substitutions
    destinationEnvironment destinationBaseline capacity covered
    callerSource callerExpression callerAssigned caller nextCommon nextLeft nextRight nextCaps rho insertion
    leftTail rightTail capsTail leftAssigned left leftControls sameCutoff sameFuel
    leftEnvironment leftBaseline leftLocals leftAvailable leftFrame leftData henv hscoped formed
    rank profile requestedFootprint requested requestedAvailable requestedReady sponsored bank unary
  simp only [RawOriginalRichFrame.Valid] at valid
  obtain ⟨firstReady⟩ := ready.selectGeneration first
    (fun _ present => List.mem_append_left _ present) rfl rfl
  obtain ⟨firstHereditary⟩ := hereditary.selectGeneration first hereditary.tablesClosed.1
    (List.sublist_append_left _ _) rfl rfl
  have localCapacity : environmentCost (firstFrame.dependencyEnvironment controls.ordered) ≤
      environmentCost ((firstFrame.merge secondFrame).dependencyEnvironment controls.ordered) := by
    change environmentCost (firstFrame.dependencyEnvironment controls.ordered) ≤
      environmentCost (firstFrame.dependencyEnvironment controls.ordered ++ secondFrame.dependencyEnvironment controls.ordered)
    rw [merge_environmentCost_append]
    exact Nat.le_max_left _ _
  have firstCovered : Covered (@EquationControlMeasure.Less strata.rules.length) first.worlds destinationBaseline.worlds := by
    intro world present
    apply covered world
    rw [WorldGenerated.merge_worlds]
    exact List.mem_append_left _ present
  obtain ⟨answer⟩ := firstIH frontier inRange replayable.1 compatible.1 firstReady firstHereditary valid.1
    substitutions destinationBaseline (Nat.le_trans localCapacity capacity) firstCovered
    caller insertion leftTail rightTail capsTail left leftControls sameCutoff sameFuel
    leftBaseline leftFrame leftData henv hscoped formed requested requestedAvailable requestedReady sponsored bank unary
  exact ⟨{ answer with
    capacity := fun ordered => Nat.le_trans (answer.capacity ordered) localCapacity
    covered := by
      intro world member
      obtain ⟨previous, present, below⟩ := answer.covered world member
      refine ⟨previous, ?_, below⟩
      change previous ∈ (first.merge second).worlds
      rw [WorldGenerated.merge_worlds]
      exact List.mem_append_left _ present }⟩

theorem WorldGenerated.ReindexDependencyAt.weaken
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {controls : OriginalWorldControls strata sourceEnv}
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph frame controls)
    {originalNextCaps : CaptureCaps}
    {κ : Lift} (originalInsertion : Ctx.Lift' κ common next)
    (originalLeft : Subst.lift_l κ originalNextLeft = commonLeft)
    (originalRight : Subst.lift_l κ originalNextRight = commonRight)
    (originalCaps : (fun i => originalNextCaps (κ.liftVar i)) = caps)
    (ih : generated.ReindexDependencyAt index) :
    (generated.weaken originalInsertion originalLeft originalRight originalCaps).ReindexDependencyAt index := by
  intro frontier inRange replayable compatible ready hereditary valid substitutions
    destinationEnvironment destinationBaseline capacity covered
    callerSource callerExpression callerAssigned caller nextCommon nextLeft nextRight nextCaps rho insertion
    leftTail rightTail capsTail leftAssigned left leftControls sameCutoff sameFuel
    leftEnvironment leftBaseline leftLocals leftAvailable leftFrame leftData henv hscoped formed
    rank profile requestedFootprint requested requestedAvailable requestedReady sponsored bank unary
  have liftedLeft : Subst.lift_l (κ.comp rho) nextLeft = commonLeft := by
    calc
      _ = Subst.lift_l κ (Subst.lift_l rho nextLeft) := by funext i; simp [Subst.lift_l, Lift.liftVar_comp]
      _ = _ := (congrArg (Subst.lift_l κ) leftTail).trans originalLeft
  have liftedRight : Subst.lift_l (κ.comp rho) nextRight = commonRight := by
    calc
      _ = Subst.lift_l κ (Subst.lift_l rho nextRight) := by funext i; simp [Subst.lift_l, Lift.liftVar_comp]
      _ = _ := (congrArg (Subst.lift_l κ) rightTail).trans originalRight
  have liftedCaps : (fun i => nextCaps ((κ.comp rho).liftVar i)) = caps := by
    calc
      _ = (fun i => nextCaps (rho.liftVar (κ.liftVar i))) := by funext i; rw [Lift.liftVar_comp]
      _ = _ := (congrArg (fun table : CaptureCaps => fun i => table (κ.liftVar i)) capsTail).trans originalCaps
  let input : OriginalNestedDisplay U nextCommon ((raw index).lift' (κ.comp rho)) leftAssigned := {
    left with expression_eq := lift'_comp.trans left.expression_eq }
  let originalReady : generated.Controlled frontier := ⟨ready.annotation, ready.within, ready.sponsored⟩
  let originalHereditary : generated.Hereditary frontier :=
    ⟨hereditary.tablesClosed, hereditary.bases, hereditary.ready⟩
  let inputData : WorldCallFrameData (P := P) (base := base) (caps := nextCaps)
      (display := input) leftControls leftBaseline frontier leftFrame :=
    ⟨leftData.generation, leftData.replayable, leftData.controlled, leftData.compatible,
      leftData.closed, leftData.capacity, leftData.covered, leftData.hereditary⟩
  obtain ⟨answer⟩ := ih frontier inRange replayable compatible originalReady originalHereditary valid substitutions
    destinationBaseline capacity covered caller (originalInsertion.comp insertion) liftedLeft liftedRight liftedCaps
    input leftControls sameCutoff sameFuel leftBaseline leftFrame inputData henv hscoped formed
    requested requestedAvailable requestedReady sponsored bank unary
  exact answer.weaken originalInsertion originalLeft originalRight originalCaps

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
