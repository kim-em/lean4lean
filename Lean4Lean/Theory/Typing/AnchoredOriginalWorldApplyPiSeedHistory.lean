import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBaseHistory
import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiSeedHistory
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientApplyPiHistoryGeneration
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBoundaryComposition
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyCaptureAssembly
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRouteOperations

/-! Positive world data for the concrete next argument seed. The original
source/header baselines and every whole-history frame are retained through
its exact zero-scope declaration reframe. No replay answer is stored here. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private realizeWorld from Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyCaptureAssembly
open private nestedDisplay_heq from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRouteOperations
open private RetainedHeaderUniverse.source_same RetainedHeaderUniverse.source_trans from
  Lean4Lean.Theory.Typing.AnchoredOriginalWorldRouteOperations
open private trans_worldInputs trans_worldReserve environment_worlds_mpr from
  Lean4Lean.Theory.Typing.AnchoredOriginalWorldRouteOperations
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

/-- Finite data on one actual route, including every retained frame. -/
structure RawGeneratedTypeRoute.ControlledWorldData
    {strata : EquationStratification env}
    (P : VEnv → Prop) (base : OriginalCaptureBase env U registry target) (caps : CaptureCaps)
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final)
    (cutoff : Nat) (fuel : Nat → Nat) (frontier : List (World strata.rules.length)) where
  generated : route.SourceGenerated P base caps
  inputs : route.WorldInputs strata
  controls : ∀ i : Fin route.frames.length, OriginalWorldControls strata (route.frames[i]).sourceEnv
  frames : ∀ i : Fin route.frames.length,
    WorldGenerated strata P base caps commonLeft commonRight (route.frames[i]).graph
      (route.frames[i]).frame.realization.frame.raw (controls i)
  ready : ∀ i, (frames i).Controlled frontier
  compatible : ∀ i, (frames i).UsesControlPrefix cutoff fuel
  replayable : ∀ i, (frames i).Replayable
  hereditary : ∀ i, (frames i).Hereditary frontier

private abbrev FramePacket
    {strata : EquationStratification env}
    (P : VEnv → Prop) (base : OriginalCaptureBase env U registry target) (caps : CaptureCaps)
    (cutoff : Nat) (fuel : Nat → Nat) (frontier : List (World strata.rules.length))
    (boxed : OriginalTypeRouteFrameBox env U registry target common commonLeft commonRight) :=
  Σ control : OriginalWorldControls strata boxed.sourceEnv,
  Σ generated : WorldGenerated strata P base caps commonLeft commonRight boxed.graph
      boxed.frame.realization.frame.raw control,
    generated.Controlled frontier × PLift (generated.UsesControlPrefix cutoff fuel) × PLift generated.Replayable × generated.Hereditary frontier

private theorem packet_cast_controls
    {strata : EquationStratification env} {base : OriginalCaptureBase env U registry target}
    {frontier : List (World strata.rules.length)}
    {first second : OriginalTypeRouteFrameBox env U registry target common commonLeft commonRight}
    (same : first = second) (packet : FramePacket P base caps cutoff fuel frontier first) :
    HEq (same ▸ packet : FramePacket P base caps cutoff fuel frontier second).1 packet.1 := by
  cases same
  rfl

private theorem packet_cast_worlds
    {strata : EquationStratification env} {base : OriginalCaptureBase env U registry target}
    {frontier : List (World strata.rules.length)}
    {first second : OriginalTypeRouteFrameBox env U registry target common commonLeft commonRight}
    (same : first = second) (packet : FramePacket P base caps cutoff fuel frontier first) :
    (same ▸ packet : FramePacket P base caps cutoff fuel frontier second).2.1.worlds = packet.2.1.worlds := by
  cases same
  rfl

private theorem table_cast_controls
    {strata : EquationStratification env} {base : OriginalCaptureBase env U registry target}
    {frontier : List (World strata.rules.length)}
    {first second : List (OriginalTypeRouteFrameBox env U registry target common commonLeft commonRight)}
    (same : first = second)
    (table : ∀ i : Fin second.length, FramePacket P base caps cutoff fuel frontier second[i])
    (index : Fin first.length) :
    HEq (((congrArg (fun fs => ∀ i : Fin fs.length, FramePacket P base caps cutoff fuel frontier fs[i]) same).mpr table) index).1
      (table (Fin.cast (congrArg List.length same) index)).1 := by
  cases same
  rfl

private theorem table_cast_worlds
    {strata : EquationStratification env} {base : OriginalCaptureBase env U registry target}
    {frontier : List (World strata.rules.length)}
    {first second : List (OriginalTypeRouteFrameBox env U registry target common commonLeft commonRight)}
    (same : first = second)
    (table : ∀ i : Fin second.length, FramePacket P base caps cutoff fuel frontier second[i])
    (index : Fin first.length) :
    (((congrArg (fun fs => ∀ i : Fin fs.length, FramePacket P base caps cutoff fuel frontier fs[i]) same).mpr table) index).2.1.worlds =
      (table (Fin.cast (congrArg List.length same) index)).2.1.worlds := by
  cases same
  rfl

private noncomputable def transData
    {common : List VExpr}
    {left : OriginalNestedDisplay U common le lt}
    {middle : OriginalNestedDisplay U common me middleAssigned}
    {right : OriginalNestedDisplay U common re rt}
    {strata : EquationStratification env}
    {base : OriginalCaptureBase env U registry target}
    {frontier : List (World strata.rules.length)}
    {first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate}
    {second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final}
    (a : first.ControlledWorldData P base caps cutoff fuel frontier)
    (b : second.ControlledWorldData P base caps cutoff fuel frontier) :
    (first.trans second).ControlledWorldData P base caps cutoff fuel frontier := by
  let Packet := FramePacket (common := common) (commonLeft := commonLeft) (commonRight := commonRight) P base caps cutoff fuel frontier
  have appended : (first.trans second).frames = first.frames ++ second.frames :=
    RawGeneratedTypeRoute.frames.eq_def _
  let selected : ∀ i : Fin (first.trans second).frames.length, Packet ((first.trans second).frames[i]) := by
    intro i
    have bound : i.val < (first.frames ++ second.frames).length := by rw [← appended]; exact i.isLt
    by_cases isLeft : i.val < first.frames.length
    · have same : (first.trans second).frames[i] = first.frames[i.val] := by
        simp only [Fin.getElem_fin, appended]
        exact List.getElem_append_left isLeft
      let j : Fin first.frames.length := ⟨i.val, isLeft⟩
      let packet : Packet (first.frames[j]) :=
        ⟨a.controls j, a.frames j, a.ready j, ⟨a.compatible j⟩, ⟨a.replayable j⟩, a.hereditary j⟩
      exact same.symm ▸ packet
    · have nextBound : i.val - first.frames.length < second.frames.length := by
        simp only [List.length_append] at bound
        omega
      have same : (first.trans second).frames[i] = second.frames[i.val - first.frames.length] := by
        simp only [Fin.getElem_fin, appended]
        exact List.getElem_append_right (Nat.le_of_not_lt isLeft)
      let j : Fin second.frames.length := ⟨i.val - first.frames.length, nextBound⟩
      let packet : Packet (second.frames[j]) :=
        ⟨b.controls j, b.frames j, b.ready j, ⟨b.compatible j⟩, ⟨b.replayable j⟩, b.hereditary j⟩
      exact same.symm ▸ packet
  exact ⟨RetainedHeaderUniverse.source_trans a.generated b.generated,
    trans_worldInputs a.inputs b.inputs,
    fun i => (selected i).1,
    fun i => (selected i).2.1,
    fun i => (selected i).2.2.1,
    fun i => (selected i).2.2.2.1.down,
    fun i => (selected i).2.2.2.2.1.down,
    fun i => (selected i).2.2.2.2.2⟩

private theorem transData_left
    {common : List VExpr}
    {left : OriginalNestedDisplay U common le lt}
    {middle : OriginalNestedDisplay U common me middleAssigned}
    {right : OriginalNestedDisplay U common re rt}
    {strata : EquationStratification env} {base : OriginalCaptureBase env U registry target}
    {frontier : List (World strata.rules.length)}
    {first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate}
    {second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final}
    (a : first.ControlledWorldData P base caps cutoff fuel frontier)
    (b : second.ControlledWorldData P base caps cutoff fuel frontier)
    (index : Fin first.frames.length) :
    HEq ((transData a b).controls (RawGeneratedTypeRoute.WorldBoundary.transLeftIndex first second index)) (a.controls index) ∧
    ((transData a b).frames (RawGeneratedTypeRoute.WorldBoundary.transLeftIndex first second index)).worlds =
      (a.frames index).worlds := by
  constructor
  · simp only [transData, RawGeneratedTypeRoute.WorldBoundary.transLeftIndex, dif_pos index.isLt]
    exact packet_cast_controls _ _
  · simp only [transData, RawGeneratedTypeRoute.WorldBoundary.transLeftIndex]
    rw [dif_pos index.isLt]
    exact packet_cast_worlds _ _

private theorem transData_right
    {common : List VExpr}
    {left : OriginalNestedDisplay U common le lt}
    {middle : OriginalNestedDisplay U common me middleAssigned}
    {right : OriginalNestedDisplay U common re rt}
    {strata : EquationStratification env} {base : OriginalCaptureBase env U registry target}
    {frontier : List (World strata.rules.length)}
    {first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate}
    {second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final}
    (a : first.ControlledWorldData P base caps cutoff fuel frontier)
    (b : second.ControlledWorldData P base caps cutoff fuel frontier)
    (index : Fin second.frames.length) :
    HEq ((transData a b).controls (RawGeneratedTypeRoute.WorldBoundary.transRightIndex first second index)) (b.controls index) ∧
    ((transData a b).frames (RawGeneratedTypeRoute.WorldBoundary.transRightIndex first second index)).worlds =
      (b.frames index).worlds := by
  have notLeft : ¬ first.frames.length + index.val < first.frames.length := by omega
  constructor
  · simp only [transData, RawGeneratedTypeRoute.WorldBoundary.transRightIndex, dif_neg notLeft]
    have sameIndex : (⟨first.frames.length + index.val - first.frames.length, by
        have := index.isLt; omega⟩ : Fin second.frames.length) = index := by
      apply Fin.ext
      simp only [Nat.add_sub_cancel_left]
    have controlsEq (i j : Fin second.frames.length) (same : i = j) : HEq (b.controls i) (b.controls j) := by
      cases same
      rfl
    exact (packet_cast_controls _ _).trans (controlsEq _ _ sameIndex)
  · simp only [transData, RawGeneratedTypeRoute.WorldBoundary.transRightIndex]
    rw [dif_neg notLeft]
    have sameIndex : (⟨first.frames.length + index.val - first.frames.length, by
        have := index.isLt; omega⟩ : Fin second.frames.length) = index := by
      apply Fin.ext
      simp only [Nat.add_sub_cancel_left]
    exact (packet_cast_worlds _ _).trans (congrArg (fun i => (b.frames i).worlds) sameIndex)

private theorem transData_coherent
    {common : List VExpr}
    {left : OriginalNestedDisplay U common le lt}
    {middle : OriginalNestedDisplay U common me middleAssigned}
    {right : OriginalNestedDisplay U common re rt}
    {strata : EquationStratification env} {base : OriginalCaptureBase env U registry target}
    {frontier : List (World strata.rules.length)}
    {first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate}
    {second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final}
    (a : first.ControlledWorldData P base caps cutoff fuel frontier)
    (b : second.ControlledWorldData P base caps cutoff fuel frontier)
    {lc : OriginalWorldControls strata left.sourceEnv} {mc : OriginalWorldControls strata middle.sourceEnv}
    {rc : OriginalWorldControls strata right.sourceEnv}
    {lw : WorldEnvironmentProvenance strata U initial} {mw : WorldEnvironmentProvenance strata U intermediate}
    {rw : WorldEnvironmentProvenance strata U final}
    (before : first.WorldBoundary a.inputs lc mc lw mw)
    (after : second.WorldBoundary b.inputs mc rc mw rw)
    (beforeCoherent : before.FrameOccurrenceCoherent a.controls a.frames)
    (afterCoherent : after.FrameOccurrenceCoherent b.controls b.frames) :
    (before.trans after).FrameOccurrenceCoherent (transData a b).controls (transData a b).frames := by
  apply RawGeneratedTypeRoute.WorldBoundary.FrameOccurrenceCoherent.trans before after
  · intro index
    refine ⟨(transData_left a b index).1.trans (beforeCoherent index).1, ?_⟩
    rw [(transData_left a b index).2]
    exact (beforeCoherent index).2
  · intro index
    refine ⟨(transData_right a b index).1.trans (afterCoherent index).1, ?_⟩
    rw [(transData_right a b index).2]
    exact (afterCoherent index).2

private noncomputable def sameData
    {strata : EquationStratification env}
    {base : OriginalCaptureBase env U registry target}
    {frontier : List (World strata.rules.length)}
    (left : OriginalNestedDisplay U common expression leftAssigned)
    (right : OriginalNestedDisplay U common expression rightAssigned)
    (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered) (initial : List Closure)
    (frame : OriginalTypeRouteFrame env registry target right.graph commonLeft commonRight)
    (lc : OriginalWorldControls strata left.sourceEnv) (rc : OriginalWorldControls strata right.sourceEnv)
    (li : WorldEnvironmentProvenance strata U initial)
    (ri : WorldEnvironmentProvenance strata U (frame.realization.frame.dependencyEnvironment rf))
    (world : WorldGenerated strata P base caps commonLeft commonRight right.graph frame.realization.frame.raw rc)
    (ready : world.Controlled frontier) (compatible : world.UsesControlPrefix cutoff fuel)
    (replayable : world.Replayable)
    (hereditary : world.Hereditary frontier)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) world.worlds ri.worlds)
    (generated : (RawGeneratedTypeRoute.same left right lf rf initial frame).SourceGenerated P base caps) :
    (RawGeneratedTypeRoute.same left right lf rf initial frame).ControlledWorldData P base caps cutoff fuel frontier := by
  let route := RawGeneratedTypeRoute.same left right lf rf initial frame
  have singleton : route.frames = [frame.box] := RawGeneratedTypeRoute.frames.eq_def _
  let Packet := FramePacket (common := common) (commonLeft := commonLeft) (commonRight := commonRight) P base caps cutoff fuel frontier
  let selected : ∀ i : Fin route.frames.length, Packet (route.frames[i]) := by
    intro i
    have same : route.frames[i] = frame.box := by
      have member := List.getElem_mem (l := route.frames) i.isLt
      exact List.mem_singleton.mp ((congrArg (fun xs => route.frames[i] ∈ xs) singleton).mp member)
    let packet : Packet frame.box := ⟨rc, world, ready, ⟨compatible⟩, ⟨replayable⟩, hereditary⟩
    exact same.symm ▸ packet
  exact ⟨generated, (lc, rc, li, ri),
    fun i => (selected i).1,
    fun i => (selected i).2.1,
    fun i => (selected i).2.2.1,
    fun i => (selected i).2.2.2.1.down,
    fun i => (selected i).2.2.2.2.1.down,
    fun i => (selected i).2.2.2.2.2⟩

private theorem sameData_coherent
    {strata : EquationStratification env}
    {base : OriginalCaptureBase env U registry target}
    {frontier : List (World strata.rules.length)}
    (left : OriginalNestedDisplay U common expression leftAssigned)
    (right : OriginalNestedDisplay U common expression rightAssigned)
    (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered) (initial : List Closure)
    (frame : OriginalTypeRouteFrame env registry target right.graph commonLeft commonRight)
    (lc : OriginalWorldControls strata left.sourceEnv) (rc : OriginalWorldControls strata right.sourceEnv)
    (li : WorldEnvironmentProvenance strata U initial)
    (ri : WorldEnvironmentProvenance strata U (frame.realization.frame.dependencyEnvironment rf))
    (world : WorldGenerated strata P base caps commonLeft commonRight right.graph frame.realization.frame.raw rc)
    (ready : world.Controlled frontier) (compatible : world.UsesControlPrefix cutoff fuel)
    (replayable : world.Replayable)
    (hereditary : world.Hereditary frontier)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) world.worlds ri.worlds)
    (generated : (RawGeneratedTypeRoute.same left right lf rf initial frame).SourceGenerated P base caps)
    (matching : lc.cutoff = rc.cutoff ∧ lc.fuel = rc.fuel) :
    (RawGeneratedTypeRoute.WorldBoundary.same left right lf rf frame lc rc li ri matching).FrameOccurrenceCoherent
      (sameData left right lf rf initial frame lc rc li ri world ready compatible replayable hereditary covered generated).controls
      (sameData left right lf rf initial frame lc rc li ri world ready compatible replayable hereditary covered generated).frames := by
  let data := sameData left right lf rf initial frame lc rc li ri world ready compatible replayable hereditary covered generated
  let boundary := RawGeneratedTypeRoute.WorldBoundary.same left right lf rf frame lc rc li ri matching
  intro index
  have sameControls : HEq (data.controls index) rc := by
    dsimp only [data, sameData]
    exact packet_cast_controls _ _
  have sameWorlds : (data.frames index).worlds = world.worlds := by
    dsimp only [data, sameData]
    exact packet_cast_worlds _ _
  have sameOccurrence : boundary.frameAt index = ⟨frame.box, rc, ri⟩ := by
    exact List.mem_singleton.mp (boundary.frameAt_mem index)
  let predicate := fun occurrence : WorldBoundaryFrame env U registry target common commonLeft commonRight strata =>
    HEq (data.controls index) occurrence.controls ∧
    Covered (@EquationControlMeasure.Less strata.rules.length) (data.frames index).worlds occurrence.world.worlds
  apply (congrArg predicate sameOccurrence).mpr
  exact ⟨sameControls, sameWorlds ▸ covered⟩

private theorem environmentCast_heq
    {strata : EquationStratification env} {first second : List Closure}
    (same : first = second) (world : WorldEnvironmentProvenance strata U first) :
    HEq (same ▸ world : WorldEnvironmentProvenance strata U second) world := by
  cases same
  rfl

private theorem environmentCast_worlds
    {strata : EquationStratification env} {first second : List Closure}
    (same : first = second) (world : WorldEnvironmentProvenance strata U first) :
    (same ▸ world : WorldEnvironmentProvenance strata U second).worlds = world.worlds := by
  cases same
  rfl

private theorem callWorld_cast
    {strata : EquationStratification env} {first second : List Closure}
    (controls : OriginalWorldControls strata sourceEnv) (phase : RichPhase)
    (node : EndpointState sourceEnv U source expression assigned)
    (same : first = second) (world : WorldEnvironmentProvenance strata U first) :
    originalCallWorld controls phase node (same ▸ world) = originalCallWorld controls phase node world := by
  cases same
  rfl

private theorem boundary_world_coherent
    {strata : EquationStratification env} {base : OriginalCaptureBase env U registry target}
    {frontier : List (World strata.rules.length)}
    {left : OriginalNestedDisplay U common firstExpression firstType}
    {right : OriginalNestedDisplay U common lastExpression lastType}
    {route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final}
    (data : route.ControlledWorldData P base caps cutoff fuel frontier)
    {lc : OriginalWorldControls strata left.sourceEnv} {rc : OriginalWorldControls strata right.sourceEnv}
    {lw : WorldEnvironmentProvenance strata U initial} {rw nextWorld : WorldEnvironmentProvenance strata U final}
    (boundary : route.WorldBoundary data.inputs lc rc lw rw)
    (coherent : boundary.FrameOccurrenceCoherent data.controls data.frames)
    (same : rw = nextWorld) :
    (same ▸ boundary : route.WorldBoundary data.inputs lc rc lw nextWorld).FrameOccurrenceCoherent data.controls data.frames := by
  cases same
  exact coherent

private theorem finalTransport
    {strata : EquationStratification env}
    {base : OriginalCaptureBase env U registry target}
    {frontier : List (World strata.rules.length)}
    {left : OriginalNestedDisplay U common firstExpression firstType}
    {right : OriginalNestedDisplay U common lastExpression lastType}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final)
    (data : route.ControlledWorldData P base caps cutoff fuel frontier)
    {lc : OriginalWorldControls strata left.sourceEnv} {rc : OriginalWorldControls strata right.sourceEnv}
    {lw : WorldEnvironmentProvenance strata U initial} {rw : WorldEnvironmentProvenance strata U final}
    (boundary : route.WorldBoundary data.inputs lc rc lw rw)
    (coherent : boundary.FrameOccurrenceCoherent data.controls data.frames)
    (equal : final = nextFinal) :
    ∃ nextRoute : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial nextFinal,
      ∃ nextData : nextRoute.ControlledWorldData P base caps cutoff fuel frontier,
        nextRoute.reserve = route.reserve ∧
        (nextRoute.worldReserve nextData.inputs).worlds = (route.worldReserve data.inputs).worlds ∧
        ∃ nextBoundary : nextRoute.WorldBoundary nextData.inputs lc rc lw (equal ▸ rw),
          nextBoundary.FrameOccurrenceCoherent nextData.controls nextData.frames := by
  cases equal
  exact ⟨route, data, rfl, rfl, boundary, coherent⟩

private theorem rightTransport
    {strata : EquationStratification env}
    {base : OriginalCaptureBase env U registry target}
    {frontier : List (World strata.rules.length)}
    {first : OriginalNestedDisplay U common firstExpression firstType}
    {last : OriginalNestedDisplay U common lastExpression lastType}
    {next : OriginalNestedDisplay U common nextExpression lastType}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight first last initial final)
    (data : route.ControlledWorldData P base caps cutoff fuel frontier)
    {lc : OriginalWorldControls strata first.sourceEnv} {rc : OriginalWorldControls strata last.sourceEnv}
    {lw : WorldEnvironmentProvenance strata U initial} {rw : WorldEnvironmentProvenance strata U final}
    (boundary : route.WorldBoundary data.inputs lc rc lw rw)
    (coherent : boundary.FrameOccurrenceCoherent data.controls data.frames)
    (expressionEq : lastExpression = nextExpression) (endpointEq : HEq last next)
    (sourceEq : next.sourceEnv = last.sourceEnv) :
    ∃ nextRoute : RawGeneratedTypeRoute env registry target commonLeft commonRight first next initial final,
      ∃ nextData : nextRoute.ControlledWorldData P base caps cutoff fuel frontier,
        nextRoute.reserve = route.reserve ∧
        (nextRoute.worldReserve nextData.inputs).worlds = (route.worldReserve data.inputs).worlds ∧
        ∃ nextBoundary : nextRoute.WorldBoundary nextData.inputs lc (sourceEq.symm ▸ rc) lw rw,
          nextBoundary.FrameOccurrenceCoherent nextData.controls nextData.frames := by
  cases expressionEq
  cases eq_of_heq endpointEq
  exact ⟨route, data, rfl, rfl, boundary, coherent⟩

private theorem same_worlds
    {strata : EquationStratification env}
    (left : OriginalNestedDisplay U common expression leftAssigned)
    (right : OriginalNestedDisplay U common expression rightAssigned)
    (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered) (initial : List Closure)
    (frame : OriginalTypeRouteFrame env registry target right.graph commonLeft commonRight)
    (lc : OriginalWorldControls strata left.sourceEnv) (rc : OriginalWorldControls strata right.sourceEnv)
    (li : WorldEnvironmentProvenance strata U initial)
    (ri : WorldEnvironmentProvenance strata U (frame.realization.frame.dependencyEnvironment rf)) :
    ((RawGeneratedTypeRoute.same left right lf rf initial frame).worldReserve (lc, rc, li, ri)).worlds =
      [originalCallWorld lc .expressionReindex left.node li, originalCallWorld rc .expressionReindex right.node ri] := by
  simp only [RawGeneratedTypeRoute.worldReserve, RawGeneratedTypeRoute.WorldInputs]
  rw [environment_worlds_mpr (RawGeneratedTypeRoute.reserve.eq_def
    (RawGeneratedTypeRoute.same left right lf rf initial frame))]
  rfl

section
variable
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  {major : EndpointRef sourceEnv U source majorExpression majorType}
  (initial : ContextDerivation sourceEnv U source)
  (domain : EndpointRef sourceEnv U source A (.sort u))
  (body : EndpointState sourceEnv U (A :: source) B (.sort v))
  (function : EndpointState sourceEnv U source f (.forallE A B))
  (argument : EndpointState sourceEnv U source a A)
  (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
  (hu : u.WF U) (hv : v.WF U)
  (location : Located major (.app hu hv (.ref domain) body function argument result))
  (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
  {right : OriginalPiTypeRouteSide U common}
  (history : OriginalApplyPiHistory env registry target commonLeft commonRight
    (originalApplicationTypeRouteSide initial domain body function argument result hu hv location graph) right)

/-- The concrete stored seed route retains its actual world inputs and
all controlled frame children through zero-scope weakening. -/
theorem OriginalApplyPiHistory.argumentSeedHistoryWorld
    {strata : EquationStratification env}
    {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
    (sourceControls : OriginalWorldControls strata sourceEnv)
    (headerControls : OriginalWorldControls strata right.sourceEnv)
    (frontier : List (World strata.rules.length))
    (noBinders : location.binderPrefix = [])
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (query : RichObs sourceEnv env U registry target argument history.sourceFrame.locals
      (raw.comp commonLeft) (input : Profile n) footprint)
    (resources : footprint.Available history.sourceFrame.available)
    (sourceWorld : WorldGenerated strata P base commonCaps commonLeft commonRight graph
      history.sourceFrame.realization.frame.raw sourceControls)
    (headerWorld : WorldGenerated strata P base commonCaps commonLeft commonRight right.graph
      history.headerFrame.realization.frame.raw headerControls)
    (sourceBaseline : WorldEnvironmentProvenance strata U
      (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered))
    (headerBaseline : WorldEnvironmentProvenance strata U history.final)
    (sourceCovered : Covered (@EquationControlMeasure.Less strata.rules.length) sourceWorld.worlds sourceBaseline.worlds)
    (headerCovered : Covered (@EquationControlMeasure.Less strata.rules.length) headerWorld.worlds headerBaseline.worlds)
    (sourceReplayable : sourceWorld.Replayable)
    (headerReplayable : headerWorld.Replayable)
    (sourceReady : sourceWorld.Controlled frontier)
    (headerReady : headerWorld.Controlled frontier)
    (sourceHereditary : sourceWorld.Hereditary frontier)
    (headerHereditary : headerWorld.Hereditary frontier)
    (sourceCompatible : sourceWorld.UsesControlPrefix sourceControls.cutoff sourceControls.fuel)
    (headerCompatible : headerWorld.UsesControlPrefix sourceControls.cutoff sourceControls.fuel)
    (whole : history.whole.ControlledWorldData P base commonCaps sourceControls.cutoff sourceControls.fuel frontier)
    (wholeBoundary : history.whole.WorldBoundary whole.inputs sourceControls headerControls
      sourceBaseline headerBaseline)
    (wholeCoherent : wholeBoundary.FrameOccurrenceCoherent whole.controls whole.frames) :
    ∃ next : OriginalSeedTypeHistory
        (history.argumentSeed (field := field) initial domain body function argument result hu hv location graph
          noBinders sourceBound query resources)
        (history.argumentSeedScope initial domain body function argument result hu hv location graph
          noBinders sourceBound query resources)
        right.graph (history.headerDomainProvenance initial domain body function argument result hu hv location graph)
        history.headerFrame.realization history.leftOrdered history.rightOrdered,
      ∃ data : next.route.ControlledWorldData P base commonCaps sourceControls.cutoff sourceControls.fuel frontier,
        next.route.reserve = history.argumentSeedReserve ∧
        (next.route.worldReserve data.inputs).worlds =
          [originalCallWorld sourceControls .expressionReindex argument.typeFormation.node sourceBaseline,
           originalCallWorld sourceControls .expressionReindex (.ref domain) sourceBaseline] ++
          (history.whole.worldReserve whole.inputs).worlds ++
          [originalCallWorld headerControls .expressionReindex right.domain headerBaseline,
           originalCallWorld headerControls .expressionReindex (.ref history.rightDomain) headerBaseline] ∧
        ∃ boundary : next.route.WorldBoundary data.inputs sourceControls headerControls
            sourceBaseline headerBaseline,
          boundary.FrameOccurrenceCoherent data.controls data.frames := by
  let seed := history.argumentSeed (field := field) initial domain body function argument result hu hv location graph
    noBinders sourceBound query resources
  let scope := history.argumentSeedScope (field := field) initial domain body function argument result hu hv location graph
    noBinders sourceBound query resources
  let provenance := history.headerDomainProvenance initial domain body function argument result hu hv location graph
  let weakening : WorldGenerated strata P base commonCaps commonLeft commonRight (.weaken right.graph (.refl (Γ := common)))
      history.headerFrame.realization.frame.raw headerControls := .weaken headerWorld .refl rfl rfl rfl
  have weakReady : weakening.Controlled frontier :=
    ⟨headerReady.annotation, headerReady.within, headerReady.sponsored⟩
  have weakCompatible : weakening.UsesControlPrefix sourceControls.cutoff sourceControls.fuel := headerCompatible
  have headerPrefix := headerCompatible.controls_match
  have weakOwnCompatible : weakening.UsesControlPrefix headerControls.cutoff headerControls.fuel := by
    rw [headerPrefix.1, headerPrefix.2]
    exact weakCompatible
  obtain ⟨header, headerActual, headerWorlds, ⟨headerActualReady⟩, _headerCompatible, environmentEq, _replayableEq, headerAnnotationEq, ⟨headerActualHereditary⟩⟩ :=
    realizeWorld history.headerFrame.realization.frame weakening weakReady weakOwnCompatible
      (headerHereditary.weaken .refl rfl rfl rfl)
      history.headerFrame.realization.substitutions
  let destination : OriginalNestedDisplay U common (right.A.subst right.raw) (.sort right.u) := {
    sourceEnv := right.sourceEnv, source := right.source, sourceExpression := right.A, sourceType := .sort right.u
    context := right.location.contextDerivation right.initial, node := .ref history.rightDomain
    provenance := provenance, raw := right.raw.lift_r .refl
    graph := .weaken right.graph .refl
    expression_eq := by rw [← lift'_subst, lift'_refl]
    type_eq := rfl }
  let destinationFrame : OriginalTypeRouteFrame env registry target destination.graph commonLeft commonRight :=
    ⟨history.headerFrame.locals, history.headerFrame.available, header, history.headerFrame.closed⟩
  let destinationBaseline : WorldEnvironmentProvenance strata U
      (destinationFrame.realization.frame.dependencyEnvironment history.rightOrdered) :=
    (environmentEq history.rightOrdered).symm ▸ headerBaseline
  have destinationCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
      headerActual.worlds destinationBaseline.worlds := by
    rw [show destinationBaseline.worlds = headerBaseline.worlds from
      environmentCast_worlds (environmentEq history.rightOrdered).symm headerBaseline, headerWorlds]
    exact headerCovered
  let left := originalApplicationTypeRouteSide initial domain body function argument result hu hv location graph
  let first := RawGeneratedTypeRoute.same left.argumentDisplay.formationDisplay left.pi.domainDisplay
    history.leftOrdered history.leftOrdered (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered) history.sourceFrame
  have firstGenerated : first.SourceGenerated P base commonCaps :=
    RetainedHeaderUniverse.source_same _ _ rfl _ _ _ _
      sourceWorld.erase.ambientGenerated.ambient.2.below sourceWorld.erase.ambientGenerated.ambient.2.below
      sourceWorld.erase.sources.1.source sourceWorld.erase.sources.1.source sourceWorld.erase
  let firstData := sameData left.argumentDisplay.formationDisplay left.pi.domainDisplay
    history.leftOrdered history.leftOrdered _ history.sourceFrame
    sourceControls sourceControls sourceBaseline sourceBaseline sourceWorld sourceReady sourceCompatible sourceReplayable sourceHereditary sourceCovered firstGenerated
  let firstBoundary := RawGeneratedTypeRoute.WorldBoundary.same left.argumentDisplay.formationDisplay left.pi.domainDisplay
    history.leftOrdered history.leftOrdered history.sourceFrame sourceControls sourceControls
    sourceBaseline sourceBaseline ⟨rfl, rfl⟩
  have firstCoherent : firstBoundary.FrameOccurrenceCoherent firstData.controls firstData.frames :=
    sameData_coherent left.argumentDisplay.formationDisplay left.pi.domainDisplay
      history.leftOrdered history.leftOrdered _ history.sourceFrame sourceControls sourceControls
      sourceBaseline sourceBaseline sourceWorld sourceReady sourceCompatible sourceReplayable sourceHereditary sourceCovered firstGenerated ⟨rfl, rfl⟩
  let middle := RawGeneratedTypeRoute.piDomain left.pi right history.leftBelow history.whole
  have middleGenerated : middle.SourceGenerated P base commonCaps := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp only [middle]; rw [RawGeneratedTypeRoute.WellFormed.eq_def]; exact whole.generated.wellFormed
    · dsimp only [middle]; rw [RawGeneratedTypeRoute.Ambient.eq_def]; exact whole.generated.ambient
    · dsimp only [middle]; rw [RawGeneratedTypeRoute.AllSources.eq_def]
      exact ⟨whole.generated.sources.left, whole.generated.sources.right, whole.generated.sources⟩
    · dsimp only [middle]; rw [RawGeneratedTypeRoute.frames.eq_def]; exact whole.generated.frames
  have middleFrames : middle.frames = history.whole.frames := by
    dsimp only [middle]; rw [RawGeneratedTypeRoute.frames.eq_def]
  let Packet := FramePacket (common := common) (commonLeft := commonLeft) (commonRight := commonRight)
    P base commonCaps sourceControls.cutoff sourceControls.fuel frontier
  let oldEntries : ∀ i : Fin history.whole.frames.length, Packet (history.whole.frames[i]) :=
    fun i => ⟨whole.controls i, whole.frames i, whole.ready i, ⟨whole.compatible i⟩, ⟨whole.replayable i⟩, whole.hereditary i⟩
  let entries : ∀ i : Fin middle.frames.length, Packet (middle.frames[i]) :=
    (congrArg (fun frames => ∀ i : Fin frames.length, Packet (frames[i])) middleFrames).mpr oldEntries
  let middleData : middle.ControlledWorldData P base commonCaps sourceControls.cutoff sourceControls.fuel frontier :=
    ⟨middleGenerated, whole.inputs,
      fun i => (entries i).1,
      fun i => (entries i).2.1,
      fun i => (entries i).2.2.1,
      fun i => (entries i).2.2.2.1.down,
      fun i => (entries i).2.2.2.2.1.down,
      fun i => (entries i).2.2.2.2.2⟩

  let middleBoundary := RawGeneratedTypeRoute.WorldBoundary.piDomain left.pi right history.leftBelow wholeBoundary
  have middleCoherent : middleBoundary.FrameOccurrenceCoherent middleData.controls middleData.frames := by
    intro index
    let oldIndex := Fin.cast (congrArg List.length middleFrames) index
    have sameOccurrence : middleBoundary.frameAt index = wholeBoundary.frameAt oldIndex := by
      unfold RawGeneratedTypeRoute.WorldBoundary.frameAt
      rfl
    have controlsEq : HEq (middleData.controls index) (whole.controls oldIndex) :=
      table_cast_controls middleFrames oldEntries index
    have worldsEq : (middleData.frames index).worlds = (whole.frames oldIndex).worlds :=
      table_cast_worlds middleFrames oldEntries index
    let predicate := fun occurrence : WorldBoundaryFrame env U registry target common commonLeft commonRight strata =>
      HEq (middleData.controls index) occurrence.controls ∧
        Covered (@EquationControlMeasure.Less strata.rules.length) (middleData.frames index).worlds occurrence.world.worlds
    apply (congrArg predicate sameOccurrence).mpr
    refine ⟨controlsEq.trans (wholeCoherent oldIndex).1, ?_⟩
    rw [worldsEq]
    exact (wholeCoherent oldIndex).2

  let last := RawGeneratedTypeRoute.same right.domainDisplay destination history.rightOrdered history.rightOrdered
    history.final destinationFrame
  have lastGenerated : last.SourceGenerated P base commonCaps :=
    RetainedHeaderUniverse.source_same _ _ rfl _ _ _ _
      headerWorld.erase.ambientGenerated.ambient.2.below headerActual.erase.ambientGenerated.ambient.2.below
      headerWorld.erase.sources.1.source headerActual.erase.sources.1.source headerActual.erase
  have headerActualCompatible : headerActual.UsesControlPrefix sourceControls.cutoff sourceControls.fuel := by
    have same := headerCompatible.controls_match
    simpa only [same.1, same.2] using _headerCompatible
  let lastData := sameData right.domainDisplay destination
    history.rightOrdered history.rightOrdered _ destinationFrame
    headerControls headerControls headerBaseline destinationBaseline headerActual headerActualReady headerActualCompatible
      (_replayableEq.mpr headerReplayable) headerActualHereditary destinationCovered lastGenerated
  let combined := (first.trans middle).trans last
  let data := transData (transData firstData middleData) lastData
  let lastBoundary := RawGeneratedTypeRoute.WorldBoundary.same right.domainDisplay destination
    history.rightOrdered history.rightOrdered destinationFrame headerControls headerControls
    headerBaseline destinationBaseline ⟨rfl, rfl⟩
  have lastCoherent : lastBoundary.FrameOccurrenceCoherent lastData.controls lastData.frames :=
    sameData_coherent right.domainDisplay destination history.rightOrdered history.rightOrdered _ destinationFrame
      headerControls headerControls headerBaseline destinationBaseline headerActual headerActualReady headerActualCompatible
      (_replayableEq.mpr headerReplayable) headerActualHereditary destinationCovered lastGenerated ⟨rfl, rfl⟩
  let combinedBoundary := (firstBoundary.trans middleBoundary).trans lastBoundary
  have combinedCoherent : combinedBoundary.FrameOccurrenceCoherent data.controls data.frames :=
    transData_coherent (transData firstData middleData) lastData _ _
      (transData_coherent firstData middleData _ _ firstCoherent middleCoherent) lastCoherent
  have reserveEq : combined.reserve = history.argumentSeedReserve := by
    change (history.argumentDomainRoute.trans last).reserve = _
    rw [RawGeneratedTypeRoute.reserve.eq_def]
    change history.argumentDomainRoute.reserve ++ last.reserve = history.argumentSeedReserve
    unfold OriginalApplyPiHistory.argumentSeedReserve
    congr 1
    rw [RawGeneratedTypeRoute.reserve.eq_def last]
    simp only [last, destinationFrame, destination, OriginalPiTypeRouteSide.domainDisplay,
      OriginalNestedDisplay.ofOccurrence, EndpointState.dependencyOrigin]
    rw [environmentEq history.rightOrdered]
    rfl
  have worldsEq : (combined.worldReserve data.inputs).worlds =
      [originalCallWorld sourceControls .expressionReindex argument.typeFormation.node sourceBaseline,
       originalCallWorld sourceControls .expressionReindex (.ref domain) sourceBaseline] ++
      (history.whole.worldReserve whole.inputs).worlds ++
      [originalCallWorld headerControls .expressionReindex right.domain headerBaseline,
       originalCallWorld headerControls .expressionReindex (.ref history.rightDomain) headerBaseline] := by
    change ((first.trans middle).trans last |>.worldReserve (trans_worldInputs
      (trans_worldInputs firstData.inputs middleData.inputs) lastData.inputs)).worlds = _
    rw [trans_worldReserve, trans_worldReserve]
    rw [show (middle.worldReserve middleData.inputs).worlds = (history.whole.worldReserve whole.inputs).worlds by
      simp only [middle, middleData, RawGeneratedTypeRoute.worldReserve, RawGeneratedTypeRoute.WorldInputs]
      rw [environment_worlds_mpr (RawGeneratedTypeRoute.reserve.eq_def middle)]
      rfl]
    change (first.worldReserve (sourceControls, sourceControls, sourceBaseline, sourceBaseline)).worlds ++
      (history.whole.worldReserve whole.inputs).worlds ++
      (last.worldReserve (headerControls, headerControls, headerBaseline, destinationBaseline)).worlds = _
    rw [same_worlds, same_worlds]
    have lastWorldEq : originalCallWorld headerControls .expressionReindex (.ref history.rightDomain)
        destinationBaseline = originalCallWorld headerControls .expressionReindex
          (.ref history.rightDomain) headerBaseline :=
      callWorld_cast headerControls .expressionReindex (.ref history.rightDomain)
        (environmentEq history.rightOrdered).symm headerBaseline
    change _ ++ _ ++ [_, originalCallWorld headerControls .expressionReindex _ destinationBaseline] = _
    rw [lastWorldEq]
    rfl
  have finalEq : header.frame.dependencyEnvironment history.rightOrdered = history.final := environmentEq history.rightOrdered
  obtain ⟨route, routeData, exactReserve, sameWorlds, routeBoundary, routeCoherent⟩ :=
    finalTransport combined data combinedBoundary combinedCoherent finalEq
  have finalWorldEq : (finalEq ▸ destinationBaseline : WorldEnvironmentProvenance strata U history.final) = headerBaseline :=
    eq_of_heq ((environmentCast_heq finalEq destinationBaseline).trans
      (environmentCast_heq finalEq.symm headerBaseline))
  let routeBoundary' : route.WorldBoundary routeData.inputs sourceControls headerControls
      sourceBaseline headerBaseline := finalWorldEq ▸ routeBoundary
  have routeCoherent' : routeBoundary'.FrameOccurrenceCoherent routeData.controls routeData.frames :=
    boundary_world_coherent routeData routeBoundary routeCoherent finalWorldEq
  have endpointEq : HEq destination (scope.declaredTypeDisplay right.graph provenance) := by
    dsimp only [destination, scope, OriginalApplyPiHistory.argumentSeedScope,
      OriginalOwnerScope.declaredTypeDisplay, seed, OriginalApplyPiHistory.argumentSeed, Lift.skipN]
    exact nestedDisplay_heq _ _ _ _ _ _ _
  obtain ⟨nextRoute, nextData, nextReserve, nextWorlds, nextBoundary, nextCoherent⟩ :=
    rightTransport route routeData routeBoundary' routeCoherent' lift'_refl.symm endpointEq rfl
  exact ⟨⟨nextRoute⟩, nextData, nextReserve.trans (exactReserve.trans reserveEq),
    nextWorlds.trans (sameWorlds.trans worldsEq), nextBoundary, nextCoherent⟩
end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
