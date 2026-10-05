import Lean4Lean.Theory.Typing.AnchoredOriginalWorldEmptyArgumentCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFormalHeaderTransplant
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private Located.dependencyEnvironment_of_prefix_nil from Lean4Lean.Theory.Typing.AnchoredOriginalFamilyArgumentPair
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

theorem FormalFamilyDestination.captureFirstArgumentWorld
    {major : EndpointRef sourceEnv U source rootExpression rootType}
    (initial : ContextDerivation sourceEnv U source)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (function : EndpointState sourceEnv U source (.const name levels) (.forallE A B))
    (argument : EndpointState sourceEnv U source a A)
    (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (location : Located major (.app hu hv (.ref domain) body function argument result))
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    {strata : EquationStratification env} {P : VEnv → Prop}
    (controls : OriginalWorldControls strata sourceEnv) (below : sourceEnv ≤ env)
    (sourceWorld : WorldEnvironmentProvenance strata U (frame.realization.frame.dependencyEnvironment controls.ordered))
    (origin : ProjectionParameterOrigin sourceEnv name info)
    {signature : ConstantTelescope (origin.family.type.instL levels)}
    {domains : signature.domains = [C,D]}
    (destination : FormalFamilyDestination (U := U) origin signature domains)
    (familyOrigin : ConstantHeaderOrigin sourceEnv name origin.family.toVConstant)
    (queryWF : ∀ level ∈ levels, level.WF U)
    (shape : origin.family.type.instL levels = .forallE C (.forallE D signature.result))
    {base : OriginalCaptureBase env U registry target} (caps : CaptureCaps)
    (frontier : List (World strata.rules.length))
    (generation : WorldGenerated strata P base caps commonLeft commonRight graph frame.realization.frame.raw controls)
    (ready : generation.Controlled frontier)
    (compatible : generation.UsesControlPrefix controls.cutoff controls.fuel)
    (replayable : generation.Replayable) (hereditary : generation.Hereditary frontier)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) generation.worlds sourceWorld.worlds)
    (headerSource : P familyOrigin.source) (typesSource : P origin.types)
    (outer : EndpointState sourceEnv U source (.proj projectedName index displayedMajor) outerType)
    (head : OriginalFactorCut.ProjectionHead outer)
    (field : EndpointRef sourceEnv U source head.fieldType (.sort head.fieldLevel))
    (fieldEq : head.field = .ref field)
    (rootLocation : Located (.right head.major) (.ref major))
    (initialWorld : WorldEnvironmentProvenance strata U ownerInitial)
    (sourceEnvironment : ∀ ordered, frame.realization.frame.dependencyEnvironment ordered = ownerInitial)
    (sourceWorlds : sourceWorld.worlds = initialWorld.worlds)
    (outerWorld : WorldEnvironmentProvenance strata U outerEnvironment)
    (sourceCapacity : environmentCost (frame.realization.frame.dependencyEnvironment controls.ordered) ≤ environmentCost outerEnvironment)
    (sourceCoveredOuter : Covered (@EquationControlMeasure.Less strata.rules.length) sourceWorld.worlds outerWorld.worlds)
    (outerPaid : Sponsored frontier [originalCallWorld controls .assignedComparison outer outerWorld])
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (bank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .assignedComparison outer outerWorld]))
    (unary : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .assignedComparison outer outerWorld])) :
    ∃ history : OriginalApplyPiHistory env registry target commonLeft commonRight
        (originalApplicationTypeRouteSide initial domain body function argument result hu hv location graph)
        (destination.nativeSide common),
      ∃ sourceEq : history.sourceFrame = frame,
        history.rightDomain = destination.firstDomain ∧
        history.headerFrame = closedTypeRouteFrame (ContextDerivation.nil (env := origin.types) (U := U))
          common env registry target commonLeft commonRight ∧
        ∃ headerWorld : WorldEnvironmentProvenance strata U history.final,
          headerWorld.worlds = [] ∧
          ∃ data : history.whole.ControlledWorldData P base caps controls.cutoff controls.fuel frontier,
            ∃ boundary : history.whole.WorldBoundary data.inputs controls (controls.atHeader origin.constructorOrigin)
                ((congrArg (fun f => f.realization.frame.dependencyEnvironment controls.ordered) sourceEq).symm ▸ sourceWorld)
                headerWorld,
              boundary.FrameOccurrenceCoherent data.controls data.frames ∧
              Sponsored [originalCallWorld controls .assignedComparison outer sourceWorld]
                (history.whole.worldReserve data.inputs).worlds ∧
              Sponsored [originalCallWorld controls .assignedComparison outer outerWorld]
                (history.whole.worldReserve data.inputs).worlds ∧
    ∃ reserveEnvironment, ∃ reserve : WorldEnvironmentProvenance strata U reserveEnvironment,
      Sponsored [originalCallWorld controls .assignedComparison outer sourceWorld] reserve.worlds ∧
      Sponsored [originalCallWorld controls .assignedComparison outer outerWorld] reserve.worlds ∧
      Nonempty (WorldVariableDemandReply P base caps
        (.capture (destination.nativeSide common).graph destination.firstDomain graph argument
          (.ofLocation (.appArgument location) initial))
        commonLeft commonRight (controls.atHeader origin.constructorOrigin) reserve frontier
        0 (Profile.empty : Profile 0)) := by
  have equivalent : ∀ ls : List VLevel, List.Forall₂ (· ≈ ·) ls ls := by
    intro ls
    induction ls with
    | nil => exact .nil
    | cons l ls ih => exact .cons (by rfl) ih
  obtain ⟨history, frameEq, finalWorld, finalEmpty, headerEq, whole, boundary, coherent, wholePaid⟩ :=
    firstApplicationPiHistoryWorld initial domain body function argument result hu hv location graph frame
      controls below sourceWorld familyOrigin queryWF (equivalent levels)
      shape caps frontier generation ready compatible replayable hereditary covered headerSource
  obtain ⟨next, nextEq, domainEq, nextHeaderEq, nextWorld, nextEmpty, nextData, nextBoundary, nextCoherent, nextPaid⟩ :=
    destination.transplantFirstHistoryWorld origin familyOrigin queryWF shape common commonLeft commonRight
      _ history controls controls frontier
      ((congrArg (fun f => f.realization.frame.dependencyEnvironment controls.ordered) frameEq).symm ▸ sourceWorld)
      finalWorld finalEmpty whole boundary coherent below headerSource typesSource outer sourceWorld
      .assignedComparison (wholePaid outer head rootLocation)
  have sourceEq : next.sourceFrame = frame := nextEq.trans frameEq
  let selectedSource : WorldGenerated strata P base caps commonLeft commonRight graph
      next.sourceFrame.realization.frame.raw controls := sourceEq.symm ▸ generation
  have selectedReady : selectedSource.Controlled frontier := by cases sourceEq; exact ready
  have selectedCompatible : selectedSource.UsesControlPrefix controls.cutoff controls.fuel := by cases sourceEq; exact compatible
  have selectedReplayable : selectedSource.Replayable := by cases sourceEq; exact replayable
  have selectedHereditary : selectedSource.Hereditary frontier := by cases sourceEq; exact hereditary
  let selectedBaseline : WorldEnvironmentProvenance strata U
      (next.sourceFrame.realization.frame.dependencyEnvironment controls.ordered) :=
    (congrArg (fun f => f.realization.frame.dependencyEnvironment controls.ordered) sourceEq).symm ▸ sourceWorld
  have selectedWorlds : selectedBaseline.worlds = sourceWorld.worlds := by cases sourceEq; rfl
  have selectedCoverage : Covered (@EquationControlMeasure.Less strata.rules.length)
      selectedSource.worlds selectedBaseline.worlds := by cases sourceEq; exact covered
  let headerControls := controls.atHeader origin.constructorOrigin
  let emptyGeneration : WorldGenerated strata P base caps commonLeft commonRight (destination.nativeSide common).graph
      (closedTypeRouteFrame (ContextDerivation.nil (env := origin.types) (U := U)) common env registry target commonLeft commonRight).realization.frame.raw
      headerControls := .empty common commonLeft commonRight (origin.typesBelow.trans below) typesSource headerControls
  let nextGeneration : WorldGenerated strata P base caps commonLeft commonRight (destination.nativeSide common).graph
      next.headerFrame.realization.frame.raw headerControls := nextHeaderEq.symm ▸ emptyGeneration
  have facts (f : OriginalTypeRouteFrame env registry target (destination.nativeSide common).graph commonLeft commonRight)
      (equal : f = closedTypeRouteFrame (ContextDerivation.nil (env := origin.types) (U := U)) common env registry target commonLeft commonRight) :
      let generated : WorldGenerated strata P base caps commonLeft commonRight (destination.nativeSide common).graph f.realization.frame.raw headerControls := equal.symm ▸ emptyGeneration
      Nonempty (generated.Controlled frontier) ∧ generated.UsesControlPrefix controls.cutoff controls.fuel ∧
        generated.Replayable ∧ Nonempty (generated.Hereditary frontier) ∧ generated.worlds = [] := by
    subst f
    exact ⟨⟨⟨.nil, by intro control active; exact Nat.zero_le _, by intro child member; cases member⟩⟩,
      ⟨rfl,rfl⟩, trivial, ⟨⟨trivial, .nil, trivial⟩⟩, rfl⟩
  obtain ⟨⟨nextReady⟩, nextCompatible, nextReplayable, ⟨nextHereditary⟩, nextWorlds⟩ := facts next.headerFrame nextHeaderEq
  have nextCoverage : Covered (@EquationControlMeasure.Less strata.rules.length) nextGeneration.worlds nextWorld.worlds := by
    rw [nextWorlds]
    intro child member
    cases member
  have noBinders : location.binderPrefix = [] := Located.sameSource_prefix_nil location
  have environmentEq : ∀ ordered, next.sourceFrame.realization.frame.dependencyEnvironment ordered = ownerInitial := by
    intro ordered
    rw [sourceEq]
    exact sourceEnvironment ordered
  have sourceBound : ∀ ordered, environmentCost (next.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost (location.dependencyEnvironment ordered ownerInitial) := by
    intro ordered
    rw [environmentEq, Located.dependencyEnvironment_of_prefix_nil ordered location noBinders]
    exact Nat.le_refl _
  have castCompose {α : Sort _} (F : α → Sort _) {x y z : α} (h : x = y) (k : y = z) (v : F z) :
      h.symm ▸ (k.symm ▸ v) = (h.trans k).symm ▸ v := by cases h; cases k; rfl
  have baselineEq :
      (congrArg (fun f => f.realization.frame.dependencyEnvironment controls.ordered) nextEq).symm ▸
        ((congrArg (fun f => f.realization.frame.dependencyEnvironment controls.ordered) frameEq).symm ▸ sourceWorld) = selectedBaseline := by
    exact castCompose (fun e => WorldEnvironmentProvenance strata U e)
      (congrArg (fun f => f.realization.frame.dependencyEnvironment controls.ordered) nextEq)
      (congrArg (fun f => f.realization.frame.dependencyEnvironment controls.ordered) frameEq) sourceWorld
  let sameBoundary : next.whole.WorldBoundary nextData.inputs controls headerControls selectedBaseline nextWorld := by
    exact baselineEq ▸ nextBoundary
  have sameCoherent : sameBoundary.FrameOccurrenceCoherent nextData.controls nextData.frames := by
    have transfer (x y : WorldEnvironmentProvenance strata U
        (next.sourceFrame.realization.frame.dependencyEnvironment controls.ordered))
        (equal : x = y)
        (b : next.whole.WorldBoundary nextData.inputs controls headerControls x nextWorld)
        (c : b.FrameOccurrenceCoherent nextData.controls nextData.frames) :
        (equal ▸ b).FrameOccurrenceCoherent nextData.controls nextData.frames := by
      subst y
      exact c
    exact transfer _ _ baselineEq nextBoundary nextCoherent
  have sameCallLocal : originalCallWorld controls .assignedComparison outer selectedBaseline =
      originalCallWorld controls .assignedComparison outer sourceWorld := by cases sourceEq; rfl
  have paidWhole : Sponsored [originalCallWorld controls .assignedComparison outer outerWorld]
      (next.whole.worldReserve nextData.inputs).worlds := by
    intro child member
    obtain ⟨parent, present, lower⟩ := nextPaid child member
    cases List.mem_singleton.mp present
    exact ⟨_, List.mem_singleton_self _, originalCallWorld_retargetBelow controls outer .assignedComparison
      sourceWorld outerWorld sourceCapacity sourceCoveredOuter lower⟩
  have selectedCapacity : environmentCost (next.sourceFrame.realization.frame.dependencyEnvironment controls.ordered) ≤
      environmentCost outerEnvironment := by rw [sourceEq]; exact sourceCapacity
  have selectedCoveredOuter : Covered (@EquationControlMeasure.Less strata.rules.length)
      selectedBaseline.worlds outerWorld.worlds := by rw [selectedWorlds]; exact sourceCoveredOuter
  obtain ⟨reserveEnvironment, reserve, reservePaidLocal, reservePaid, capture⟩ := next.captureEmptyArgumentWorld
    initial domain body function argument result hu hv location graph
    controls headerControls frontier noBinders sourceBound selectedSource nextGeneration selectedBaseline nextWorld
    selectedCoverage nextCoverage selectedReplayable nextReplayable selectedReady nextReady selectedHereditary nextHereditary
    selectedCompatible nextCompatible nextData sameBoundary sameCoherent outer head field fieldEq rootLocation initialWorld
    environmentEq (selectedWorlds.trans sourceWorlds) outerWorld selectedCapacity selectedCoveredOuter (origin.types_count_lt controls.ordered)
    (by intro child member; rw [nextEmpty] at member; cases member)
    paidWhole (by intro child member; rw [nextEmpty] at member; cases member)
    (by simpa only [sameCallLocal] using nextPaid) outerPaid henv hscoped formed bank unary
  refine ⟨next, sourceEq, domainEq, nextHeaderEq, nextWorld, nextEmpty, nextData, sameBoundary,
    sameCoherent, nextPaid, paidWhole, reserveEnvironment, reserve, ?_, reservePaid, ?_⟩
  · simpa only [sameCallLocal] using reservePaidLocal
  let conclusion (declared : EndpointRef origin.types U [] C (.sort destination.firstLevel)) : Prop :=
    Nonempty (WorldVariableDemandReply P base caps
      (.capture (destination.nativeSide common).graph declared graph argument
        (.ofLocation (.appArgument location) initial))
      commonLeft commonRight headerControls reserve frontier 0 (Profile.empty : Profile 0))
  change conclusion next.rightDomain at capture
  exact Eq.mp (congrArg conclusion domainEq) capture
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
