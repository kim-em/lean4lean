import Lean4Lean.Theory.Typing.AnchoredOriginalWorldEmptyCaptureReserve
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldEmptyHistoryCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldInitialFamilyHistory
import Lean4Lean.Theory.Typing.AnchoredOriginalTemplateParameterWorldCalls

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private descendant_below from Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyApplyPiWorldHistory
open private Located.dependencyEnvironment_of_prefix_nil from Lean4Lean.Theory.Typing.AnchoredOriginalFamilyArgumentPair
open private located_worlds_nil from Lean4Lean.Theory.Typing.AnchoredOriginalWorldLocatedCoverage
open private singletonSponsoredBelow from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

section
variable
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

theorem OriginalApplyPiHistory.captureEmptyArgumentWorld
    {strata : EquationStratification env}
    {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
    (sourceControls : OriginalWorldControls strata sourceEnv)
    (headerControls : OriginalWorldControls strata right.sourceEnv)
    (frontier : List (World strata.rules.length))
    (noBinders : location.binderPrefix = [])
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost (location.dependencyEnvironment ordered ownerInitial))
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
    (wholeCoherent : wholeBoundary.FrameOccurrenceCoherent whole.controls whole.frames)
    (outer : EndpointState sourceEnv U source (.proj projectedName index displayedMajor) outerType)
    (head : OriginalFactorCut.ProjectionHead outer)
    (field : EndpointRef sourceEnv U source head.fieldType (.sort head.fieldLevel))
    (fieldEq : head.field = .ref field) (rootLocation : Located (.right head.major) (.ref major))
    (initialWorld : WorldEnvironmentProvenance strata U ownerInitial)
    (sourceEnvironment : ∀ ordered, history.sourceFrame.realization.frame.dependencyEnvironment ordered = ownerInitial)
    (sourceWorlds : sourceBaseline.worlds = initialWorld.worlds)
    (outerWorld : WorldEnvironmentProvenance strata U outerEnvironment)
    (sourceCapacity : environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment sourceControls.ordered) ≤ environmentCost outerEnvironment)
    (sourceCoveredOuter : Covered (@EquationControlMeasure.Less strata.rules.length) sourceBaseline.worlds outerWorld.worlds)
    (headerEarlier : headerControls.ordered.constantCount < sourceControls.ordered.constantCount)
    (headerInherited : Sponsored [originalCallWorld sourceControls .assignedComparison outer outerWorld]
      headerBaseline.worlds)
    (wholePaid : Sponsored [originalCallWorld sourceControls .assignedComparison outer outerWorld]
      (history.whole.worldReserve whole.inputs).worlds)
    (headerInheritedLocal : Sponsored [originalCallWorld sourceControls .assignedComparison outer sourceBaseline]
      headerBaseline.worlds)
    (wholePaidLocal : Sponsored [originalCallWorld sourceControls .assignedComparison outer sourceBaseline]
      (history.whole.worldReserve whole.inputs).worlds)
    (outerPaid : Sponsored frontier [originalCallWorld sourceControls .assignedComparison outer outerWorld])
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (bank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld sourceControls .assignedComparison outer outerWorld]))
    (unary : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld sourceControls .assignedComparison outer outerWorld])) :
    ∃ reserveEnvironment, ∃ reserve : WorldEnvironmentProvenance strata U reserveEnvironment,
      Sponsored [originalCallWorld sourceControls .assignedComparison outer sourceBaseline] reserve.worlds ∧
      Sponsored [originalCallWorld sourceControls .assignedComparison outer outerWorld] reserve.worlds ∧
      Nonempty (WorldVariableDemandReply P base commonCaps
        (.capture right.graph history.rightDomain graph argument (.ofLocation (.appArgument location) initial))
        commonLeft commonRight headerControls reserve frontier 0 (Profile.empty : Profile 0)) := by
  let query : RichObs sourceEnv env U registry target argument history.sourceFrame.locals
      (raw.comp commonLeft) (Profile.empty : Profile 0) [] := .legacy (.legacy .empty)
  have resources : Footprint.Available ([] : Footprint) history.sourceFrame.available := fun _ _ member => nomatch member
  let seed := history.argumentSeed (field := field) initial domain body function argument result hu hv location graph
    noBinders sourceBound query resources
  let scope : CappedOwnerScope common raw commonLeft commonRight commonCaps seed.depth
      (seed.owner.context seed.initialContext) := {
    toOriginalOwnerScope := history.argumentSeedScope (field := field) initial domain body function argument result hu hv location graph
      noBinders sourceBound query resources
    caps := commonCaps, capsTail := rfl }
  obtain ⟨route, data, reserveEq, worlds, boundary, coherent⟩ :=
    history.argumentSeedHistoryWorld (field := field) initial domain body function argument result hu hv location graph
      sourceControls headerControls frontier noBinders sourceBound query resources sourceWorld headerWorld
      sourceBaseline headerBaseline sourceCovered headerCovered sourceReplayable headerReplayable sourceReady headerReady
      sourceHereditary headerHereditary sourceCompatible headerCompatible whole wholeBoundary wholeCoherent
  have seedReady : ControlledStoredQuery sourceControls frontier (.observation seed.query) := {
    annotation := .empty
    within := by
      intro control active
      simp only [seed, OriginalApplyPiHistory.argumentSeed, query, StoredOriginalQuery.headDepth, RichObs.headDepth, SortableObs.headDepth]
      rw [Lean4Lean.AnchoredSource.Adapted.Obs.headDepth.eq_def]
      exact Nat.zero_le _
    sponsored := by intro child member; cases member }
  have ownerWorlds : (seed.owner.worldEnvironment sourceControls initialWorld).worlds = sourceBaseline.worlds := by
    change (initialWorld.located sourceControls (.appArgument location)).worlds = _
    rw [located_worlds_nil sourceControls (.appArgument location) initialWorld noBinders]
    exact sourceWorlds.symm
  have ownerBelow : WorldBelow strata.rules.length
      (originalCallWorld sourceControls .fundamental seed.owner.node
        (seed.owner.worldEnvironment sourceControls initialWorld))
      (originalCallWorld sourceControls .assignedComparison outer outerWorld) := by
    apply originalCallWorld_retargetBelow sourceControls outer .assignedComparison
      sourceBaseline outerWorld sourceCapacity sourceCoveredOuter
    have lower := descendant_below head rootLocation (.appArgument location) sourceControls sourceBaseline
      .fundamental .assignedComparison
    have ownerEnvironment : seed.owner.dependencyEnvironment sourceControls.ordered ownerInitial =
        history.sourceFrame.realization.frame.dependencyEnvironment sourceControls.ordered := by
      change (Located.appArgument location).dependencyEnvironment sourceControls.ordered ownerInitial = _
      rw [Located.dependencyEnvironment_of_prefix_nil sourceControls.ordered (.appArgument location) noBinders, sourceEnvironment]
    simpa only [originalCallWorld, ownerWorlds, ownerEnvironment,
      show seed.owner.node = argument from rfl] using lower
  have headerBelow {Γ : List VExpr} {e T : VExpr} (node : EndpointState right.sourceEnv U Γ e T) :
      WorldBelow strata.rules.length (originalCallWorld headerControls .expressionReindex node headerBaseline)
        (originalCallWorld sourceControls .assignedComparison outer outerWorld) := by
    have controlPrefix := headerCompatible.controls_match
    apply Below.root
    · simpa only [originalCallWorld, controlPrefix.1, controlPrefix.2] using
        (EquationControlMeasure.constantsDecrease headerEarlier
          strata.rules.length sourceControls.cutoff sourceControls.fuel _ _ : _)
    · intro child member
      obtain ⟨parent, present, below⟩ := headerInherited child member
      cases List.mem_singleton.mp present
      exact below
  have routePaid : Sponsored [originalCallWorld sourceControls .assignedComparison outer outerWorld]
      (route.route.worldReserve data.inputs).worlds := by
    intro child present
    rw [worlds] at present
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    rcases List.mem_append.mp present with present | present
    · rcases List.mem_append.mp present with present | present
      · rcases List.mem_cons.mp present with rfl | present
        · exact originalCallWorld_retargetBelow sourceControls outer .assignedComparison sourceBaseline outerWorld sourceCapacity sourceCoveredOuter
            (descendant_below head rootLocation (.assignedFormation (.appArgument location)) sourceControls sourceBaseline _ _)
        · cases List.mem_singleton.mp present
          exact originalCallWorld_retargetBelow sourceControls outer .assignedComparison sourceBaseline outerWorld sourceCapacity sourceCoveredOuter
            (descendant_below head rootLocation (.appDomain location) sourceControls sourceBaseline _ _)
      · obtain ⟨parent, member, lower⟩ := wholePaid child present
        cases List.mem_singleton.mp member
        exact lower
    · rcases List.mem_cons.mp present with rfl | present
      · exact headerBelow right.domain
      · cases List.mem_singleton.mp present
        exact headerBelow (.ref history.rightDomain)
  have headerBelowLocal {Γ : List VExpr} {e T : VExpr} (node : EndpointState right.sourceEnv U Γ e T) :
      WorldBelow strata.rules.length (originalCallWorld headerControls .expressionReindex node headerBaseline)
        (originalCallWorld sourceControls .assignedComparison outer sourceBaseline) := by
    have controlPrefix := headerCompatible.controls_match
    apply Below.root
    · simpa only [originalCallWorld, controlPrefix.1, controlPrefix.2] using
        (EquationControlMeasure.constantsDecrease headerEarlier
          strata.rules.length sourceControls.cutoff sourceControls.fuel _ _ : _)
    · intro child member
      obtain ⟨parent, present, below⟩ := headerInheritedLocal child member
      cases List.mem_singleton.mp present
      exact below
  have routePaidLocal : Sponsored [originalCallWorld sourceControls .assignedComparison outer sourceBaseline]
      (route.route.worldReserve data.inputs).worlds := by
    intro child present
    rw [worlds] at present
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    rcases List.mem_append.mp present with present | present
    · rcases List.mem_append.mp present with present | present
      · rcases List.mem_cons.mp present with rfl | present
        · exact (descendant_below head rootLocation (.assignedFormation (.appArgument location)) sourceControls sourceBaseline _ _)
        · cases List.mem_singleton.mp present
          exact (descendant_below head rootLocation (.appDomain location) sourceControls sourceBaseline _ _)
      · obtain ⟨parent, member, lower⟩ := wholePaidLocal child present
        cases List.mem_singleton.mp member
        exact lower
    · rcases List.mem_cons.mp present with rfl | present
      · exact headerBelowLocal right.domain
      · cases List.mem_singleton.mp present
        exact headerBelowLocal (.ref history.rightDomain)
  have funded {calls : List (World strata.rules.length)}
      (paid : Sponsored [originalCallWorld sourceControls .assignedComparison outer outerWorld] calls) :
      CallBelow strata.rules.length (frontier ++ calls)
        (frontier ++ [originalCallWorld sourceControls .assignedComparison outer outerWorld]) := by
    have lower := split_call (fun child member => by
      obtain ⟨parent, present, below⟩ := paid child member
      cases List.mem_singleton.mp present
      exact below)
    have extend : ∀ extra : List (World strata.rules.length),
        CallBelow strata.rules.length (extra ++ calls)
          (extra ++ [originalCallWorld sourceControls .assignedComparison outer outerWorld]) := by
      intro extra
      induction extra with
      | nil => exact lower
      | cons world tail ih => exact ih.cons world
    exact extend frontier
  have sponsored {calls : List (World strata.rules.length)}
      (paid : Sponsored [originalCallWorld sourceControls .assignedComparison outer outerWorld] calls) :
      Sponsored frontier calls := by
    intro child member
    obtain ⟨parent, present, lower⟩ := paid child member
    cases List.mem_singleton.mp present
    exact singletonSponsoredBelow outerPaid lower child (List.mem_singleton_self _)
  have ownerPaid : Sponsored [originalCallWorld sourceControls .assignedComparison outer outerWorld]
      [originalCallWorld sourceControls .fundamental seed.owner.node (seed.owner.worldEnvironment sourceControls initialWorld)] := by
    intro child present
    cases List.mem_singleton.mp present
    exact ⟨_, List.mem_singleton_self _, ownerBelow⟩
  have headerOwnCompatible : headerWorld.UsesControlPrefix headerControls.cutoff headerControls.fuel := by
    have controlPrefix := headerCompatible.controls_match
    rw [controlPrefix.1, controlPrefix.2]
    exact headerCompatible
  have outputPaidLocal := ProjectionHead.emptyCaptureReserve_sponsored head field fieldEq major rootLocation
    history.rightDomain sourceControls headerControls initialWorld sourceBaseline
    (sourceEnvironment sourceControls.ordered).symm sourceWorlds.symm headerBaseline headerEarlier
    headerCompatible.controls_match.1 headerCompatible.controls_match.2 headerInheritedLocal
    (route.route.worldReserve data.inputs) routePaidLocal
  have outputPaid := ProjectionHead.emptyCaptureReserve_retargetedSponsored head field fieldEq major rootLocation
    history.rightDomain sourceControls headerControls initialWorld sourceBaseline
    (sourceEnvironment sourceControls.ordered).symm sourceWorlds.symm outerWorld sourceCapacity sourceCoveredOuter headerBaseline headerEarlier
    headerCompatible.controls_match.1 headerCompatible.controls_match.2 headerInherited
    (route.route.worldReserve data.inputs) routePaid
  refine ⟨_, _, outputPaidLocal, outputPaid, generatedEmptyHistoryCaptureWorld graph graph argument
    (.ofLocation (.appArgument location) initial) rfl seed scope sourceControls headerControls frontier _
    sourceWorld sourceReplayable (.inr location) sourceHereditary sourceReady sourceCompatible seedReady
    (history.headerDomainProvenance initial domain body function argument result hu hv location graph)
    history.headerFrame.realization headerWorld headerReplayable headerHereditary headerReady headerOwnCompatible
    route initialWorld (sourceBaseline, headerBaseline) ⟨sourceCovered, headerCovered⟩ ?_
    data boundary coherent sourceWorld.erase.ambientGenerated.ambient.1 sourceWorld.erase.sources.1
    sourceWorld.erase.ambientGenerated.ambient.1 sourceWorld.erase.sources.1
    henv hscoped formed bank unary (sponsored ownerPaid) (funded ownerPaid) (sponsored routePaid) (funded routePaid)⟩
  rw [ownerWorlds]
  exact Covered.refl _

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
