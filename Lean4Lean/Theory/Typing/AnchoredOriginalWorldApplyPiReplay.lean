import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplyPiOutputCoverage
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationArguments

/-! Actual application route execution starts with the incoming result query.
Backward argument selection, Pi packing and captured output are constructed;
only the structurally smaller whole-Pi route is recursively interpreted. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3600000

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
  (sourceGraph : OriginalCaptureMap (common := common) (location.contextDerivation initial) sourceRaw)
  {headerRoot : EndpointRef headerEnv U headerRootSource headerExpression headerType}
  (headerInitial : ContextDerivation headerEnv U headerRootSource)
  (headerDomain : EndpointRef headerEnv U headerSource C (.sort cu))
  (headerBody : EndpointState headerEnv U (C :: headerSource) D (.sort dv))
  (hcu : cu.WF U) (hdv : dv.WF U)
  (headerLocation : Located headerRoot (.pi hcu hdv (.ref headerDomain) headerBody))
  (headerGraph : OriginalCaptureMap (common := common) (headerLocation.contextDerivation headerInitial) headerRaw)

local notation "sourceSide" => originalApplicationTypeRouteSide initial domain body function argument result hu hv location sourceGraph
local notation "headerSide" => originalNativePiRouteSide headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph


theorem OriginalApplyPiHistory.replayApplicationReplyWorldStep
    {n : Nat} {profile : Profile n}
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight sourceSide headerSide)
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    (sourceControls : OriginalWorldControls strata sourceEnv)
    (headerControls : OriginalWorldControls strata headerEnv)
    (frontier : List (World strata.rules.length))
    (sourceWorld : WorldGenerated strata P base commonCaps commonLeft commonRight sourceGraph
      history.sourceFrame.realization.frame.raw sourceControls)
    (headerWorld : WorldGenerated strata P base commonCaps commonLeft commonRight headerGraph
      history.headerFrame.realization.frame.raw headerControls)
    (sourceBaseline : WorldEnvironmentProvenance strata U
      (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered))
    (headerBaseline : WorldEnvironmentProvenance strata U history.final)
    (sourceCovered : Covered (@EquationControlMeasure.Less strata.rules.length) sourceWorld.worlds sourceBaseline.worlds)
    (headerCovered : Covered (@EquationControlMeasure.Less strata.rules.length) headerWorld.worlds headerBaseline.worlds)
    (sourceReplayable : sourceWorld.Replayable)
    (headerReplayable : headerWorld.Replayable)
    (sourceReady : sourceWorld.Controlled frontier)
    (sourceHereditary : sourceWorld.Hereditary frontier)
    (headerReady : headerWorld.Controlled frontier)
    (headerHereditary : headerWorld.Hereditary frontier)
    (sourceCompatible : sourceWorld.UsesControlPrefix sourceControls.cutoff sourceControls.fuel)
    (headerCompatible : headerWorld.UsesControlPrefix sourceControls.cutoff sourceControls.fuel)
    (wholeData : history.whole.ControlledWorldData P base commonCaps sourceControls.cutoff sourceControls.fuel frontier)
    (wholeBoundary : history.whole.WorldBoundary wholeData.inputs sourceControls headerControls
      sourceBaseline headerBaseline)
    (wholeCoherent : wholeBoundary.FrameOccurrenceCoherent wholeData.controls wholeData.frames)
    (noBinders : location.binderPrefix = [])
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (initialProvenance : WorldEnvironmentProvenance strata U ownerInitial)
    (sourceAdmission : Covered (@EquationControlMeasure.Less strata.rules.length)
      sourceBaseline.worlds initialProvenance.worlds)
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (sourceSponsored : Sponsored frontier [originalCallWorld sourceControls .fundamental
      (sourceSide).node sourceBaseline])
    (headerSponsored : Sponsored frontier [originalCallWorld headerControls .fundamental
      (headerSide).display.node headerBaseline])
    (sourceF : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld sourceControls .fundamental (sourceSide).node sourceBaseline]))
    (sourceR : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld sourceControls .fundamental (sourceSide).node sourceBaseline]))
    (headerF : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld headerControls .fundamental (headerSide).display.node headerBaseline]))
    (wholeReplay : ∀ {queryRank : Nat} {start : VExpr} {queryProfile : Profile queryRank},
      (incoming : AmbientBoundedParameterReply base commonCaps start (sourceSide).pi.display commonLeft commonRight queryProfile
        (environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered))) →
      WorldParameterReplyData (P := P) sourceControls sourceBaseline frontier incoming →
      queryProfile.HasType (.sort true) →
      ∃ output : AmbientBoundedParameterReply base commonCaps start (headerSide).display commonLeft commonRight
        queryProfile (environmentCost history.final),
        Nonempty (WorldParameterReplyData (P := P) headerControls headerBaseline frontier output))
    (incoming : AmbientBoundedParameterReply base commonCaps start (sourceSide).resultDisplay commonLeft commonRight
      profile (environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)))
    (incomingData : WorldParameterReplyData (P := P) sourceControls sourceBaseline frontier incoming)
    (sorted : profile.HasType (.sort true)) :
    ∃ output : AmbientBoundedParameterReply base commonCaps start history.destination commonLeft commonRight profile
        (environmentCost (history.outputEnvironment field major ownerInitial)),
      Nonempty (WorldParameterReplyData (P := P) headerControls
        (history.outputWorld field major sourceControls headerControls initialProvenance sourceBaseline headerBaseline wholeData.inputs)
        frontier output) := by
  let prior := incoming.reply.answer.reply
  let selected : OriginalTypeRouteFrame env registry target sourceGraph commonLeft commonRight :=
    ⟨prior.locals, prior.available, prior.realization, prior.closed⟩
  let selectedData : WorldCallFrameData (P := P) (base := base) (caps := commonCaps)
      (display := (sourceSide).termDisplay) sourceControls sourceBaseline frontier selected.realization := {
    generation := incomingData.generation
    hereditary := incomingData.hereditary
    replayable := incomingData.replayable
    controlled := incomingData.controlled
    compatible := incomingData.compatible
    closed := prior.closed
    capacity := incoming.reply.bounded sourceControls.ordered
    covered := incomingData.covered }
  obtain ⟨footprint, certificate, certificateReady, resources, _⟩ :=
    prior.query.code_controlled henv sourceControls incomingData.query sorted
  obtain ⟨frameData⟩ := WorldUnaryFrameData.ofGenerated prior.realization.frame
    incomingData.generation incomingData.controlled
    incomingData.replayable incomingData.compatible incomingData.hereditary
  obtain ⟨packet, supply, supplyReady⟩ := generatedWorldApplicationArguments
    initial domain body function argument result hu hv location prior.realization.frame
    prior.realization.substitutions sourceControls incomingData.generation.environment frontier frameData
    sourceBaseline (incoming.reply.bounded sourceControls.ordered) incomingData.covered
    henv hscoped formed prior.closed sourceSponsored sourceR certificate resources certificateReady
  obtain ⟨packed, ⟨packedReady⟩⟩ := packet.piRequestWorld frameData
    sourceBaseline (incoming.reply.bounded sourceControls.ordered) incomingData.covered
    henv hscoped history.leftBelow formed prior.closed sourceSponsored sourceF supply supplyReady
  obtain ⟨answer, _, _⟩ := history.replayApplicationPackedWorldStep (field := field)
    initial domain body function argument result hu hv location sourceGraph
    headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
    sourceControls headerControls frontier sourceWorld headerWorld sourceBaseline headerBaseline
    sourceCovered headerCovered sourceReplayable headerReplayable sourceReady sourceHereditary headerReady headerHereditary
    sourceCompatible headerCompatible wholeData wholeBoundary wholeCoherent selected selectedData
    noBinders sourceBound initialProvenance sourceAdmission henv hscoped headerBelow formed
    sourceSponsored headerSponsored sourceF sourceR headerF wholeReplay packed packedReady
  let completed := answer.toAmbientApplyPiReplayResult.boundedReply
  have sourceRelated : TypeRelated env U registry target start ((B.inst a).subst (sourceRaw.comp commonLeft)) profile := by
    simpa only [OriginalApplicationTypeRouteSide.resultDisplay, OriginalNestedDisplay.ofOccurrence,
      subst_subst, originalApplicationTypeRouteSide] using incoming.related
  have sourcePath : TypeConversion env U target start ((B.inst a).subst (sourceRaw.comp commonLeft)) := by
    simpa only [OriginalApplicationTypeRouteSide.resultDisplay, OriginalNestedDisplay.ofOccurrence,
      subst_subst, originalApplicationTypeRouteSide] using incoming.path
  let output : AmbientBoundedParameterReply base commonCaps start history.destination commonLeft commonRight profile
      (environmentCost (history.outputEnvironment field major ownerInitial)) := {
    reply := completed.reply
    related := sourceRelated.trans henv completed.related
    path := sourcePath.trans completed.path
    generation := completed.generation }
  let ready := answer.boundedWorldReply
  exact ⟨output, ⟨{
    generation := ready.generation
    hereditary := ready.hereditary
    replayable := ready.replayable
    controlled := ready.controlled
    compatible := ready.compatible
    query := ready.query
    covered := ready.covered }⟩⟩

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
