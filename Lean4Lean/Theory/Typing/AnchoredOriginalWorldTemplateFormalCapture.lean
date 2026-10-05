import Lean4Lean.Theory.Typing.AnchoredOriginalWorldTemplateFirstFormalCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFormalSecondParameterCapture
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
open private firstContext from Lean4Lean.Theory.Typing.AnchoredOriginalWorldTemplateFirstFormalCapture
open private transportWorld transportWorld_worlds from Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyApplyPiWorldHistory
open private Located.dependencyEnvironment_of_prefix_nil from Lean4Lean.Theory.Typing.AnchoredOriginalFamilyArgumentPair
open private sponsored_covered from Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyHistorySponsorship
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4200000

private theorem frameEnvironmentOfHEq
    {first second : ContextDerivation sourceEnv U source}
    {frame : OriginalRichFrame sourceEnv env U registry target first locals σ τ available}
    {next : OriginalRichFrame sourceEnv env U registry target second locals σ τ available}
    (contextEq : first = second) (same : HEq frame next) (ordered : sourceEnv.Ordered) :
    frame.dependencyEnvironment ordered = next.dependencyEnvironment ordered := by
  cases contextEq
  cases eq_of_heq same
  rfl

private theorem worldsOfHEq
    {strata : EquationStratification env}
    {first : WorldEnvironmentProvenance strata U one}
    {second : WorldEnvironmentProvenance strata U two}
    (environmentEq : one = two) (same : HEq first second) : first.worlds = second.worlds := by
  cases environmentEq
  cases eq_of_heq same
  rfl

private theorem identityExecutionRecontext
    {strata : EquationStratification env} {P : VEnv → Prop}
    {first second : ContextDerivation sourceEnv U source}
    (equal : first = second)
    (controls : OriginalWorldControls strata sourceEnv)
    (frontier : List (World strata.rules.length))
    (frame : OriginalRichFrame sourceEnv env U registry target first locals σ τ available)
    (world : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame world)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (closed : available.AtomClosed) :
    ∃ next : OriginalTypeRouteFrame env registry target (.identity second) σ τ,
      ∃ environment : next.realization.frame.dependencyEnvironment controls.ordered =
          frame.dependencyEnvironment controls.ordered,
        Nonempty (WorldBoundaryFrame.ExecutionData P (frame.captureBase substitutions)
          (frame.captureBase substitutions).initialCaps frontier
          ⟨next.box, controls, transportWorld environment.symm world⟩) := by
  cases equal
  obtain ⟨ready⟩ := data.controlled substitutions
  exact ⟨⟨locals, available, ⟨frame, substitutions⟩, closed⟩, rfl,
    ⟨⟨data.generation substitutions, trivial, ready, ⟨rfl,rfl⟩, Covered.refl _,
      data.generation_hereditary substitutions⟩⟩⟩
section
variable
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {leftDisplay : OriginalNestedDisplay U common leftExpression leftAssigned}
    {rightNode : EndpointState rightEnv U rightSource (.proj name index rightValue) rightAssigned}
    (rightHead : ProjectionHead rightNode)
    {rightContext : ContextDerivation rightEnv U rightSource}
    (rightGraph : OriginalCaptureMap (common := common) rightContext rightRaw)
    (displayedEq : displayed = rightValue.subst rightRaw)
    (controls : OriginalWorldControls strata rightEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (answer : WorldTemplateAssignedReply (P := P) base caps leftDisplay
      (OriginalNestedDisplay.recordBridgeReference rightGraph (.right rightHead.major) displayedEq)
      commonLeft commonRight controls baseline frontier (profile : Profile n))
    (input : answer.FormationInput)
    (arguments : rightHead.parameters ++ rightHead.indices = [a, p])
    (bootstrap : WorldTemplateMajorBackwardInitialization input
      (congrArg (mkApps (.const name rightHead.levels)) arguments) rightHead.levelsWF)

theorem WorldTemplateMajorBackwardInitialization.captureFormalParametersWorld
    (origin : ProjectionParameterOrigin rightEnv name rightHead.info)
    {signature : ConstantTelescope (origin.family.type.instL rightHead.levels)}
    {domains : signature.domains = [C,D]}
    (destination : FormalFamilyDestination (U := U) origin signature domains)
    (field : EndpointRef rightEnv U rightSource rightHead.fieldType (.sort rightHead.fieldLevel))
    (fieldEq : rightHead.field = .ref field)
    (paid : Sponsored frontier [originalCallWorld controls .assignedComparison rightNode baseline])
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (sourceClosed : ∀ source, source ≤ env → P source)
    (bank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .assignedComparison rightNode baseline]))
    (unary : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .assignedComparison rightNode baseline])) :
    ∃ frame : OriginalRichFrame rightEnv env U registry target
        ((bootstrap.firstLocation (arguments := arguments)).contextDerivation input.provenance.initial)
        answer.reply.reply.answer.reply.locals (rightRaw.comp commonLeft) (rightRaw.comp commonLeft)
        answer.reply.reply.answer.reply.available,
      ∃ captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered),
        HEq frame bootstrap.frame ∧ HEq captured bootstrap.captured ∧
        ∃ frameData : WorldUnaryFrameData P controls frontier frame captured,
        let ownBase := frame.captureBase input.substitutions
        ∃ formalGraph : OriginalCaptureMap (common := rightSource) destination.context ((Subst.id.cons a).cons p),
        ∃ formalLocals formalAvailable,
        ∃ realization : OriginalCaptureRealization formalGraph env registry target formalLocals
            (rightRaw.comp commonLeft) (rightRaw.comp commonLeft) formalAvailable,
        ∃ reserveEnvironment, ∃ reserve : WorldEnvironmentProvenance strata U reserveEnvironment,
          Sponsored [originalCallWorld controls .assignedComparison rightNode captured] reserve.worlds ∧
          Sponsored [originalCallWorld controls .assignedComparison rightNode baseline] reserve.worlds ∧
          Nonempty (WorldCallFrameData (P := P) (base := ownBase) (caps := ownBase.initialCaps)
            (display := destination.display formalGraph) (controls.atHeader origin.constructorOrigin)
            reserve frontier realization) := by
  obtain ⟨frame, captured, sameFrame, sameCaptured, frameData, history, sourceEq, domainEq, headerEq,
      headerWorld, headerEmpty, whole, boundary, coherent, wholePaidLocal, wholePaid,
      firstReserveEnvironment, firstReserve, firstPaidLocal, firstPaid, ⟨firstReply⟩⟩ :=
    bootstrap.captureFirstFormalWorld rightHead rightGraph displayedEq controls baseline frontier answer input arguments
      origin destination field fieldEq paid henv hscoped formed sourceClosed bank unary
  let firstGraph := OriginalCaptureMap.identity
    ((bootstrap.firstLocation (arguments := arguments)).contextDerivation input.provenance.initial)
  let sourceFrame : OriginalTypeRouteFrame env registry target firstGraph
      (rightRaw.comp commonLeft) (rightRaw.comp commonLeft) :=
    ⟨_, _, ⟨frame, input.substitutions⟩, input.closed⟩
  let ownBase := frame.captureBase input.substitutions
  let generation := frameData.generation input.substitutions
  obtain ⟨ready⟩ := frameData.controlled input.substitutions
  let hereditary := frameData.generation_hereditary input.substitutions
  let sourceEnvironment : history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered =
      frame.dependencyEnvironment controls.ordered :=
    congrArg (fun f : OriginalTypeRouteFrame env registry target firstGraph
      (rightRaw.comp commonLeft) (rightRaw.comp commonLeft) => f.realization.frame.dependencyEnvironment controls.ordered) sourceEq
  let sourceData : WorldBoundaryFrame.ExecutionData P ownBase ownBase.initialCaps frontier
      ⟨history.sourceFrame.box, controls, transportWorld sourceEnvironment.symm captured⟩ := by
    have localData (f : OriginalTypeRouteFrame env registry target firstGraph
        (rightRaw.comp commonLeft) (rightRaw.comp commonLeft)) (same : f = sourceFrame) :
        WorldBoundaryFrame.ExecutionData P ownBase ownBase.initialCaps frontier
          ⟨f.box, controls, transportWorld
            (congrArg (fun x => x.realization.frame.dependencyEnvironment controls.ordered) same).symm captured⟩ := by
      subst f
      exact ⟨generation, trivial, ready, ⟨rfl,rfl⟩, Covered.refl _, hereditary⟩
    exact localData history.sourceFrame sourceEq
  let headerControls := controls.atHeader origin.constructorOrigin
  let emptyGeneration : WorldGenerated strata P ownBase ownBase.initialCaps
      (rightRaw.comp commonLeft) (rightRaw.comp commonLeft) (destination.nativeSide rightSource).graph
      (closedTypeRouteFrame (ContextDerivation.nil (env := origin.types) (U := U)) rightSource env registry target
        (rightRaw.comp commonLeft) (rightRaw.comp commonLeft)).realization.frame.raw headerControls :=
    .empty rightSource _ _ (origin.typesBelow.trans input.sourceBelow)
      (sourceClosed _ (origin.typesBelow.trans input.sourceBelow)) headerControls
  let priorData : WorldBoundaryFrame.ExecutionData P ownBase ownBase.initialCaps frontier
      ⟨history.headerFrame.box, headerControls, headerWorld⟩ := by
    have localData (f : OriginalTypeRouteFrame env registry target (destination.nativeSide rightSource).graph
        (rightRaw.comp commonLeft) (rightRaw.comp commonLeft))
        (same : f = closedTypeRouteFrame (ContextDerivation.nil (env := origin.types) (U := U)) rightSource env registry target
          (rightRaw.comp commonLeft) (rightRaw.comp commonLeft))
        (world : WorldEnvironmentProvenance strata U (f.realization.frame.dependencyEnvironment headerControls.ordered)) :
        WorldBoundaryFrame.ExecutionData P ownBase ownBase.initialCaps frontier ⟨f.box, headerControls, world⟩ := by
      subst f
      exact ⟨emptyGeneration, trivial,
        ⟨.nil, by intro control active; exact Nat.zero_le _, by intro child member; cases member⟩,
        ⟨rfl,rfl⟩, (by intro child member; cases member), ⟨trivial, .nil, trivial⟩⟩
    exact localData history.headerFrame headerEq headerWorld
  let firstSide := originalApplicationTypeRouteSide input.provenance.initial bootstrap.backward.firstDomain
    bootstrap.backward.firstBody bootstrap.backward.firstFunction bootstrap.backward.firstArgument bootstrap.backward.firstResult
    bootstrap.backward.firstHu bootstrap.backward.firstHv (bootstrap.firstLocation (arguments := arguments)) firstGraph
  let selectedFrame : OriginalTypeRouteFrame env registry target (destination.secondSide firstSide).graph
      (rightRaw.comp commonLeft) (rightRaw.comp commonLeft) :=
    ⟨firstReply.locals, firstReply.available, firstReply.realization, firstReply.hereditary.tablesClosed.closed⟩
  let selected := firstReply.generation.environment
  let selectedData : WorldBoundaryFrame.ExecutionData P ownBase ownBase.initialCaps frontier
      ⟨selectedFrame.box, headerControls, selected⟩ :=
    ⟨firstReply.generation, firstReply.replayable, firstReply.controlled, firstReply.compatible,
      Covered.refl _, firstReply.hereditary⟩
  have selectedPaid : Sponsored [originalCallWorld controls .assignedComparison rightNode captured] selected.worlds :=
    sponsored_covered firstReply.covered firstPaidLocal
  obtain ⟨nextFrame, nextEnvironment, ⟨nextData⟩⟩ :=
    identityExecutionRecontext (firstContext (arguments := arguments) (bootstrap := bootstrap)) controls frontier
      frame captured frameData input.substitutions input.closed
  have noBinders : (bootstrap.firstLocation (arguments := arguments)).binderPrefix = [] :=
    Located.sameSource_prefix_nil _
  have sourceBound : ∀ ordered, environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost ((bootstrap.firstLocation (arguments := arguments)).dependencyEnvironment ordered
        (frame.dependencyEnvironment controls.ordered)) := by
    intro ordered
    rw [show history.sourceFrame.realization.frame.dependencyEnvironment ordered =
        frame.dependencyEnvironment controls.ordered from sourceEnvironment,
      Located.dependencyEnvironment_of_prefix_nil ordered _ noBinders]
    exact Nat.le_refl _
  have capacity : environmentCost (frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment := by
    rw [frameEnvironmentOfHEq (firstContext (arguments := arguments) (bootstrap := bootstrap)) sameFrame]
    exact bootstrap.capacity
  have covered : Covered (@EquationControlMeasure.Less strata.rules.length) captured.worlds baseline.worlds := by
    rw [worldsOfHEq (frameEnvironmentOfHEq (firstContext (arguments := arguments) (bootstrap := bootstrap)) sameFrame controls.ordered) sameCaptured]
    exact bootstrap.covered
  obtain ⟨reserveEnvironment, reserve, reserveLocal, reservePaid, ⟨secondReply⟩⟩ :=
    destination.captureSecondArgumentWorld rightHead fieldEq (Located.here) controls captured origin
      input.provenance.initial bootstrap.backward.firstDomain bootstrap.backward.firstBody bootstrap.backward.firstFunction
      bootstrap.backward.firstArgument bootstrap.backward.firstResult bootstrap.backward.firstHu bootstrap.backward.firstHv
      (bootstrap.firstLocation (arguments := arguments)) firstGraph history sourceEnvironment headerWorld
      (by intro child member; rw [headerEmpty] at member; cases member)
      whole wholePaidLocal boundary coherent noBinders sourceBound (origin.typesBelow.trans input.sourceBelow)
      sourceData priorData selectedFrame selected selectedPaid selectedData
      bootstrap.domain bootstrap.body bootstrap.function bootstrap.argument bootstrap.result bootstrap.domainWF bootstrap.bodyWF
      bootstrap.location (.identity (bootstrap.location.contextDerivation input.provenance.initial))
      nextFrame nextEnvironment nextData rfl baseline capacity covered paid henv hscoped formed bank unary
  refine ⟨frame, captured, sameFrame, sameCaptured, frameData, ?_⟩
  let actualGraph := OriginalCaptureMap.capture (destination.secondSide firstSide).graph destination.secondDomain
    (.identity (bootstrap.location.contextDerivation input.provenance.initial)) bootstrap.argument
    (.ofLocation (.appArgument bootstrap.location) input.provenance.initial)
  let conclusion (first second : VExpr) : Prop :=
    ∃ formalGraph : OriginalCaptureMap (common := rightSource) destination.context
        ((Subst.id.cons first).cons second),
      ∃ formalLocals formalAvailable,
      ∃ realization : OriginalCaptureRealization formalGraph env registry target formalLocals
          (rightRaw.comp commonLeft) (rightRaw.comp commonLeft) formalAvailable,
      ∃ reserveEnvironment, ∃ reserve : WorldEnvironmentProvenance strata U reserveEnvironment,
        Sponsored [originalCallWorld controls .assignedComparison rightNode captured] reserve.worlds ∧
        Sponsored [originalCallWorld controls .assignedComparison rightNode baseline] reserve.worlds ∧
        Nonempty (WorldCallFrameData (P := P) (base := ownBase) (caps := ownBase.initialCaps)
          (display := destination.display formalGraph) headerControls reserve frontier realization)
  have package : conclusion (a.subst .id) (p.subst .id) := by
    refine ⟨actualGraph, secondReply.locals, secondReply.available, secondReply.realization,
      reserveEnvironment, reserve, reserveLocal, reservePaid, ?_⟩
    exact ⟨⟨secondReply.generation, secondReply.replayable, secondReply.controlled, secondReply.compatible,
      secondReply.hereditary.tablesClosed.closed, secondReply.capacity headerControls.ordered,
      secondReply.covered, secondReply.hereditary⟩⟩
  have finalPackage : conclusion a p := ((congrArg (fun first => conclusion first (p.subst .id)) (subst_id (e := a))).trans
    (congrArg (conclusion a) (subst_id (e := p)))) ▸ package
  exact finalPackage
end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
