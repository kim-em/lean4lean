import Lean4Lean.Theory.Typing.AnchoredOriginalWorldTemplateFormalCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFormalFamilyRoundTrip
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldTwoParameterDemandExtraction
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
open private firstContext from Lean4Lean.Theory.Typing.AnchoredOriginalWorldTemplateFirstFormalCapture
open private frameEnvironmentOfHEq worldsOfHEq from Lean4Lean.Theory.Typing.AnchoredOriginalWorldTemplateFormalCapture
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3400000

private theorem castInputCode
    {strata : EquationStratification env}
    {node : EndpointState sourceEnv U source expression assigned}
    (equal : expression = next)
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (controls : OriginalWorldControls strata sourceEnv) (frontier : List (World strata.rules.length))
    (ready : ControlledStoredQuery controls frontier (.certificate certificate)) :
    ∃ nextCertificate : RichCert sourceEnv env U registry target (node.cast equal rfl)
        locals σ relevant profile footprint,
      Nonempty (ControlledStoredQuery controls frontier (.certificate nextCertificate)) := by
  cases equal
  exact ⟨certificate, ⟨ready⟩⟩

private theorem dropFirstWorld
    (frontier : List (World count)) (first second : World count) :
    CallBelow count (frontier ++ [second]) (frontier ++ [first,second]) := by
  induction frontier with
  | nil => exact Relation.TransGen.single (.head (replacement := []) (by intro child member; cases member))
  | cons value rest ih => exact ih.cons value
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
      commonLeft commonRight controls baseline frontier (profile : Profile (q+1)))
    (input : answer.FormationInput)
    (arguments : rightHead.parameters ++ rightHead.indices = [a, p])
    (bootstrap : WorldTemplateMajorBackwardInitialization input
      (congrArg (mkApps (.const name rightHead.levels)) arguments) rightHead.levelsWF)


include bootstrap

/-- Construct both formal captures, execute the caller/formal/caller R path,
and expose the requested finite family resources in the SAME caller table. -/
theorem WorldTemplateMajorBackwardInitialization.familyRequestsWorld
    (origin : ProjectionParameterOrigin rightEnv name rightHead.info)
    {signature : ConstantTelescope (origin.family.type.instL rightHead.levels)}
    {domains : signature.domains = [C,D]}
    (destination : FormalFamilyDestination (U := U) origin signature domains)
    (field : EndpointRef rightEnv U rightSource rightHead.fieldType (.sort rightHead.fieldLevel))
    (fieldEq : rightHead.field = .ref field)
    (other : World strata.rules.length)
    (paid : Sponsored frontier [other, originalCallWorld controls .assignedComparison rightNode baseline])
    (code : TemplateAssignedResult env U registry target leftDisplay.node (EndpointState.ref (.right rightHead.major))
      answer.reply.reply.answer.reply.locals (leftDisplay.raw.comp commonLeft) (rightRaw.comp commonLeft)
      answer.reply.reply.answer.reply.available relevant profile)
    (ready : ControlledStoredQuery controls frontier (.certificate code.certificate))
    {family : FamilyData (Profile q)}
    (member : (show Atom (q+1) from .family family) ∈ profile.atoms)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (sourceClosed : ∀ source, source ≤ env → P source)
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    (bank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [other, originalCallWorld controls .assignedComparison rightNode baseline]))
    (unary : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [other, originalCallWorld controls .assignedComparison rightNode baseline])) :
    WorldFamilyRequestProperty controls frontier (.right rightHead.major) registry target
      answer.reply.reply.answer.reply.locals (rightRaw.comp commonLeft)
      answer.reply.reply.answer.reply.available name rightHead.levels [a,p] family := by
  have onlyPaid : Sponsored frontier [originalCallWorld controls .assignedComparison rightNode baseline] := by
    intro child present
    cases List.mem_singleton.mp present
    exact paid _ (by simp)
  have dropped := dropFirstWorld frontier other (originalCallWorld controls .assignedComparison rightNode baseline)
  have smallerBank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .assignedComparison rightNode baseline]) :=
    fun calls below => bank calls (below.trans dropped)
  have smallerUnary : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .assignedComparison rightNode baseline]) :=
    fun calls below => unary calls (below.trans dropped)
  obtain ⟨frame, captured, sameFrame, sameCaptured, frameData, formalGraph, formalLocals, formalAvailable,
      formalFrame, formalEnvironment, formalBaseline, inheritedLocal, inherited, ⟨formalData⟩⟩ :=
    WorldTemplateMajorBackwardInitialization.captureFormalParametersWorld rightHead rightGraph displayedEq controls baseline frontier answer input arguments bootstrap
      origin destination field fieldEq onlyPaid henv hscoped formed sourceClosed smallerBank smallerUnary
  let ownBase := frame.captureBase input.substitutions
  let generation := frameData.generation input.substitutions
  obtain ⟨frameReady⟩ := frameData.controlled input.substitutions
  have capacity : environmentCost (frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment := by
    rw [frameEnvironmentOfHEq (firstContext (arguments := arguments) (bootstrap := bootstrap)) sameFrame]
    exact bootstrap.capacity
  have covered : Covered (@EquationControlMeasure.Less strata.rules.length) captured.worlds baseline.worlds := by
    rw [worldsOfHEq (frameEnvironmentOfHEq (firstContext (arguments := arguments) (bootstrap := bootstrap)) sameFrame controls.ordered) sameCaptured]
    exact bootstrap.covered
  let callerData : WorldCallFrameData (P := P) (base := ownBase) (caps := ownBase.initialCaps)
      (display := OriginalNestedDisplay.identity ownBase (.ref (.right rightHead.major))
        (.ofLocation .here ownBase.context)) controls baseline frontier ownBase.identityRealization :=
    ⟨generation, trivial, frameReady, ⟨rfl,rfl⟩, input.closed, capacity, covered,
      frameData.generation_hereditary input.substitutions⟩
  let expressionEq := congrArg (mkApps (.const name rightHead.levels)) arguments
  obtain ⟨callerCode, ⟨callerReady⟩⟩ := castInputCode expressionEq code.certificate controls frontier ready
  exact destination.callerFamilyRequestsWorld ownBase rightHead origin
    (input.provenance.location.castExpression expressionEq) formalGraph controls baseline formalBaseline frontier other
    callerData formalFrame formalData inherited paid callerCode callerReady code.resources member
    henv hscoped formed sourceClosed notDefinition notNative bank unary

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
