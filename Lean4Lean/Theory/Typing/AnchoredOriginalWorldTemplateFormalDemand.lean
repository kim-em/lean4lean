import Lean4Lean.Theory.Typing.AnchoredOriginalWorldTemplateFormalFamilyRequests

/-! The original P demand is recovered from the actual independent major
reply. Both formal captures and the caller/formal/caller replay are computed
from the same reply and the outer induction banks. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 3400000

section
variable
  {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
  {initial : ContextDerivation sourceEnv U rootSource}
  {domain : EndpointRef sourceEnv U source E (.sort u)}
  {body : EndpointState sourceEnv U (E :: source) F (.sort v)}
  {function : EndpointState sourceEnv U source (.app (.const name leftLevels) leftA) (.forallE E F)}
  {argument : EndpointState sourceEnv U source leftP E}
  {result : EndpointState sourceEnv U source (F.inst leftP) (.sort v)}
  {hu : u.WF U} {hv : v.WF U}
  {location : Located root (.app hu hv (.ref domain) body function argument result)}
  {frame : OriginalRichFrame sourceEnv env U registry target
    (location.contextDerivation initial) locals σ τ available}
  {substitutions : Ctx.SubstEq env U target σ τ source}
  {strata : EquationStratification env} {P : VEnv → Prop}
  {leftControls : OriginalWorldControls strata sourceEnv}
  {leftWorld : WorldEnvironmentProvenance strata U leftEnvironment}
  {frontier : List (World strata.rules.length)}
  {extraQuery : RichGradedResult sourceEnv env U registry target argument locals σ available (extra : Profile m)}
  {queryLevels : List VLevel}
  {queryWF : ∀ level ∈ queryLevels, level.WF U}
  (packet : WorldTwoParameterBackward initial domain body function argument result hu hv location frame substitutions
    P leftControls leftWorld frontier (profile : Profile n) relevant extraQuery info queryWF)

/-- This consumes the SAME enriched comparison result. In particular the
bootstrap histories, formal frame, and demanded right observer are outputs,
not alignment or semantic premises. -/
theorem WorldTwoParameterBackward.rightExtraQueryFromMajorWorld
    (declaredC declaredD : VExpr)
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {leftDisplay : OriginalNestedDisplay U common leftExpression leftAssigned}
    (leftNode : EndpointState sourceEnv U source leftOuterExpression leftOuterAssigned)
    {rightNode : EndpointState rightEnv U rightSource (.proj name index rightValue) rightAssigned}
    (rightHead : ProjectionHead rightNode)
    {rightContext : ContextDerivation rightEnv U rightSource}
    (rightGraph : OriginalCaptureMap (common := common) rightContext rightRaw)
    (displayedEq : displayed = rightValue.subst rightRaw)
    (controls : OriginalWorldControls strata rightEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (answer : WorldTemplateAssignedReply (P := P) base caps leftDisplay
      (OriginalNestedDisplay.recordBridgeReference rightGraph (.right rightHead.major) displayedEq)
      commonLeft commonRight controls baseline frontier
      (.singleton (n := packet.first.request.rank+1)
        (.family ⟨name,queryLevels,familyRelevant,[packet.firstDeclared declaredC,packet.secondDeclared declaredD]⟩)))
    (code : TemplateAssignedResult env U registry target leftDisplay.node (.ref (.right rightHead.major))
      answer.reply.reply.answer.reply.locals (leftDisplay.raw.comp commonLeft) (rightRaw.comp commonLeft)
      answer.reply.reply.answer.reply.available familyRelevant
      (.singleton (n := packet.first.request.rank+1)
        (.family ⟨name,queryLevels,familyRelevant,[packet.firstDeclared declaredC,packet.secondDeclared declaredD]⟩)))
    (ready : ControlledStoredQuery controls frontier (.certificate code.certificate))
    (arguments : rightHead.parameters ++ rightHead.indices = [rightA,rightP])
    (origin : ProjectionParameterOrigin rightEnv name rightHead.info)
    {signature : ConstantTelescope (origin.family.type.instL rightHead.levels)}
    {domains : signature.domains = [C,D]}
    (destination : FormalFamilyDestination (U := U) origin signature domains)
    (field : EndpointRef rightEnv U rightSource rightHead.fieldType (.sort rightHead.fieldLevel))
    (fieldEq : rightHead.field = .ref field)
    (paid : Sponsored frontier
      [originalCallWorld leftControls .assignedComparison leftNode leftWorld,
       originalCallWorld controls .assignedComparison rightNode baseline])
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (sourceClosed : ∀ source, source ≤ env → P source)
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    (bank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld leftControls .assignedComparison leftNode leftWorld,
        originalCallWorld controls .assignedComparison rightNode baseline]))
    (unary : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld leftControls .assignedComparison leftNode leftWorld,
        originalCallWorld controls .assignedComparison rightNode baseline])) :
    ∃ nominal : WorldRichFamilySourceRequest controls frontier (.right rightHead.major) registry target
        answer.reply.reply.answer.reply.locals (rightRaw.comp commonLeft)
        answer.reply.reply.answer.reply.available rightP (packet.secondDeclared declaredD),
    ∃ query : RichFamilyArgumentQuery (.right rightHead.major) env registry target rightSource
        answer.reply.reply.answer.reply.locals (rightRaw.comp commonLeft)
        answer.reply.reply.answer.reply.available rightP extra,
    ∃ output : ControlledStoredQuery controls frontier (.observation query.query.observation),
      query.assigned = nominal.argument.assigned ∧
      HEq query.node nominal.argument.node ∧ HEq query.location nominal.argument.location ∧
      query.query.rank = nominal.argument.query.rank ∧
      query.query.footprint = nominal.argument.query.footprint ∧
      output.annotation.worlds = nominal.controlled.annotation.worlds ∧
      (∀ policy, query.query.observation.headDepth policy = nominal.argument.query.observation.headDepth policy) := by
  have initializedInput : Nonempty answer.FormationInput := WorldTemplateAssignedReply.initializeProjectionMajor rightHead rightGraph displayedEq controls baseline frontier answer
    leftNode leftControls leftWorld paid unary
  let input : answer.FormationInput := Classical.choice initializedInput
  have initialized : Nonempty (WorldTemplateMajorBackwardInitialization (answer := answer) input
      (congrArg (mkApps (.const name rightHead.levels)) arguments) rightHead.levelsWF) :=
    WorldTemplateAssignedReply.initializeProjectionMajorBackward rightHead rightGraph displayedEq controls baseline frontier answer
    input arguments leftNode leftControls leftWorld bank henv hscoped formed sourceClosed
  let bootstrap : WorldTemplateMajorBackwardInitialization (answer := answer) input
      (congrArg (mkApps (.const name rightHead.levels)) arguments) rightHead.levelsWF := Classical.choice initialized
  have requests := WorldTemplateMajorBackwardInitialization.familyRequestsWorld
    (family := ⟨name,queryLevels,familyRelevant,[packet.firstDeclared declaredC,packet.secondDeclared declaredD]⟩) rightHead rightGraph displayedEq controls baseline frontier
    answer input arguments bootstrap origin destination field fieldEq
    (originalCallWorld leftControls .assignedComparison leftNode leftWorld) paid code ready
    (List.mem_singleton_self _)
    henv hscoped formed sourceClosed notDefinition notNative bank unary
  exact packet.rightExtraQueryWorld declaredC declaredD controls frontier requests henv hscoped formed

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
