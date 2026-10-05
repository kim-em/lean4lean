import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFormalFamilyConsumption
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFormalFamilyCallerRequests

/-! The complete caller/formal/caller query path. The only formal input is
the actual positive parameter-capture frame and its funded retained worlds.
The initial R, complete charged compiler, and both parameter return R calls
are executed here, preserving the incoming finite family demand. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
open private sourceProvenance from Lean4Lean.Theory.Typing.AnchoredOriginalWorldFormalFamilyRequestReplay
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

theorem FormalFamilyDestination.callerFamilyRequestsWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    (base : OriginalCaptureBase env U registry target)
    {outer : EndpointState base.sourceEnv U base.source (.proj name field major) assigned}
    (head : ProjectionHead outer)
    (origin : VEnv.ProjectionParameterOrigin base.sourceEnv name info)
    {levels : List VLevel} {C D : VExpr}
    {signature : ConstantTelescope (origin.family.type.instL levels)}
    {domains : signature.domains = [C,D]}
    (destination : FormalFamilyDestination (U := U) origin signature domains)
    {callerNode : EndpointState base.sourceEnv U base.source (.app (.app (.const name levels) a) p) callerAssigned}
    (location : Located (.right head.major) callerNode)
    (formalGraph : OriginalCaptureMap (common := base.source) destination.context
      ((Subst.id.cons a).cons p))
    (controls : OriginalWorldControls strata base.sourceEnv)
    (callerWorld : WorldEnvironmentProvenance strata U callerEnvironment)
    (formalBaseline : WorldEnvironmentProvenance strata U formalEnvironment)
    (frontier : List (World strata.rules.length)) (other : World strata.rules.length)
    (callerData : WorldCallFrameData (P := P) (base := base) (caps := base.initialCaps)
      (display := OriginalNestedDisplay.identity base (.ref (.right head.major))
        (.ofLocation .here base.context)) controls callerWorld frontier base.identityRealization)
    (formalFrame : OriginalCaptureRealization formalGraph env registry target
      formalLocals base.left base.right formalAvailable)
    (formalData : WorldCallFrameData (P := P) (base := base) (caps := base.initialCaps)
      (display := destination.display formalGraph) (controls.atHeader origin.constructorOrigin)
      formalBaseline frontier formalFrame)
    (inherited : Sponsored [originalCallWorld controls .assignedComparison outer callerWorld] formalBaseline.worlds)
    (paid : Sponsored frontier [other, originalCallWorld controls .assignedComparison outer callerWorld])
    {family : FamilyData (Profile q)} {profile : Profile (q+1)}
    (certificate : RichCert base.sourceEnv env U registry target callerNode base.locals base.left
      relevant profile footprint)
    (ready : ControlledStoredQuery controls frontier (.certificate certificate))
    (resources : footprint.Available base.available)
    (member : (show Atom (q+1) from .family family) ∈ profile.atoms)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (sourceClosed : ∀ next ≤ env, P next)
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    (bank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [other, originalCallWorld controls .assignedComparison outer callerWorld]))
    (unary : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [other, originalCallWorld controls .assignedComparison outer callerWorld])) :
    WorldFamilyRequestProperty controls frontier (.right head.major) registry target
      base.locals base.left base.available name levels [a,p] family := by
  let callerDisplay := OriginalNestedDisplay.identity base callerNode (sourceProvenance location base.context)
  let formalDisplay := destination.display formalGraph
  let formalControls := controls.atHeader origin.constructorOrigin
  have actualCallerData : WorldCallFrameData (P := P) (base := base) (caps := base.initialCaps)
      (display := callerDisplay) controls callerWorld frontier base.identityRealization :=
    ⟨callerData.generation, callerData.replayable, callerData.controlled, callerData.compatible,
      callerData.closed, callerData.capacity, callerData.covered, callerData.hereditary⟩
  obtain ⟨smaller, sponsored⟩ := FormalFamilyDestination.reindexFunding
    (head := head) (origin := origin) (destination := destination) (location := location)
    controls callerWorld formalBaseline frontier other inherited paid
  obtain ⟨reply, ⟨data⟩⟩ := bank.observation _ smaller base base.initialCaps callerDisplay formalDisplay
    base.left base.right controls formalControls rfl rfl callerWorld formalBaseline frontier rfl sponsored
    base.identityRealization actualCallerData formalFrame formalData (.code certificate) resources ready.code
  obtain ⟨nextFootprint, formalCode, formalReady, formalResources, _⟩ :=
    reply.answer.reply.query.code_controlled henv formalControls data.query certificate.formed
  obtain ⟨_, _, _, _, requests⟩ := destination.consumeSelectedWorld origin controls formalGraph
    formalBaseline frontier outer callerWorld other reply data formalCode formalReady formalResources
    inherited paid unary member henv hscoped formed sourceClosed notDefinition notNative
  have selectedData : WorldCallFrameData (P := P) (base := base) (caps := base.initialCaps)
      (display := formalDisplay) formalControls formalBaseline frontier reply.answer.reply.realization :=
    ⟨data.generation, data.replayable, data.controlled, data.compatible, reply.answer.reply.closed,
      reply.bounded formalControls.ordered, data.covered, data.hereditary⟩
  let outerApplication := applicationPrefix location
  let innerApplication := applicationPrefix (Located.appFunction outerApplication.view.location)
  exact destination.callerRequestsWorld base head origin formalGraph controls callerWorld formalBaseline frontier other
    callerData reply.answer.reply.realization selectedData inherited paid henv hscoped formed bank
    innerApplication.view.argument (.appArgument innerApplication.view.location)
    outerApplication.view.argument (.appArgument outerApplication.view.location) requests

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
