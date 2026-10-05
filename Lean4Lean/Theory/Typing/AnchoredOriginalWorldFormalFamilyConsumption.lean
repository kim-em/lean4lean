import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFormalFamilyReindex
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldTracedTwoVariableFamily

/-! Run the checked two-variable compiler on exactly the formal frame
selected by R. Its original captures may have changed; the returned actual
coverage and hereditary history are used to fund and build the diagonal. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
open private from_right from Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls
open private inheritedCall from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecordMajorBridge
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem FormalFamilyDestination.consumeSelectedWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    (origin : VEnv.ProjectionParameterOrigin sourceEnv name info)
    (controls : OriginalWorldControls strata sourceEnv)
    {levels : List VLevel} {C D : VExpr}
    {signature : ConstantTelescope (origin.family.type.instL levels)}
    {domains : signature.domains = [C,D]}
    (destination : FormalFamilyDestination (U := U) origin signature domains)
    (graph : OriginalCaptureMap (common := common) destination.context
      ((Subst.id.cons first).cons second))
    (baseline : WorldEnvironmentProvenance strata U formalEnvironment)
    (frontier : List (World strata.rules.length))
    (caller : EndpointState sourceEnv U source callerExpression callerAssigned)
    (callerWorld : WorldEnvironmentProvenance strata U callerEnvironment)
    (other : World strata.rules.length)
    {demand : FamilyData (Profile q)} {profile : Profile (q+1)}
    (reply : AmbientBoundedGeneratedQueryReply base caps (destination.display graph)
      commonLeft commonRight profile (environmentCost formalEnvironment))
    (data : WorldGeneratedQueryReplyData (P := P) (controls.atHeader origin.constructorOrigin)
      baseline frontier reply)
    (certificate : RichCert origin.types env U registry target destination.node
      reply.answer.reply.locals (((Subst.id.cons first).cons second).comp commonLeft)
      relevant profile footprint)
    (ready : ControlledStoredQuery (controls.atHeader origin.constructorOrigin) frontier (.certificate certificate))
    (resources : footprint.Available reply.answer.reply.available)
    (inherited : Sponsored [originalCallWorld controls .assignedComparison caller callerWorld] baseline.worlds)
    (paid : Sponsored frontier [other, originalCallWorld controls .assignedComparison caller callerWorld])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [other, originalCallWorld controls .assignedComparison caller callerWorld]))
    (member : (show Atom (q+1) from .family demand) ∈ profile.atoms)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (sourceClosed : ∀ next ≤ env, P next)
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none) :
    ∃ nextFootprint,
    ∃ output : RichCert origin.types env U registry target destination.node
        reply.answer.reply.locals (((Subst.id.cons first).cons second).comp commonLeft) relevant
        (.singleton (show Atom (q+1) from .family demand)) nextFootprint,
    ∃ _outputReady : ControlledStoredQuery (controls.atHeader origin.constructorOrigin) frontier (.certificate output),
      nextFootprint.Available reply.answer.reply.available ∧
      WorldFamilyRequestProperty (controls.atHeader origin.constructorOrigin) frontier
        (.left destination.original) registry target reply.answer.reply.locals
        (((Subst.id.cons first).cons second).comp commonLeft) reply.answer.reply.available
        name levels [.bvar 1, .bvar 0] demand := by
  let frame := reply.answer.reply.realization.frame
  let formalControls := controls.atHeader origin.constructorOrigin
  obtain ⟨unaryData⟩ := WorldUnaryFrameData.ofGenerated frame data.generation data.controlled
    data.replayable data.compatible data.hereditary
  let captured := frame.diagonalWorld formalControls data.generation.environment
  have capturedPaid : Sponsored [originalCallWorld controls .assignedComparison caller callerWorld] captured.worlds := by
    intro child member
    rw [OriginalRichFrame.diagonalWorld_worlds] at member
    obtain ⟨original, present, equal | smaller⟩ := data.covered child member
    · cases equal
      exact inherited _ present
    · obtain ⟨parent, parentMember, parentBelow⟩ := inherited original present
      exact ⟨parent, parentMember, EquationWorldClosureOrder.trans
        (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans
        smaller parentBelow⟩
  have childBelow := ProjectionParameterOrigin.formalNode_below origin controls destination.node captured
    caller callerWorld .fundamental .assignedComparison capturedPaid
  obtain ⟨smaller, sponsored⟩ := inheritedCall frontier (from_right (by
      intro child member
      cases List.mem_singleton.mp member
      exact childBelow)) paid (by
    intro child member
    cases List.mem_singleton.mp member
    exact ⟨_, by simp, childBelow⟩)
  have childBank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld formalControls .fundamental destination.node captured]) :=
    fun budget lower => bank budget (lower.trans smaller)
  exact EndpointRef.tracedTwoVariableFamilyWorld (.left destination.original) destination.context
    formalControls frontier frame.leftDiagonal captured unaryData.leftDiagonal reply.answer.reply.closed
    reply.answer.reply.realization.substitutions.left ready resources
    data.generation.erase.ambientGenerated.ambient.1.below sponsored childBank member
    henv hscoped formed sourceClosed notDefinition notNative

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
