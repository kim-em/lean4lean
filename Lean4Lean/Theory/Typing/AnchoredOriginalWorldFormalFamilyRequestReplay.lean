import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFormalFamilyReindex
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyRequest

/-! Return an actual formal parameter observer to its arbitrary caller
operand. The formal parameter is interpreted by its positive capture map;
ordinary R is used only after that map proves exact expression agreement. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
open private from_right from Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls
open private inheritedCall from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecordMajorBridge
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

private theorem suffixLength
    {first : ContextDerivation sourceEnv U firstSource}
    {last : ContextDerivation sourceEnv U lastSource}
    (suffix : ContextDerivation.Suffix first last) : firstSource.length ≤ lastSource.length := by
  induction suffix with
  | refl => exact Nat.le_refl _
  | cons previous ih => exact Nat.le_trans ih (by simp)

private theorem sameSourceContext
    {first last : ContextDerivation sourceEnv U source}
    (suffix : ContextDerivation.Suffix first last) : first = last := by
  cases suffix with
  | refl => rfl
  | cons previous =>
    have bound := suffixLength previous
    simp only [List.length_cons] at bound
    omega

private noncomputable def sourceProvenance
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned}
    (location : Located root node) (context : ContextDerivation sourceEnv U source) :
    EndpointProvenance context node := {
  rootSource := source, rootExpression := rootExpression, rootType := rootType
  root := root, initial := context, location := location
  context_eq := sameSourceContext (Classical.choice (location.contextDerivation_suffix context)) }

/-- This consumes the computed request on the selected formal frame. It
does not require the arbitrary caller term to have been a variable, nor
does it reinterpret a query under different equation controls. -/
theorem FormalFamilyDestination.replayParameterWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {outer : EndpointState sourceEnv U source (.proj name field major) assigned}
    (head : ProjectionHead outer)
    (origin : VEnv.ProjectionParameterOrigin sourceEnv name info)
    {levels : List VLevel} {C D : VExpr}
    {signature : ConstantTelescope (origin.family.type.instL levels)}
    {domains : signature.domains = [C,D]}
    (destination : FormalFamilyDestination (U := U) origin signature domains)
    (firstParameter : Bool)
    (callerArgument : EndpointState sourceEnv U source (if firstParameter then a else p) argumentType)
    (location : Located (.right head.major) callerArgument)
    (initial : ContextDerivation sourceEnv U source)
    (callerGraph : OriginalCaptureMap (common := common) (location.contextDerivation initial) callerRaw)
    (formalGraph : OriginalCaptureMap (common := common) destination.context
      ((Subst.id.cons (a.subst callerRaw)).cons (p.subst callerRaw)))
    (controls : OriginalWorldControls strata sourceEnv)
    (callerWorld : WorldEnvironmentProvenance strata U callerEnvironment)
    (formalBaseline : WorldEnvironmentProvenance strata U formalEnvironment)
    (frontier : List (World strata.rules.length)) (other : World strata.rules.length)
    (callerFrame : OriginalCaptureRealization callerGraph env registry target
      callerLocals commonLeft commonRight callerAvailable)
    (callerData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := OriginalNestedDisplay.ofOccurrence initial location callerGraph)
      controls callerWorld frontier callerFrame)
    (formalFrame : OriginalCaptureRealization formalGraph env registry target
      formalLocals commonLeft commonRight formalAvailable)
    (formalData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := destination.display formalGraph) (controls.atHeader origin.constructorOrigin)
      formalBaseline frontier formalFrame)
    (nominal : WorldRichFamilySourceRequest (controls.atHeader origin.constructorOrigin) frontier
      (.left destination.original) registry target formalLocals
      (((Subst.id.cons (a.subst callerRaw)).cons (p.subst callerRaw)).comp commonLeft)
      formalAvailable (.bvar (if firstParameter then 1 else 0)) (request : DataRequest (Profile n)))
    (inherited : Sponsored [originalCallWorld controls .assignedComparison outer callerWorld] formalBaseline.worlds)
    (paid : Sponsored frontier [other, originalCallWorld controls .assignedComparison outer callerWorld])
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (bank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [other, originalCallWorld controls .assignedComparison outer callerWorld])) :
    ∃ reply : AmbientBoundedGeneratedQueryReply base caps
        (OriginalNestedDisplay.ofOccurrence initial location callerGraph) commonLeft commonRight request.input
        (environmentCost callerEnvironment),
      Nonempty (WorldGeneratedQueryReplyData (P := P) controls callerWorld frontier reply) := by
  let formalControls := controls.atHeader origin.constructorOrigin
  let selected := formalData.generation.environment
  let callerDisplay := OriginalNestedDisplay.ofOccurrence initial location callerGraph
  let formalDisplay : OriginalNestedDisplay U common
      ((if firstParameter then a else p).subst callerRaw)
      (nominal.argument.assigned.subst ((Subst.id.cons (a.subst callerRaw)).cons (p.subst callerRaw))) := {
    sourceEnv := origin.types, source := [D,C]
    sourceExpression := .bvar (if firstParameter then 1 else 0)
    sourceType := nominal.argument.assigned
    context := destination.context, node := nominal.argument.node
    provenance := sourceProvenance nominal.argument.location destination.context
    raw := (Subst.id.cons (a.subst callerRaw)).cons (p.subst callerRaw)
    graph := formalGraph
    expression_eq := by cases firstParameter <;> rfl
    type_eq := rfl }
  have selectedPaid : Sponsored [originalCallWorld controls .assignedComparison outer callerWorld] selected.worlds := by
    intro child member
    obtain ⟨original, present, equal | smaller⟩ := formalData.covered child member
    · cases equal
      exact inherited _ present
    · obtain ⟨parent, parentMember, parentBelow⟩ := inherited original present
      exact ⟨parent, parentMember, EquationWorldClosureOrder.trans
        (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans
        smaller parentBelow⟩
  have formalBelow := ProjectionParameterOrigin.formalNode_below origin controls nominal.argument.node selected
    outer callerWorld .expressionReindex .assignedComparison selectedPaid
  have callerBelow := ProjectionHead.parameter_below head location controls callerWorld .expressionReindex .assignedComparison
  obtain ⟨smaller, sponsored⟩ := inheritedCall frontier (from_right (calls :=
      [originalCallWorld formalControls .expressionReindex nominal.argument.node selected,
       originalCallWorld controls .expressionReindex callerArgument callerWorld]) (by
    intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact formalBelow
    · cases List.mem_singleton.mp member
      exact callerBelow)) paid (by
    intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, by simp, formalBelow⟩
    · cases List.mem_singleton.mp member
      exact ⟨_, by simp, callerBelow⟩)
  have selectedData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := formalDisplay) formalControls selected frontier formalFrame :=
    ⟨formalData.generation, formalData.replayable, formalData.controlled, formalData.compatible,
      formalData.closed, Nat.le_refl _, Covered.refl _, formalData.hereditary⟩
  obtain ⟨rawReply, ⟨rawData⟩⟩ := bank.observation _ smaller base caps formalDisplay callerDisplay
    commonLeft commonRight formalControls controls rfl rfl selected callerWorld frontier rfl sponsored
    formalFrame selectedData callerFrame callerData nominal.argument.query.observation
    nominal.argument.query.resources nominal.controlled
  let query := rawReply.answer.reply.query.adaptRequest henv hscoped formed
    nominal.argument.query.bound nominal.argument.query.adapter
  let reply := rawReply.mapQuery query
  exact ⟨reply, ⟨⟨rawData.generation, rawData.replayable, rawData.controlled, rawData.compatible,
    rawData.query, rawData.covered, rawData.hereditary⟩⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
