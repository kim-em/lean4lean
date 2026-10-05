import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFormalFamilyRequestReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilySourceRequests
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyParameterReplay

/-! Formal parameter requests return to the actual caller's fixed base.
Each lower R answer is frozen by its genuine identity cap derivation, so
the two independently selected replies produce requests on one original
caller frame without identifying their generated frames. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
open private from_right from Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls
open private inheritedCall from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecordMajorBridge
open private sourceProvenance from Lean4Lean.Theory.Typing.AnchoredOriginalWorldFormalFamilyRequestReplay
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

section
variable
  {strata : EquationStratification env} {P : VEnv → Prop}
  (base : OriginalCaptureBase env U registry target)
  {outer : EndpointState base.sourceEnv U base.source (.proj name field major) assigned}
  (head : ProjectionHead outer)
  (origin : VEnv.ProjectionParameterOrigin base.sourceEnv name info)
  {levels : List VLevel} {C D : VExpr}
  {signature : ConstantTelescope (origin.family.type.instL levels)}
  {domains : signature.domains = [C,D]}
  (destination : FormalFamilyDestination (U := U) origin signature domains)
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
  (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
  (bank : WorldBoundedCallBank env U registry strata P
    (frontier ++ [other, originalCallWorld controls .assignedComparison outer callerWorld]))

include callerData formalData inherited paid henv hscoped formed bank

theorem FormalFamilyDestination.replayParameterAtBaseWorld
    (firstParameter : Bool)
    (callerArgument : EndpointState base.sourceEnv U base.source (if firstParameter then a else p) argumentType)
    (location : Located (.right head.major) callerArgument)
    (nominal : WorldRichFamilySourceRequest (controls.atHeader origin.constructorOrigin) frontier
      (.left destination.original) registry target formalLocals (((Subst.id.cons a).cons p).comp base.left)
      formalAvailable (.bvar (if firstParameter then 1 else 0)) (request : DataRequest (Profile n))) :
    Nonempty (WorldRichFamilySourceRequest controls frontier (.right head.major)
      registry target base.locals base.left base.available (if firstParameter then a else p) request) := by
  let formalControls := controls.atHeader origin.constructorOrigin
  let selected := formalData.generation.environment
  let callerDisplay := OriginalNestedDisplay.identity base callerArgument (sourceProvenance location base.context)
  let sourceDisplay : OriginalNestedDisplay U base.source (if firstParameter then a else p)
      (nominal.argument.assigned.subst ((Subst.id.cons a).cons p)) := {
    sourceEnv := origin.types, source := [D,C]
    sourceExpression := .bvar (if firstParameter then 1 else 0)
    sourceType := nominal.argument.assigned
    context := destination.context, node := nominal.argument.node
    provenance := sourceProvenance nominal.argument.location destination.context
    raw := (Subst.id.cons a).cons p, graph := formalGraph
    expression_eq := by cases firstParameter <;> rfl
    type_eq := rfl }
  have selectedPaid : Sponsored [originalCallWorld controls .assignedComparison outer callerWorld] selected.worlds := by
    intro child member
    obtain ⟨original, present, equal | smaller⟩ := formalData.covered child member
    · cases equal
      exact inherited _ present
    · obtain ⟨parent, parentMember, parentBelow⟩ := inherited original present
      exact ⟨parent, parentMember, EquationWorldClosureOrder.trans
        (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans smaller parentBelow⟩
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
  have selectedData : WorldCallFrameData (P := P) (base := base) (caps := base.initialCaps)
      (display := sourceDisplay) formalControls selected frontier formalFrame :=
    ⟨formalData.generation, formalData.replayable, formalData.controlled, formalData.compatible,
      formalData.closed, Nat.le_refl _, Covered.refl _, formalData.hereditary⟩
  have destinationData : WorldCallFrameData (P := P) (base := base) (caps := base.initialCaps)
      (display := callerDisplay) controls callerWorld frontier base.identityRealization :=
    ⟨callerData.generation, callerData.replayable, callerData.controlled, callerData.compatible,
      callerData.closed, callerData.capacity, callerData.covered, callerData.hereditary⟩
  obtain ⟨rawReply, ⟨rawData⟩⟩ := bank.observation _ smaller base base.initialCaps sourceDisplay callerDisplay
    base.left base.right formalControls controls rfl rfl selected callerWorld frontier rfl sponsored
    formalFrame selectedData base.identityRealization destinationData nominal.argument.query.observation
    nominal.argument.query.resources nominal.controlled
  let query := rawReply.answer.reply.query.adaptRequest henv hscoped formed
    nominal.argument.query.bound nominal.argument.query.adapter
  let reply := rawReply.mapQuery query
  obtain ⟨frozenReady⟩ := reply.answer.freezeBase_controlled rawData.query
  refine ⟨⟨⟨argumentType, callerArgument, location, reply.answer.freezeBase⟩, frozenReady, ?_⟩⟩
  have anchor := nominal.anchor
  cases firstParameter <;> exact anchor

include callerData formalData inherited paid henv hscoped formed bank

/-- Both actual computed formal requests are transferred to the literal
caller operands and retained on the SAME caller base. Their original key,
support, anchor, and incoming descriptor are unchanged. -/
theorem FormalFamilyDestination.callerRequestsWorld
    (firstArgument : EndpointState base.sourceEnv U base.source a firstType)
    (firstLocation : Located (.right head.major) firstArgument)
    (secondArgument : EndpointState base.sourceEnv U base.source p secondType)
    (secondLocation : Located (.right head.major) secondArgument)
    (property : WorldFamilyRequestProperty (controls.atHeader origin.constructorOrigin) frontier
      (.left destination.original) registry target formalLocals (((Subst.id.cons a).cons p).comp base.left)
      formalAvailable name levels [.bvar 1, .bvar 0] (family : FamilyData (Profile n))) :
    WorldFamilyRequestProperty controls frontier (.right head.major) registry target
      base.locals base.left base.available name levels [a,p] family := by
  rcases family with ⟨familyNameField, familyLevelsField, familyRelevant, requestsList⟩
  obtain ⟨familyName, familyLevels, requests⟩ := property
  refine ⟨familyName, familyLevels, ?_⟩
  cases requests with
  | cons first rest =>
    cases rest with
    | cons second rest =>
      cases rest
      obtain ⟨first⟩ := first
      obtain ⟨second⟩ := second
      exact .cons (FormalFamilyDestination.replayParameterAtBaseWorld base head origin destination formalGraph
        controls callerWorld formalBaseline frontier other callerData formalFrame formalData inherited paid
        henv hscoped formed bank true firstArgument firstLocation first)
        (.cons (FormalFamilyDestination.replayParameterAtBaseWorld base head origin destination formalGraph
          controls callerWorld formalBaseline frontier other callerData formalFrame formalData inherited paid
          henv hscoped formed bank false secondArgument secondLocation second) .nil)

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
