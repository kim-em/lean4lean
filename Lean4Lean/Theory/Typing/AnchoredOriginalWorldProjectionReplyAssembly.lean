import Lean4Lean.Theory.Typing.AnchoredOriginalWorldProjectionPreservation
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecipeArgumentTransport
import Lean4Lean.Theory.Typing.AnchoredRecordProjection

/-! Rebuild a projection from its actual selected child frames. The two
positive generations, including their finite base ancestries, are merged.
Only the new projection's top opening labels are constructed; nested query
annotations are retained unchanged and keep their original sponsors. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
open private projectionMajor_cost_lt from
  Lean4Lean.Theory.Typing.AnchoredOriginalRichProjectionReindex
open private field_cost_lt from
  Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

noncomputable def ProjectionHead.worldReplyDisplay
    {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    (_head : ProjectionHead node)
    (context : ContextDerivation sourceEnv U source)
    (provenance : EndpointProvenance context node)
    (graph : OriginalCaptureMap (common := common) context raw) :
    OriginalNestedDisplay U common ((VExpr.proj name index major).subst raw) (assigned.subst raw) :=
  ⟨sourceEnv, source, .proj name index major, assigned, context, node, provenance,
    raw, graph, rfl, rfl⟩

private def projectionMajorProvenance
    {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    (head : ProjectionHead node)
    (provenance : EndpointProvenance context node) :
    EndpointProvenance context (.ref (.right head.major)) where
  rootSource := provenance.rootSource
  rootExpression := provenance.rootExpression
  rootType := provenance.rootType
  root := provenance.root
  initial := provenance.initial
  location := .projMajor (head.route.locate provenance.location)
  context_eq := by
    change context = (head.route.locate provenance.location).contextDerivation provenance.initial
    rw [PrefixRoute.locate_contextDerivation]
    exact provenance.context_eq

private def projectionFieldProvenance
    {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    (head : ProjectionHead node)
    (provenance : EndpointProvenance context node) :
    EndpointProvenance context head.field where
  rootSource := provenance.rootSource
  rootExpression := provenance.rootExpression
  rootType := provenance.rootType
  root := provenance.root
  initial := provenance.initial
  location := .projField (head.route.locate provenance.location)
  context_eq := by
    change context = (head.route.locate provenance.location).contextDerivation provenance.initial
    rw [PrefixRoute.locate_contextDerivation]
    exact provenance.context_eq

/-- The two child replies may select different resource tables. Their actual
world frame data supplies both capacity and coverage at the fixed destination
baseline. No history is recovered from an old query-owned opening label. -/
theorem RichObs.projectionFromSelectedWorldReplies
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {left : EndpointState leftEnv U leftSource (.proj name index leftMajor) leftType}
    {right : EndpointState rightEnv U rightSource (.proj name index rightMajor) rightType}
    (leftHead : ProjectionHead left) (rightHead : ProjectionHead right)
    (context : ContextDerivation rightEnv U rightSource)
    (provenance : EndpointProvenance context right)
    (graph : OriginalCaptureMap (common := common) context raw)
    (controls : OriginalWorldControls strata rightEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (paid : Sponsored frontier [originalCallWorld controls .fundamental right baseline])
    (first : OriginalCaptureRealization graph env registry target
      firstLocals commonLeft commonRight firstAvailable)
    (second : OriginalCaptureRealization graph env registry target
      secondLocals commonLeft commonRight secondAvailable)
    (firstData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := ProjectionHead.worldReplyDisplay rightHead context provenance graph) controls baseline frontier first)
    (secondData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := ProjectionHead.worldReplyDisplay rightHead context provenance graph) controls baseline frontier second)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (nameEq : record.family.name = name) (member : (index, request) ∈ record.fields)
    (sourceField : RichCert leftEnv env U registry target leftHead.field leftLocals leftSubst
      true support sourceFootprint)
    (typed : request.input.HasType support)
    (alignment : DomainChain env U registry target request.input request.domain
      (leftHead.fieldType.subst leftSubst))
    (majorReply : RichGradedResult rightEnv env U registry target (.ref (.right rightHead.major))
      firstLocals (raw.comp commonLeft) firstAvailable (.singleton (n := n+1) (.record record)))
    (majorReady : ControlledStoredQuery controls frontier (.observation majorReply.observation))
    (majorValue : RichSupportedValue rightEnv env U registry target (.ref (.right rightHead.major))
      firstLocals (raw.comp commonLeft) (raw.comp commonRight) firstAvailable
      (.singleton (n := n+1) (.record record)))
    (fieldReply : RichProjectionAssignedReply leftHead rightHead env registry target
      secondLocals leftSubst (raw.comp commonLeft) secondAvailable support)
    (fieldReady : ControlledStoredQuery controls frontier (.certificate fieldReply.code.certificate)) :
    ∃ reply : AmbientBoundedGeneratedQueryReply base caps
        (ProjectionHead.worldReplyDisplay rightHead context provenance graph) commonLeft commonRight request.input
        (environmentCost baselineEnvironment),
      ∃ data : WorldGeneratedQueryReplyData (P := P) controls baseline frontier reply,
        reply.answer.reply.available = firstAvailable.append secondAvailable ∧
        data.generation.worlds = firstData.generation.worlds ++ secondData.generation.worlds ∧
        data.query.annotation.worlds =
          [originalCallWorld controls .fundamental (.ref (.right rightHead.major)) data.generation.environment] ++
          [originalCallWorld controls .fundamental rightHead.field data.generation.environment] ++
          majorReady.annotation.worlds ++ fieldReady.annotation.worlds ∧
        ∀ policy, reply.answer.reply.query.observation.headDepth policy =
          max (majorReply.observation.headDepth policy) (fieldReply.code.certificate.headDepth policy) := by
  have localsEq : firstLocals = secondLocals :=
    firstData.generation.erase.capped.generated.locals_eq.trans
      secondData.generation.erase.capped.generated.locals_eq.symm
  cases localsEq
  let merged : OriginalCaptureRealization graph env registry target firstLocals
      commonLeft commonRight (firstAvailable.append secondAvailable) :=
    ⟨first.frame.merge second.frame, first.substitutions⟩
  let mergedData := firstData.merge secondData
  obtain ⟨majorFootprint, majorQuery, majorAnnotation, majorResources, majorWorlds, majorDepth⟩ :=
    majorReply.recordObservation_worlds_depth henv majorReady.annotation
  let majorSite : WorldQuerySite strata (.ref (.right rightHead.major)) firstLocals (raw.comp commonLeft) := {
    context := context
    provenance := projectionMajorProvenance rightHead provenance
    right := raw.comp commonRight
    available := firstAvailable.append secondAvailable
    frame := merged.frame
    annotation := ⟨controls, mergedData.generation.environment⟩ }
  let fieldSite : WorldQuerySite strata rightHead.field firstLocals (raw.comp commonLeft) := {
    context := context
    provenance := projectionFieldProvenance rightHead provenance
    right := raw.comp commonRight
    available := firstAvailable.append secondAvailable
    frame := merged.frame
    annotation := ⟨controls, mergedData.generation.environment⟩ }
  let chain := alignment.trans
    (.step fieldReply.path typed sourceField.formed fieldReply.code.related (.refl _))
  let observation := RichObs.projection rightHead nameEq member majorQuery
    fieldReply.code.certificate typed chain
  let annotation := WorldObsProvenance.projection rightHead nameEq member majorAnnotation
    fieldReady.annotation majorSite fieldSite typed chain
  have resources : (majorFootprint ++ fieldReply.code.footprint).Available
      (firstAvailable.append secondAvailable) := by
    intro i need present
    rcases List.mem_append.mp present with present | present
    · exact List.mem_append_left _ (majorResources i need present)
    · exact List.mem_append_right _ (fieldReply.code.resources i need present)
  have sitePaid : Sponsored frontier (majorSite.worlds ++ fieldSite.worlds) := by
    have outerBound := originalCallWorld_boundedNode controls .fundamental right
      mergedData.generation.environment baseline mergedData.capacity mergedData.covered
    have majorLower : WorldBelow strata.rules.length
        (originalCallWorld controls .fundamental (.ref (.right rightHead.major)) mergedData.generation.environment)
        (originalCallWorld controls .fundamental right baseline) := by
      apply BoundedNode.child (r := @EquationControlMeasure.Less strata.rules.length)
        EquationControlMeasure.less_trans outerBound
      exact original_child (richSchedule_strict
        (projectionMajor_cost_lt rightHead controls.ordered _) _ _) _ _ _ _ _
    have fieldLower : WorldBelow strata.rules.length
        (originalCallWorld controls .fundamental rightHead.field mergedData.generation.environment)
        (originalCallWorld controls .fundamental right baseline) := by
      apply BoundedNode.child (r := @EquationControlMeasure.Less strata.rules.length)
        EquationControlMeasure.less_trans outerBound
      exact original_child (richSchedule_strict
        (field_cost_lt rightHead controls.ordered _) _ _) _ _ _ _ _
    intro world present
    obtain ⟨sponsor, member, lower⟩ := paid _ (List.mem_singleton_self _)
    change world ∈ [_] ++ [_] at present
    rcases List.mem_append.mp present with present | present
    · cases List.mem_singleton.mp present
      exact ⟨sponsor, member, EquationWorldClosureOrder.trans
        (r := @EquationControlMeasure.Less strata.rules.length)
        EquationControlMeasure.less_trans majorLower lower⟩
    · cases List.mem_singleton.mp present
      exact ⟨sponsor, member, EquationWorldClosureOrder.trans
        (r := @EquationControlMeasure.Less strata.rules.length)
        EquationControlMeasure.less_trans fieldLower lower⟩
  have worlds : annotation.worlds = majorSite.worlds ++ fieldSite.worlds ++
      majorReady.annotation.worlds ++ fieldReady.annotation.worlds := by
    change majorSite.worlds ++ fieldSite.worlds ++ majorAnnotation.worlds ++ _ = _
    rw [majorWorlds]
    rfl
  have depth : ∀ policy, observation.headDepth policy =
      max (majorReply.observation.headDepth policy) (fieldReply.code.certificate.headDepth policy) := by
    intro policy
    simp only [observation, RichObs.headDepth]
    rw [majorDepth]
  let queryReady : ControlledStoredQuery controls frontier (.observation observation) := {
    annotation := annotation
    within := by
      intro control active
      change observation.headDepth _ ≤ _
      rw [depth]
      exact Nat.max_le.mpr ⟨majorReady.within control active, fieldReady.within control active⟩
    sponsored := by
      change Sponsored frontier annotation.worlds
      rw [worlds]
      exact (sitePaid.merge majorReady.sponsored).merge fieldReady.sponsored }
  let query : RichGradedResult rightEnv env U registry target right firstLocals
      (raw.comp commonLeft) (firstAvailable.append secondAvailable) request.input := {
    rank := n
    bound := Nat.le_refl _
    raw := request.input
    footprint := majorFootprint ++ fieldReply.code.footprint
    observation := observation
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := resources
    live := (majorValue.related.projectRecord henv hscoped formed member).live henv hscoped formed }
  let reply : AmbientBoundedGeneratedQueryReply base caps
      (ProjectionHead.worldReplyDisplay rightHead context provenance graph) commonLeft commonRight request.input
      (environmentCost baselineEnvironment) := {
    answer := {
      reply := ⟨firstLocals, firstAvailable.append secondAvailable, merged,
        mergedData.generation.erase.capped.generated, query, mergedData.closed⟩
      capped := mergedData.generation.erase.capped }
    bounded := fun ordered => by
      cases Subsingleton.elim ordered controls.ordered
      exact mergedData.capacity
    generation := mergedData.generation.erase.ambientGenerated }
  let data : WorldGeneratedQueryReplyData (P := P) controls baseline frontier reply := {
    generation := mergedData.generation
    replayable := mergedData.replayable
    controlled := mergedData.controlled
    compatible := mergedData.compatible
    query := queryReady
    covered := mergedData.covered
    hereditary := mergedData.hereditary }
  refine ⟨reply, data, rfl, WorldGenerated.merge_worlds, ?_, depth⟩
  exact worlds

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
