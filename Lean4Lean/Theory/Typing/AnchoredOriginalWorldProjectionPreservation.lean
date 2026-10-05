import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQuerySiteReady
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryContinuation
import Lean4Lean.Theory.Typing.AnchoredOriginalRichProjectionReindex

/-! Projection reconstruction from independently selected actual child frames.
Old child annotations are retained. Only the newly introduced projection sites
are constructed, at the exact merged paired frame. This local producer does
not manufacture the recursive R/C replies or their sponsor bounds. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut
open EquationWorldClosureOrder
open private projectionMajor_cost_lt from Lean4Lean.Theory.Typing.AnchoredOriginalRichProjectionReindex
open private field_cost_lt from Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

noncomputable def OriginalRichOccurrenceFrame.merge
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U occurrenceSource expression assigned}
    {location : Located root node}
    (first : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ firstAvailable
      ordered initialEnvironment)
    (second : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ secondAvailable
      ordered initialEnvironment) :
    OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ
      (firstAvailable.append secondAvailable) ordered initialEnvironment :=
  ⟨first.frame.merge second.frame, first.substitutions, by
    rw [OriginalRichFrame.merge_environmentCost]
    exact Nat.max_le.mpr ⟨first.environment_le, second.environment_le⟩⟩

noncomputable def OriginalRichOccurrenceFrame.mergeWorld
    {strata : EquationStratification env}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U occurrenceSource expression assigned}
    {location : Located root node}
    (controls : OriginalWorldControls strata sourceEnv)
    (first : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ firstAvailable
      controls.ordered initialEnvironment)
    (second : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ secondAvailable
      controls.ordered initialEnvironment)
    (firstWorld : WorldEnvironmentProvenance strata U (first.frame.dependencyEnvironment controls.ordered))
    (secondWorld : WorldEnvironmentProvenance strata U (second.frame.dependencyEnvironment controls.ordered)) :
    WorldEnvironmentProvenance strata U ((first.merge second).frame.dependencyEnvironment controls.ordered) :=
  firstWorld.append secondWorld

/-- The selected frame's environment is exactly the max of the two actual
child capacities; no call is replayed in an enlarged input frame. -/
theorem OriginalRichOccurrenceFrame.merge_cost
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U occurrenceSource expression assigned}
    {location : Located root node}
    (first : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ firstAvailable
      ordered initialEnvironment)
    (second : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ secondAvailable
      ordered initialEnvironment) :
    environmentCost ((first.merge second).frame.dependencyEnvironment ordered) =
      max (environmentCost (first.frame.dependencyEnvironment ordered))
        (environmentCost (second.frame.dependencyEnvironment ordered)) :=
  first.frame.merge_environmentCost ordered second.frame

theorem RichObs.projectionFromWorldReplies
    {strata : EquationStratification env}
    {left : EndpointState leftEnv U leftSource (.proj name index leftMajor) leftType}
    {right : EndpointState rightEnv U rightSource (.proj name index rightMajor) rightType}
    {root : EndpointRef rightEnv U rootSource rootExpression rootType}
    {location : Located root right}
    (leftHead : ProjectionHead left) (rightHead : ProjectionHead right)
    (controls : OriginalWorldControls strata rightEnv)
    (first : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ firstAvailable
      controls.ordered initialEnvironment)
    (second : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ secondAvailable
      controls.ordered initialEnvironment)
    (firstWorld : WorldEnvironmentProvenance strata U (first.frame.dependencyEnvironment controls.ordered))
    (secondWorld : WorldEnvironmentProvenance strata U (second.frame.dependencyEnvironment controls.ordered))
    (henv : env.Ordered) (below : rightEnv ≤ env)
    (firstAmbient : first.frame.Ambient) (secondAmbient : second.frame.Ambient)
    (firstClosed : firstAvailable.AtomClosed) (secondClosed : secondAvailable.AtomClosed)
    {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (nameEq : record.family.name = name) (member : (index, request) ∈ record.fields)
    (sourceField : RichCert leftEnv env U registry target leftHead.field leftLocals leftSubst true support sourceFootprint)
    (typed : request.input.HasType support)
    (alignment : DomainChain env U registry target request.input request.domain (leftHead.fieldType.subst leftSubst))
    (majorReply : RichGradedResult rightEnv env U registry target (.ref (.right rightHead.major)) locals σ firstAvailable
      (.singleton (n := n + 1) (.record record)))
    (majorAnnotation : WorldObsProvenance strata majorReply.observation)
    (fieldReply : RichProjectionAssignedReply leftHead rightHead env registry target locals leftSubst σ secondAvailable support)
    (fieldAnnotation : WorldCertProvenance strata fieldReply.code.certificate) :
    let chosen := first.merge second
    let environment := first.mergeWorld controls second firstWorld secondWorld
    let routed := chosen.routeWorld controls rightHead.route environment
    let majorSite := (chosen.projMajor rightHead).worldSite controls routed
    let fieldSite := (chosen.projField rightHead).worldSite controls routed
    ∃ (majorFootprint : Footprint)
      (majorQuery : RichObs rightEnv env U registry target (.ref (.right rightHead.major)) locals σ
        (.singleton (n := n + 1) (.record record)) majorFootprint),
      majorSite.Ready majorQuery ∧ fieldSite.Ready (.code fieldReply.code.certificate) ∧
      ∃ (footprint : Footprint)
        (observation : RichObs rightEnv env U registry target right locals σ request.input footprint)
        (annotation : WorldObsProvenance strata observation),
        footprint.Available (firstAvailable.append secondAvailable) ∧
        annotation.worlds = majorSite.worlds ++ fieldSite.worlds ++ majorAnnotation.worlds ++ fieldAnnotation.worlds ∧
        (∀ policy, observation.headDepth policy =
          max (majorReply.observation.headDepth policy) (fieldReply.code.certificate.headDepth policy)) := by
  dsimp only
  obtain ⟨majorFootprint, majorQuery, selectedAnnotation, majorResources, sameWorlds, sameDepth⟩ :=
    majorReply.recordObservation_worlds_depth henv majorAnnotation
  let chosen := first.merge second
  let environment := first.mergeWorld controls second firstWorld secondWorld
  let routed := chosen.routeWorld controls rightHead.route environment
  let majorSite := (chosen.projMajor rightHead).worldSite controls routed
  let fieldSite := (chosen.projField rightHead).worldSite controls routed
  let chain := alignment.trans (.step fieldReply.path typed sourceField.formed fieldReply.code.related (.refl _))
  let observation := RichObs.projection rightHead nameEq member majorQuery fieldReply.code.certificate typed chain
  let annotation := WorldObsProvenance.projection rightHead nameEq member selectedAnnotation fieldAnnotation
    majorSite fieldSite typed chain
  have resources : (majorFootprint ++ fieldReply.code.footprint).Available (firstAvailable.append secondAvailable) := by
    intro i need present
    rcases List.mem_append.mp present with present | present
    · exact List.mem_append_left _ (majorResources i need present)
    · exact List.mem_append_right _ (fieldReply.code.resources i need present)
  have closed : (firstAvailable.append secondAvailable).AtomClosed := by
    intro i need present atom member
    rcases List.mem_append.mp present with present | present
    · exact List.mem_append_left _ (firstClosed i need present atom member)
    · exact List.mem_append_right _ (secondClosed i need present atom member)
  have ready := chosen.projectionSites_ready controls environment rightHead majorQuery fieldReply.code.certificate below
    (firstAmbient.merge secondAmbient) closed resources
  refine ⟨majorFootprint, majorQuery, ready.1, ready.2, _, observation, annotation, resources, ?_, ?_⟩
  · change majorSite.worlds ++ fieldSite.worlds ++ selectedAnnotation.worlds ++ fieldAnnotation.worlds = _
    rw [sameWorlds]
  · intro policy
    simp only [observation, RichObs.headDepth]
    rw [sameDepth]

private theorem transportedWorlds
    {strata : EquationStratification env} {first second : List OriginalClosureMeasure.Closure}
    (equal : first = second) (environment : WorldEnvironmentProvenance strata U first) :
    (show WorldEnvironmentProvenance strata U second from equal ▸ environment).worlds = environment.worlds := by
  cases equal
  rfl

/-- Original route exposure preserves both the actual numeric environment
and the actual annotated worlds; equality of scalar costs is not used. -/
theorem OriginalRichOccurrenceFrame.projectionSite_worlds
    {strata : EquationStratification env}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U occurrenceSource (.proj name index major) assigned}
    {location : Located root node}
    (controls : OriginalWorldControls strata sourceEnv)
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      controls.ordered initialEnvironment)
    (environment : WorldEnvironmentProvenance strata U (occurrence.frame.dependencyEnvironment controls.ordered))
    (head : ProjectionHead node) :
    let routed := occurrence.routeWorld controls head.route environment
    ((occurrence.projMajor head).worldSite controls routed).worlds =
      [originalCallWorld controls .fundamental (.ref (.right head.major)) environment] ∧
    ((occurrence.projField head).worldSite controls routed).worlds =
      [originalCallWorld controls .fundamental head.field environment] := by
  dsimp only
  constructor <;>
    simp only [OriginalRichOccurrenceFrame.worldSite, WorldQuerySite.worlds,
      WorldClosureProvenance.worlds, OriginalRichOccurrenceFrame.projMajor,
      OriginalRichOccurrenceFrame.projField, OriginalRichOccurrenceFrame.routeWorld,
      transportedWorlds, originalCallWorld]
  all_goals rw [occurrence.route_worldEnvironment head.route]

/-- Fresh native metadata sites are funded by the actual destination F.
They do not require a comparison with the source sponsor. -/
theorem OriginalRichOccurrenceFrame.projectionSites_sponsored
    {strata : EquationStratification env}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U occurrenceSource (.proj name index major) assigned}
    {location : Located root node}
    (controls : OriginalWorldControls strata sourceEnv)
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      controls.ordered initialEnvironment)
    (environment : WorldEnvironmentProvenance strata U (occurrence.frame.dependencyEnvironment controls.ordered))
    (head : ProjectionHead node) (source : World strata.rules.length) :
    let routed := occurrence.routeWorld controls head.route environment
    Sponsored [source, originalCallWorld controls .fundamental node environment]
      (((occurrence.projMajor head).worldSite controls routed).worlds ++
        ((occurrence.projField head).worldSite controls routed).worlds) := by
  dsimp only
  rw [(occurrence.projectionSite_worlds controls environment head).1,
    (occurrence.projectionSite_worlds controls environment head).2]
  intro use member
  rcases List.mem_append.mp member with member | member
  · cases List.mem_singleton.mp member
    refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    exact original_child (richSchedule_strict (projectionMajor_cost_lt head controls.ordered _) _ _) _ _ _ _ _
  · cases List.mem_singleton.mp member
    refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    exact original_child (richSchedule_strict (field_cost_lt head controls.ordered _) _ _) _ _ _ _ _

/-- Actual output control preservation. Recursive child answers supply only
controls for their own observations; native metadata sponsorship and all
output masked bounds are derived at the same selected merged frame. -/
theorem RichObs.projectionFromControlledReplies
    {strata : EquationStratification env}
    {left : EndpointState leftEnv U leftSource (.proj name index leftMajor) leftType}
    {right : EndpointState rightEnv U rightSource (.proj name index rightMajor) rightType}
    {root : EndpointRef rightEnv U rootSource rootExpression rootType}
    {location : Located root right}
    (leftHead : ProjectionHead left) (rightHead : ProjectionHead right)
    (controls : OriginalWorldControls strata rightEnv)
    (first : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ firstAvailable
      controls.ordered initialEnvironment)
    (second : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ secondAvailable
      controls.ordered initialEnvironment)
    (firstWorld : WorldEnvironmentProvenance strata U (first.frame.dependencyEnvironment controls.ordered))
    (secondWorld : WorldEnvironmentProvenance strata U (second.frame.dependencyEnvironment controls.ordered))
    (henv : env.Ordered) (below : rightEnv ≤ env)
    (firstAmbient : first.frame.Ambient) (secondAmbient : second.frame.Ambient)
    (firstClosed : firstAvailable.AtomClosed) (secondClosed : secondAvailable.AtomClosed)
    {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (nameEq : record.family.name = name) (member : (index, request) ∈ record.fields)
    (sourceField : RichCert leftEnv env U registry target leftHead.field leftLocals leftSubst true support sourceFootprint)
    (typed : request.input.HasType support)
    (alignment : DomainChain env U registry target request.input request.domain (leftHead.fieldType.subst leftSubst))
    (majorReply : RichGradedResult rightEnv env U registry target (.ref (.right rightHead.major)) locals σ firstAvailable
      (.singleton (n := n + 1) (.record record)))
    (fieldReply : RichProjectionAssignedReply leftHead rightHead env registry target locals leftSubst σ secondAvailable support)
    (sourceSponsor : World strata.rules.length)
    (majorReady : ControlledStoredQuery controls
      [sourceSponsor, originalCallWorld controls .fundamental right (first.mergeWorld controls second firstWorld secondWorld)]
      (.observation majorReply.observation))
    (fieldReady : ControlledStoredQuery controls
      [sourceSponsor, originalCallWorld controls .fundamental right (first.mergeWorld controls second firstWorld secondWorld)]
      (.certificate fieldReply.code.certificate)) :
    let chosen := first.merge second
    let environment := first.mergeWorld controls second firstWorld secondWorld
    let routed := chosen.routeWorld controls rightHead.route environment
    let majorSite := (chosen.projMajor rightHead).worldSite controls routed
    let fieldSite := (chosen.projField rightHead).worldSite controls routed
    ∃ (majorFootprint : Footprint)
      (majorQuery : RichObs rightEnv env U registry target (.ref (.right rightHead.major)) locals σ
        (.singleton (n := n + 1) (.record record)) majorFootprint),
      majorSite.Ready majorQuery ∧ fieldSite.Ready (.code fieldReply.code.certificate) ∧
      ∃ (footprint : Footprint)
        (observation : RichObs rightEnv env U registry target right locals σ request.input footprint)
        (output : ControlledStoredQuery controls
          [sourceSponsor, originalCallWorld controls .fundamental right environment] (.observation observation)),
        footprint.Available (firstAvailable.append secondAvailable) ∧
        output.annotation.worlds = majorSite.worlds ++ fieldSite.worlds ++ majorReady.annotation.worlds ++ fieldReady.annotation.worlds ∧
        (∀ policy, observation.headDepth policy =
          max (majorReply.observation.headDepth policy) (fieldReply.code.certificate.headDepth policy)) := by
  dsimp only
  obtain ⟨majorFootprint, majorQuery, majorSiteReady, fieldSiteReady,
    footprint, observation, annotation, resources, worlds, depth⟩ :=
    RichObs.projectionFromWorldReplies leftHead rightHead controls first second firstWorld secondWorld
      henv below firstAmbient secondAmbient firstClosed secondClosed nameEq member sourceField typed alignment
      majorReply majorReady.annotation fieldReply fieldReady.annotation
  let environment := first.mergeWorld controls second firstWorld secondWorld
  let output : ControlledStoredQuery controls
      [sourceSponsor, originalCallWorld controls .fundamental right environment] (.observation observation) := {
    annotation := annotation
    within := by
      intro control active
      change observation.headDepth _ ≤ _
      rw [depth]
      exact Nat.max_le.mpr ⟨majorReady.within control active, fieldReady.within control active⟩
    sponsored := by
      change Sponsored _ annotation.worlds
      rw [worlds]
      have native := (first.merge second).projectionSites_sponsored controls environment rightHead sourceSponsor
      simpa only [List.append_assoc, environment, StoredOriginalQuery.Provenance.worlds] using native.merge (majorReady.sponsored.merge fieldReady.sponsored) }
  exact ⟨majorFootprint, majorQuery, majorSiteReady, fieldSiteReady,
    footprint, observation, output, resources, worlds, depth⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
