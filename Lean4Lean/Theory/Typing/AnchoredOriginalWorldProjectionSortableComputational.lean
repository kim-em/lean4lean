import Lean4Lean.Theory.Typing.AnchoredOriginalRichProjectionSortableComputational
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldComputationalPrefix
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls

/-! Execute the two proper F children of a sortable projection, then restore
its actual assigned prefix. This establishes the semantic F answer and the
assigned certificate controls. Right-query fuel is preserved separately; a
paired right-site provenance constructor is not assumed. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
open private fullRecordAdmission from Lean4Lean.Theory.Typing.AnchoredOriginalRichProjectionSortableComputational
open private projectionMajor_cost_lt from Lean4Lean.Theory.Typing.AnchoredOriginalRichProjectionReindex
open private field_cost_lt from Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls
open private singletonSponsoredBelow from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

/-- The input's actual child annotations are selected below. Neither child F
answer, field relation, nor assigned-prefix replay is supplied by a caller. -/
theorem projectionSortableWorldValue
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source (.proj name index value) assigned}
    (head : ProjectionHead node) (provenance : EndpointProvenance context node)
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (capacity : environmentCost (frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) captured.worlds baseline.worlds)
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental node baseline])
    (unary : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental node baseline]))
    (replay : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental node baseline]))
    {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (nameEq : record.family.name = name) (member : (index, request) ∈ record.fields)
    (majorQuery : RichObs sourceEnv env U registry target (.ref (.right head.major))
      locals σ (.singleton (n := n+1) (.record record)) majorFootprint)
    {atom : Atom n} {output : Atom m}
    (selected : atom ∈ request.input.atoms)
    (path : GeneralOutputPath env U registry target atom output)
    (sortable : (Profile.singleton output).HasType (.sort relevant))
    (fieldCode : RichCert sourceEnv env U registry target head.field locals σ true support fieldFootprint)
    (typed : (Profile.singleton output).HasType support)
    (resources : (majorFootprint ++ fieldFootprint).Available available)
    (majorAnnotation : WorldObsProvenance strata majorQuery)
    (fieldAnnotation : WorldCertProvenance strata fieldCode)
    (majorSite : WorldQuerySite (registry := registry) (target := target) strata
      (.ref (.right head.major)) locals σ)
    (fieldSite : WorldQuerySite (registry := registry) (target := target) strata head.field locals σ)
    (within : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => (RichObs.projectionSortable head nameEq member majorQuery selected path sortable
        fieldCode typed).headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (sponsored : Sponsored frontier (WorldObsProvenance.projectionSortable head nameEq member selected path
      sortable majorAnnotation fieldAnnotation majorSite fieldSite typed).worlds) :
    ∃ answer : RichComputationalValue sourceEnv env U registry target node locals σ τ available
        (Profile.singleton output),
      Nonempty (ControlledStoredQuery controls frontier (.certificate answer.certificate)) ∧
      EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
        (fun control => answer.rightQuery.observation.headDepth
          (stratifiedHeadPolicy (strata.headOrdinal registry) control)) := by
  let majorReady : ControlledStoredQuery controls frontier (.observation majorQuery) := {
    annotation := majorAnnotation
    within := by
      intro control active
      have bound := within control active
      simp only [RichObs.headDepth] at bound
      exact Nat.le_trans (Nat.le_max_left _ _) bound
    sponsored := fun world member => sponsored world
      (List.mem_append_left _ (List.mem_append_right _ member)) }
  let fieldReady : ControlledStoredQuery controls frontier (.certificate fieldCode) := {
    annotation := fieldAnnotation
    within := by
      intro control active
      have bound := within control active
      simp only [RichObs.headDepth] at bound
      exact Nat.le_trans (Nat.le_max_right _ _) bound
    sponsored := fun world member => sponsored world (List.mem_append_right _ member) }
  have majorLower : WorldBelow strata.rules.length
      (originalCallWorld controls .fundamental (.ref (.right head.major)) baseline)
      (originalCallWorld controls .fundamental node baseline) :=
    original_child (richSchedule_strict (projectionMajor_cost_lt head controls.ordered _) _ _) _ _ _ _ _
  have fieldLower : WorldBelow strata.rules.length
      (originalCallWorld controls .fundamental head.field baseline)
      (originalCallWorld controls .fundamental node baseline) :=
    original_child (richSchedule_strict (field_cost_lt head controls.ordered _) _ _) _ _ _ _ _
  have fund : ∀ child, WorldBelow strata.rules.length child
      (originalCallWorld controls .fundamental node baseline) →
      CallBelow strata.rules.length (frontier ++ [child])
        (frontier ++ [originalCallWorld controls .fundamental node baseline]) := by
    intro child lower
    have prepend : ∀ front : List (World strata.rules.length),
        CallBelow strata.rules.length (front ++ [child])
          (front ++ [originalCallWorld controls .fundamental node baseline]) := by
      intro front
      induction front with
      | nil => exact split_call (by intro world member; cases List.mem_singleton.mp member; exact lower)
      | cons world rest ih => exact ih.cons world
    exact prepend frontier
  let majorProvenance : EndpointProvenance context (.ref (.right head.major)) := {
    rootSource := provenance.rootSource, rootExpression := provenance.rootExpression, rootType := provenance.rootType
    root := provenance.root, initial := provenance.initial
    location := .projMajor (head.route.locate provenance.location)
    context_eq := by
      change context = (head.route.locate provenance.location).contextDerivation provenance.initial
      rw [PrefixRoute.locate_contextDerivation]
      exact provenance.context_eq }
  let fieldProvenance : EndpointProvenance context head.field := {
    rootSource := provenance.rootSource, rootExpression := provenance.rootExpression, rootType := provenance.rootType
    root := provenance.root, initial := provenance.initial
    location := .projField (head.route.locate provenance.location)
    context_eq := by
      change context = (head.route.locate provenance.location).contextDerivation provenance.initial
      rw [PrefixRoute.locate_contextDerivation]
      exact provenance.context_eq }
  have majorResources := fun i need hm => resources i need (List.mem_append_left _ hm)
  have fieldResources := fun i need hm => resources i need (List.mem_append_right _ hm)
  obtain ⟨majorAnswer, _, ⟨majorAnswerReady⟩⟩ := (unary _ (fund _ majorLower)).computational
    (.ref (.right head.major)) majorProvenance controls frame captured baseline frontier capacity covered rfl
    (singletonSponsoredBelow paid majorLower) data closed formed substitutions majorQuery majorResources majorReady
  obtain ⟨fieldValue, _, ⟨fieldValueReady⟩⟩ := (unary _ (fund _ fieldLower)).computational
    head.field fieldProvenance controls frame captured baseline frontier capacity covered rfl
    (singletonSponsoredBelow paid fieldLower) data closed formed substitutions (.code fieldCode) fieldResources {
      annotation := .code fieldAnnotation
      within := by
        simpa only [StoredOriginalQuery.headDepth, RichObs.headDepth] using fieldReady.within
      sponsored := fieldReady.sponsored }
  obtain ⟨nextFieldFootprint, nextField, nextFieldReady, nextFieldResources, _⟩ :=
    fieldValue.rightQuery.code_controlled henv controls fieldValueReady fieldCode.formed
  have fieldRelated := fieldValue.related.code_of_sortable henv hscoped formed fieldCode.formed
  obtain ⟨nextMajorFootprint, nextMajor, nextMajorAnnotation, nextMajorResources, sameWorlds, sameDepth⟩ :=
    majorAnswer.rightQuery.recordObservation_worlds_depth henv majorAnswerReady.annotation
  have admitted := fullRecordAdmission henv hscoped formed majorAnswer.related member
  have outputRelated := (admitted.sortableOutputRelated henv hscoped formed selected path sortable typed
    fieldRelated.left_diagonal).2
  have related : Related env U registry target ((VExpr.proj name index value).subst σ)
      ((VExpr.proj name index value).subst τ) (head.fieldType.subst σ) (Profile.singleton output) support := by
    simpa only [nameEq, subst_proj] using outputRelated
  let native : RichSupportedValue sourceEnv env U registry target (projectionNatural head)
      locals σ τ available (Profile.singleton output) := {
    support := support, footprint := fieldFootprint, certificate := fieldCode,
    resources := fieldResources, typed := typed, related := related,
    typeCode := fieldRelated.left_diagonal }
  let right : RichGradedResult sourceEnv env U registry target (projectionNatural head)
      locals τ available (Profile.singleton output) := {
    rank := m, bound := Nat.le_refl _, raw := .singleton output,
    footprint := nextMajorFootprint ++ nextFieldFootprint,
    observation := .projectionSortable (naturalProjectionHead head) nameEq member nextMajor
      selected path sortable nextField typed,
    adapter := by simpa only [raiseProfile_self] using
      (show GeneralNormalProfileAdapter env U registry target (.singleton output) (.singleton output) from .refl _),
    resources := fun i need hm => (List.mem_append.mp hm).elim
      (nextMajorResources i need) (nextFieldResources i need),
    live := related.live henv hscoped formed }
  obtain ⟨direct⟩ := head.route.direct (fun _ _ equal => by cases equal)
    (provenance.location.originalDirect.direct (fun _ _ equal => by cases equal))
  obtain ⟨restored, ⟨restoredReady⟩⟩ := direct.restoreSupportedWorld node controls frame captured baseline frontier
    capacity covered data closed formed substitutions henv hscoped paid unary replay provenance
    (Nat.le_refl _) native fieldReady
  refine ⟨{restored with rightQuery := right.restoreRoute head.route}, ⟨restoredReady⟩, ?_⟩
  intro control active
  simp only [RichGradedResult.restoreRoute, right, RichObs.headDepth]
  rw [sameDepth]
  exact Nat.max_le.mpr ⟨majorAnswerReady.within control active, nextFieldReady.within control active⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
