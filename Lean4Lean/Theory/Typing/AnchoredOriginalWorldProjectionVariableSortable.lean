import Lean4Lean.Theory.Typing.AnchoredOriginalWorldProjectionObservationDemandCompiler

/-! Rebuild a caller projection at its actual selected sortable demand. The
whole retained record request remains intact, while the real caller field
certificate supports only the finite requested output. -/
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
set_option maxHeartbeats 2200000

/-- The complete actual input query is compiled first. Its exact selected
record member, original request atom and output path then construct the new
observer, with proper-original opening sites and the original child sponsors. -/
theorem ControlledStoredQuery.projectionVariableSortableWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation callerEnv U callerSource}
    {callerNode : EndpointState callerEnv U callerSource (.proj name index (.bvar caller)) callerAssigned}
    (callerHead : ProjectionHead callerNode)
    (controls : OriginalWorldControls strata callerEnv)
    (frontier : List (World strata.rules.length))
    {query : RichObs callerEnv env U registry target callerNode locals σ profile footprint}
    (ready : ControlledStoredQuery controls frontier (.observation query))
    (provenance : EndpointProvenance context callerNode)
    (frame : OriginalRichFrame callerEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (substitutions : Ctx.SubstEq env U target σ τ callerSource)
    (resources : footprint.Available available)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (sourceBelow : callerEnv ≤ env) (sourceClosed : ∀ next ≤ env, P next)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental callerNode captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental callerNode captured]))
    (selected : atom ∈ profile.atoms)
    {m : Nat} {output : Atom m}
    (path : GeneralOutputPath env U registry target atom output)
    {support : Profile m}
    (fieldCode : RichCert callerEnv env U registry target callerHead.field
      locals σ true support fieldFootprint)
    (fieldResources : fieldFootprint.Available available)
    (fieldReady : ControlledStoredQuery controls frontier (.certificate fieldCode))
    (typed : (Profile.singleton output).HasType support)
    (sortable : (Profile.singleton output).HasType (.sort relevant)) :
    ∃ result : RichGradedResult callerEnv env U registry target callerNode locals σ available
        (Profile.singleton output),
      Nonempty (ControlledStoredQuery controls frontier (.observation result.observation)) ∧
      ∃ rank, ∃ request : DataRequest (Profile rank),
        RankedData.RequestAdmission env U (relations env U registry rank) target request
          (.proj name index (σ caller)) (.proj name index (τ caller)) ∧
        Admitted env U registry target
          (show Key m from ⟨request.domain,request.anchor,Profile.singleton output⟩)
          (.proj name index (σ caller)) (.proj name index (τ caller)) := by
  obtain ⟨rank,record,request,majorQuery,majorReady,value,certificateReady,valueReady,
      admitted,outputAdmitted,nameEq,member,requestAtom,selectedAtom,⟨outputPath⟩⟩ :=
    ControlledStoredQuery.projectionVariableDemandWorld callerHead controls frontier ready provenance frame captured data
      closed substitutions resources henv hscoped formed sourceBelow sourceClosed paid bank selected path
  obtain ⟨majorFootprint,majorObservation,majorAnnotation,majorResources,majorWorlds,majorDepth⟩ :=
    majorQuery.recordObservation_worlds_depth henv majorReady.annotation
  let majorSite : WorldQuerySite strata (.ref (.right callerHead.major)) locals σ := {
    context := context
    provenance := {
      rootSource := provenance.rootSource, rootExpression := provenance.rootExpression,
      rootType := provenance.rootType, root := provenance.root, initial := provenance.initial
      location := .projMajor (callerHead.route.locate provenance.location)
      context_eq := by
        change context = (callerHead.route.locate provenance.location).contextDerivation provenance.initial
        rw [PrefixRoute.locate_contextDerivation]
        exact provenance.context_eq }
    right := τ, available := available, frame := frame, annotation := ⟨controls,captured⟩ }
  let fieldSite : WorldQuerySite strata callerHead.field locals σ := {
    context := context
    provenance := {
      rootSource := provenance.rootSource, rootExpression := provenance.rootExpression,
      rootType := provenance.rootType, root := provenance.root, initial := provenance.initial
      location := .projField (callerHead.route.locate provenance.location)
      context_eq := by
        change context = (callerHead.route.locate provenance.location).contextDerivation provenance.initial
        rw [PrefixRoute.locate_contextDerivation]
        exact provenance.context_eq }
    right := τ, available := available, frame := frame, annotation := ⟨controls,captured⟩ }
  let observation := RichObs.projectionSortable callerHead nameEq member majorObservation
    selectedAtom outputPath sortable fieldCode typed
  let annotation := WorldObsProvenance.projectionSortable callerHead nameEq member
    selectedAtom outputPath sortable majorAnnotation fieldReady.annotation majorSite fieldSite typed
  have supplied : (majorFootprint ++ fieldFootprint).Available available := by
    intro i need present
    exact (List.mem_append.mp present).elim (majorResources i need) (fieldResources i need)
  have sitePaid : Sponsored frontier (majorSite.worlds ++ fieldSite.worlds) := by
    have majorLower : WorldBelow strata.rules.length
        (originalCallWorld controls .fundamental (.ref (.right callerHead.major)) captured)
        (originalCallWorld controls .fundamental callerNode captured) :=
      original_child (richSchedule_strict
        (projectionMajor_cost_lt callerHead controls.ordered _) _ _) _ _ _ _ _
    have fieldLower : WorldBelow strata.rules.length
        (originalCallWorld controls .fundamental callerHead.field captured)
        (originalCallWorld controls .fundamental callerNode captured) :=
      original_child (richSchedule_strict
        (field_cost_lt callerHead controls.ordered _) _ _) _ _ _ _ _
    intro world present
    obtain ⟨sponsor,member,lower⟩ := paid _ (List.mem_singleton_self _)
    change world ∈ [_] ++ [_] at present
    rcases List.mem_append.mp present with present | present
    · cases List.mem_singleton.mp present
      exact ⟨sponsor,member,EquationWorldClosureOrder.trans
        (r := @EquationControlMeasure.Less strata.rules.length)
        EquationControlMeasure.less_trans majorLower lower⟩
    · cases List.mem_singleton.mp present
      exact ⟨sponsor,member,EquationWorldClosureOrder.trans
        (r := @EquationControlMeasure.Less strata.rules.length)
        EquationControlMeasure.less_trans fieldLower lower⟩
  have worlds : annotation.worlds = majorSite.worlds ++ fieldSite.worlds ++
      majorReady.annotation.worlds ++ fieldReady.annotation.worlds := by
    change majorSite.worlds ++ fieldSite.worlds ++ majorAnnotation.worlds ++ _ = _
    rw [majorWorlds]
    rfl
  have depth : ∀ policy, observation.headDepth policy =
      max (majorQuery.observation.headDepth policy) (fieldCode.headDepth policy) := by
    intro policy
    simp only [observation,RichObs.headDepth,majorDepth]
  let queryReady : ControlledStoredQuery controls frontier (.observation observation) := {
    annotation := annotation
    within := by
      intro control active
      change observation.headDepth _ ≤ _
      rw [depth]
      exact Nat.max_le.mpr ⟨majorReady.within control active,fieldReady.within control active⟩
    sponsored := by
      change Sponsored frontier annotation.worlds
      rw [worlds]
      exact (sitePaid.merge majorReady.sponsored).merge fieldReady.sponsored }
  have live : Profile.Live env U registry target (Profile.singleton output) := by
    obtain ⟨_,_,_,_,_,_,_,pair⟩ := outputAdmitted
    exact Related.live henv hscoped formed pair
  let result : RichGradedResult callerEnv env U registry target callerNode locals σ available
      (Profile.singleton output) := {
    rank := m, bound := Nat.le_refl _, raw := .singleton output
    footprint := majorFootprint ++ fieldFootprint, observation := observation
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := supplied, live := live }
  exact ⟨result,⟨queryReady⟩,rank,request,admitted,outputAdmitted⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
