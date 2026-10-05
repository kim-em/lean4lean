import Lean4Lean.Theory.Typing.AnchoredOriginalRichProjectionReindex
import Lean4Lean.Theory.Typing.AnchoredOriginalRichComputationalValue

/-! Paired computational projection F at the actual structural projection.
The source field certificate remains at its original formation child; the
right projection query uses the paired major and field answers. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

noncomputable def naturalProjectionHead
    {node : EndpointState sourceEnv U source (.proj name index value) assigned}
    (head : ProjectionHead node) : ProjectionHead (projectionNatural head) :=
  ⟨head.info, head.registered, head.levels, head.levelsWF, head.levelCount,
    head.parameters, head.parameterCount, head.indices, head.indexCount,
    head.sourceMajor, head.fieldType, head.selected, head.fieldLevel, head.fieldWF,
    head.field, head.major, head.closed, head.relevance, .done _⟩

theorem RichComputationalValue.projected_nativeDepth
    {node : EndpointState sourceEnv U source (.proj name index value) assigned}
    (head : ProjectionHead node)
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (nameEq : record.family.name = name) (member : (index, request) ∈ record.fields)
    (fieldCode : RichCert sourceEnv env U registry target head.field locals σ true support fieldFootprint)
    (fieldResources : fieldFootprint.Available available)
    (typed : request.input.HasType support)
    (alignment : DomainChain env U registry target request.input request.domain (head.fieldType.subst σ))
    (majorAnswer : RichComputationalValue sourceEnv env U registry target (.ref (.right head.major))
      locals σ τ available (Profile.singleton (n := n + 1) (.record record)))
    (fieldAnswer : RichCodeTransferResult env U registry target head.field head.field
      locals σ τ available true support) :
    ∃ answer : RichComputationalValue sourceEnv env U registry target (projectionNatural head)
      locals σ τ available request.input,
      (∀ current, answer.rightQuery.observation.nativeDepth current =
        max (majorAnswer.rightQuery.observation.nativeDepth current) (fieldAnswer.certificate.nativeDepth current)) ∧
      (∀ current, answer.certificate.nativeDepth current = fieldCode.nativeDepth current) := by
  obtain ⟨majorFootprint, majorQuery, majorResources, majorDepth⟩ := majorAnswer.rightQuery.recordObservation_nativeDepth henv
  have raw := (head.field.sound.defeq.mono sourceBelow).substDF henv substitutions.wf formed substitutions
  let rightAlignment : DomainChain env U registry target request.input request.domain (head.fieldType.subst τ) :=
    alignment.trans (.step (.single raw) typed fieldCode.formed fieldAnswer.related (.refl _))
  have projected := majorAnswer.related.projectRecord henv hscoped formed member
  have related : Related env U registry target ((VExpr.proj name index value).subst σ)
      ((VExpr.proj name index value).subst τ) (head.fieldType.subst σ) request.input support := by
    simpa only [nameEq, subst_proj] using
      alignment.related henv typed fieldAnswer.related.left_diagonal projected
  refine ⟨{
    support := support
    footprint := fieldFootprint
    certificate := fieldCode
    resources := fieldResources
    typed := typed
    related := related
    typeCode := fieldAnswer.related.left_diagonal
    rightQuery := {
      rank := n
      bound := Nat.le_refl _
      raw := request.input
      footprint := majorFootprint ++ fieldAnswer.footprint
      observation := .projection (naturalProjectionHead head) nameEq member majorQuery fieldAnswer.certificate typed rightAlignment
      adapter := ?_
      resources := fun i need hm => (List.mem_append.mp hm).elim
        (majorResources i need) (fieldAnswer.resources i need)
      live := related.live henv hscoped formed } }, ?_, fun _ => rfl⟩
  · simpa only [raiseProfile_self] using
      (show GeneralNormalProfileAdapter env U registry target request.input request.input from .refl _)
  · intro current
    simp only [RichObs.nativeDepth, majorDepth]

theorem RichComputationalValue.projected
    {node : EndpointState sourceEnv U source (.proj name index value) assigned}
    (head : ProjectionHead node)
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (nameEq : record.family.name = name) (member : (index, request) ∈ record.fields)
    (fieldCode : RichCert sourceEnv env U registry target head.field locals σ true support fieldFootprint)
    (fieldResources : fieldFootprint.Available available)
    (typed : request.input.HasType support)
    (alignment : DomainChain env U registry target request.input request.domain (head.fieldType.subst σ))
    (majorAnswer : RichComputationalValue sourceEnv env U registry target (.ref (.right head.major))
      locals σ τ available (Profile.singleton (n := n + 1) (.record record)))
    (fieldAnswer : RichCodeTransferResult env U registry target head.field head.field
      locals σ τ available true support) :
    Nonempty (RichComputationalValue sourceEnv env U registry target (projectionNatural head)
      locals σ τ available request.input) := by
  obtain ⟨answer, _, _⟩ := RichComputationalValue.projected_nativeDepth head henv hscoped sourceBelow
    formed substitutions nameEq member fieldCode fieldResources typed alignment majorAnswer fieldAnswer
  exact ⟨answer⟩

variable {header : EndpointRef headerEnv U [] headerExpression headerType}
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  {major : EndpointRef sourceEnv U source majorExpression majorType}

/-- Both fixed original children decrease at the actual frame environment.
The declaration reserve of the structural projection is retained in the
parent cost, rather than replaced by a caller-selected numeric bound. -/
theorem HeaderBinderFrame.projectionComputationalStep
    {context : ContextDerivation headerEnv U headerSource}
    {node : EndpointState headerEnv U headerSource (.proj name index value) assigned}
    (head : ProjectionHead node)
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (hf : headerEnv.Ordered) (sf : sourceEnv.Ordered) (initial : List Closure)
    (frame : HeaderBinderFrame header field major env registry target context locals σ τ available)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ headerSource)
    {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (nameEq : record.family.name = name) (member : (index, request) ∈ record.fields)
    (majorQuery : RichObs headerEnv env U registry target (.ref (.right head.major))
      locals σ (Profile.singleton (n := n + 1) (.record record)) majorFootprint)
    (fieldCode : RichCert headerEnv env U registry target head.field locals σ true support fieldFootprint)
    (typed : request.input.HasType support)
    (alignment : DomainChain env U registry target request.input request.domain (head.fieldType.subst σ))
    (resources : (majorFootprint ++ fieldFootprint).Available available)
    (majorF : HeaderComputationalInductionAt header field major env registry hf sf initial context
      (.ref (.right head.major))
      (Closure.close ((projectionNatural head).dependencyOrigin hf)
        (frame.dependencyEnvironment hf sf initial)).cost)
    (fieldF : HeaderCodeInductionAt header field major env registry hf sf initial context head.field
      (Closure.close ((projectionNatural head).dependencyOrigin hf)
        (frame.dependencyEnvironment hf sf initial)).cost) :
    Nonempty (RichComputationalValue headerEnv env U registry target (projectionNatural head)
      locals σ τ available request.input) := by
  have majorResources := fun i need hm => resources i need (List.mem_append_left _ hm)
  have fieldResources := fun i need hm => resources i need (List.mem_append_right _ hm)
  have majorBound : (Closure.close ((EndpointState.ref (.right head.major)).dependencyOrigin hf)
      (frame.dependencyEnvironment hf sf initial)).cost <
      (Closure.close ((projectionNatural head).dependencyOrigin hf)
        (frame.dependencyEnvironment hf sf initial)).cost := by
    apply original_child_same_environment
    apply Origin.rule_child
    simp [EndpointState.dependencyOrigin, EndpointRef.dependencyOrigin]
  have fieldBound : (Closure.close (head.field.dependencyOrigin hf)
      (frame.dependencyEnvironment hf sf initial)).cost <
      (Closure.close ((projectionNatural head).dependencyOrigin hf)
        (frame.dependencyEnvironment hf sf initial)).cost := by
    apply original_child_same_environment
    apply Origin.rule_child
    simp
  obtain ⟨majorAnswer⟩ := majorF target locals σ τ available frame majorBound closed formed substitutions
    majorQuery majorResources
  obtain ⟨fieldAnswer⟩ := fieldF target locals σ τ available frame fieldBound closed formed substitutions
    fieldCode fieldResources
  exact RichComputationalValue.projected head henv hscoped headerBelow formed substitutions nameEq member
    fieldCode fieldResources typed alignment majorAnswer fieldAnswer

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
