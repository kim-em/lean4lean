import Lean4Lean.Theory.Typing.AnchoredOriginalTemplateComparison
import Lean4Lean.Theory.Typing.AnchoredOriginalRichProjectionComputational
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls

/-! Productive native projection comparison. Both semantic recursive inputs
belong to actual proper original children: the displayed major and the
field formation. No assigned comparison at the projection is assumed.

To instantiate these local child calls in a sparse template interpreter,
its field step must still construct the actual field template correspondence
from the retained projection metadata. Smaller original cost alone does not
supply that correspondence. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
open private recordShape_raise recordShape_normal recordAdapter_rigid from
  Lean4Lean.Theory.Typing.AnchoredOriginalRichRecordExtraction
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

@[simp] theorem RichObs.headDepth_lowerRaised (current : Name → Nat → Nat)
    {n N : Nat} {profile : Profile n} {bound : n ≤ N}
    (source : RichObs sourceEnv env U registry Γ node locals σ (raiseProfile N bound profile) footprint) :
    source.lowerRaised.headDepth current = source.headDepth current := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n
      simp only [RichObs.lowerRaised, dif_pos]
      exact RichObs.headDepth_mpr current rfl rfl (raiseProfile_self ..) rfl
        (congrArg (fun p => RichObs sourceEnv env U registry Γ node locals σ p footprint)
          (raiseProfile_self profile).symm) source
    · have previous : n ≤ N := by omega
      simp only [RichObs.lowerRaised, dif_neg equal]
      let changed := (congrArg (fun p => RichObs sourceEnv env U registry Γ node locals σ p footprint)
        (raiseProfile_step previous profile)).mp source
      change (RichObs.unpad changed).lowerRaised.headDepth current = _
      refine (ih (source := .unpad changed)).trans ?_
      simp only [RichObs.headDepth]
      exact RichObs.headDepth_mp current rfl rfl (raiseProfile_step previous profile) rfl _ source

/-- A generalized computational answer at a record demand yields an exact
source record observer. No inverse code support or stronger R answer is used. -/
theorem RichGradedResult.recordObservation_headDepth
    (henv : env.Ordered)
    (result : RichGradedResult sourceEnv env U registry Γ node locals σ available
      (Profile.singleton (n := n + 1) (.record (record : RecordData (Profile n))))) :
    ∃ footprint, ∃ observation : RichObs sourceEnv env U registry Γ node locals σ
      (Profile.singleton (n := n + 1) (.record record)) footprint, footprint.Available available ∧
      ∀ current, observation.headDepth current = result.observation.headDepth current := by
  have adapter := result.adapter
  rw [raiseProfile_singleton] at adapter
  have shape := recordShape_raise record result.bound
  have normalized := recordShape_normal shape
  change GeneralProfileAdapter env U registry Γ _ (.singleton (AdapterNormal.atom _)) at adapter
  rw [normalized] at adapter
  obtain ⟨normal, member, ⟨entry⟩⟩ := adapter.origin (List.mem_singleton_self _)
  obtain ⟨original, originalMember, equal⟩ := List.mem_map.mp member
  subst normal
  have same := recordAdapter_rigid entry shape
  let selected := RichObs.view (.select result.observation originalMember) (AdapterNormal.view henv original)
  have outputEq : Profile.singleton (AdapterNormal.atom original) =
      raiseProfile result.rank result.bound (Profile.singleton (n := n + 1) (.record record)) := by
    simp only [raiseProfile_singleton, same]
  let observed : RichObs sourceEnv env U registry Γ node locals σ
      (raiseProfile result.rank result.bound (Profile.singleton (n := n + 1) (.record record))) result.footprint :=
    (congrArg (fun profile => RichObs sourceEnv env U registry Γ node locals σ profile result.footprint) outputEq).mp selected
  refine ⟨result.footprint, observed.lowerRaised, result.resources, ?_⟩
  intro current
  rw [RichObs.headDepth_lowerRaised]
  exact (RichObs.headDepth_mp current rfl rfl outputEq rfl _ selected).trans
    (by simp only [selected, RichObs.headDepth])



/-- Raw projection comparison is independent of observational demand. The
left original field formation and original major equality provide exactly
the declaration guard and frozen field type used by the raw rule. -/
theorem ProjectionHead.templateRaw
    {left : EndpointState leftEnv U leftSource (.proj name index leftValue) leftType}
    (head : ProjectionHead left)
    (henv : env.Ordered) (below : leftEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ leftSource)
    (majorRaw : env.IsDefEq U target (leftValue.subst σ) rightValue
      ((mkApps (.const name head.levels) (head.parameters ++ head.indices)).subst σ)) :
    env.IsDefEq U target ((VExpr.proj name index leftValue).subst σ)
      (.proj name index rightValue) (head.fieldType.subst σ) := by
  have fieldTyped := (head.field.sound.defeq.mono below).substDF henv
    substitutions.wf formed substitutions
  have major := (head.major.forget.defeq.mono below).substDF henv
    substitutions.wf formed substitutions
  have selected := VProjectionInfo.fieldType_subst_some
    (typeName := name) (levels := head.levels) (params := head.parameters)
    (index := index) (major := head.sourceMajor) (result := head.fieldType)
    (substitution := σ) head.info head.closed head.selected
  have other := major.trans majorRaw
  simp only [subst_mkApps, List.map_append, subst] at major other
  exact .projDF (info := head.info)
    (params := head.parameters.map (VExpr.subst · σ))
    (indexArgs := head.indices.map (VExpr.subst · σ))
    (below.projections head.registered) head.levelsWF head.levelCount
    (by simpa using head.parameterCount) (by simpa using head.indexCount)
    selected (by simpa only [subst_sort] using fieldTyped)
    major other head.closed head.relevance

/-- Rebuild the actual right native projection from the two concrete child
answers. The requested support is unchanged, and both output depth bounds
refer to the SAME returned witnesses. The raw path remains meaningful when
`request.input` is empty. -/
theorem TemplateComparisonResult.projection
    {left : EndpointState leftEnv U leftSource (.proj name index leftValue) leftType}
    {right : EndpointState rightEnv U rightSource (.proj name index rightValue) rightType}
    (leftHead : ProjectionHead left) (rightHead : ProjectionHead right)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : leftEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ leftSource)
    {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (nameEq : record.family.name = name) (member : (index, request) ∈ record.fields)
    (fieldCode : RichCert leftEnv env U registry target leftHead.field leftLocals σ
      true support fieldFootprint)
    (fieldResources : fieldFootprint.Available leftAvailable)
    (typed : request.input.HasType support)
    (alignment : DomainChain env U registry target request.input request.domain
      (leftHead.fieldType.subst σ))
    (majorAnswer : TemplateComparisonResult env U registry target
      (.ref (.right leftHead.major)) (.ref (.right rightHead.major)) leftLocals rightLocals
      σ τ leftAvailable rightAvailable (Profile.singleton (n := n + 1) (.record record)))
    (fieldAnswer : TemplateCodeResult env U registry target leftHead.field rightHead.field
      rightLocals σ τ rightAvailable true support) :
    ∃ answer : TemplateComparisonResult env U registry target
      (projectionNatural leftHead) (projectionNatural rightHead) leftLocals rightLocals
      σ τ leftAvailable rightAvailable request.input,
      (∀ policy, answer.rightQuery.observation.headDepth policy =
        max (majorAnswer.rightQuery.observation.headDepth policy)
          (fieldAnswer.certificate.headDepth policy)) ∧
      (∀ policy, answer.source.certificate.headDepth policy = fieldCode.headDepth policy) ∧
      TypeConversion env U target (leftHead.fieldType.subst σ) (rightHead.fieldType.subst τ) := by
  obtain ⟨majorFootprint, majorQuery, majorResources, majorDepth⟩ :=
    majorAnswer.rightQuery.recordObservation_headDepth henv
  let rightAlignment : DomainChain env U registry target request.input request.domain
      (rightHead.fieldType.subst τ) :=
    alignment.trans (.step fieldAnswer.path typed fieldCode.formed fieldAnswer.related (.refl _))
  have projected := majorAnswer.related.projectRecord henv hscoped formed member
  have related : Related env U registry target ((VExpr.proj name index leftValue).subst σ)
      ((VExpr.proj name index rightValue).subst τ) (leftHead.fieldType.subst σ)
      request.input support := by
    simpa only [nameEq, subst_proj] using
      alignment.related henv typed fieldAnswer.related.left_diagonal projected
  have raw := ProjectionHead.templateRaw leftHead henv below formed substitutions majorAnswer.raw
  refine ⟨{
    source := {
      support := support
      footprint := fieldFootprint
      certificate := fieldCode
      resources := fieldResources
      typed := typed
      related := related.left_diagonal
      typeCode := fieldAnswer.related.left_diagonal }
    related := related
    raw := raw
    rightQuery := {
      rank := n
      bound := Nat.le_refl _
      raw := request.input
      footprint := majorFootprint ++ fieldAnswer.footprint
      observation := .projection (naturalProjectionHead rightHead) nameEq member majorQuery
        fieldAnswer.certificate typed rightAlignment
      adapter := ?_
      resources := fun i need hm => (List.mem_append.mp hm).elim
        (majorResources i need) (fieldAnswer.resources i need)
      live := related.live henv hscoped formed } }, ?_, fun _ => rfl, fieldAnswer.path⟩
  · simpa only [raiseProfile_self] using
      (show GeneralNormalProfileAdapter env U registry target request.input request.input from .refl _)
  · intro policy
    simp only [RichObs.headDepth, majorDepth]


open EquationWorldClosureOrder
open private major_below field_cost_lt from_both from
  Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls

/-- Both productive comparisons replace their own actual projection world
by a proper original child. There is no sum-of-two-costs assumption and no
comparison at the current projection among these obligations. -/
theorem projectionTemplateChildrenFunding
    {left : EndpointState leftEnv U leftSource (.proj name index leftValue) leftType}
    {right : EndpointState rightEnv U rightSource (.proj name index rightValue) rightType}
    (leftHead : ProjectionHead left) (rightHead : ProjectionHead right)
    (leftControls : OriginalWorldControls strata leftEnv)
    (rightControls : OriginalWorldControls strata rightEnv)
    (leftCaptured : WorldEnvironmentProvenance strata U leftEnvironment)
    (rightCaptured : WorldEnvironmentProvenance strata U rightEnvironment) :
    let parent := [originalCallWorld leftControls .assignedComparison left leftCaptured,
      originalCallWorld rightControls .assignedComparison right rightCaptured]
    CallBelow strata.rules.length
      [originalCallWorld leftControls .expressionReindex (.ref (.right leftHead.major)) leftCaptured,
       originalCallWorld rightControls .expressionReindex (.ref (.right rightHead.major)) rightCaptured] parent ∧
    CallBelow strata.rules.length
      [originalCallWorld leftControls .expressionReindex leftHead.field leftCaptured,
       originalCallWorld rightControls .expressionReindex rightHead.field rightCaptured] parent := by
  dsimp only
  constructor
  · exact from_both (major_below leftHead leftControls leftCaptured _ _)
      (major_below rightHead rightControls rightCaptured _ _)
  · apply from_both
    · exact original_child (richSchedule_strict
        (field_cost_lt leftHead leftControls.ordered leftEnvironment) _ _) _ _ _ _ _
    · exact original_child (richSchedule_strict
        (field_cost_lt rightHead rightControls.ordered rightEnvironment) _ _) _ _ _ _ _

/-- Invoke the productive local interpreter only at the actual major and
field children, then rebuild the projection. The callbacks are the two
recursive template clauses, not an assigned-C answer for this projection.
Their eligibility as template comparisons requires the caller's computed
field/major correspondence; the supplied world proofs only discharge the
independent original-cost part of that eligibility. -/
theorem projectionTemplateStep
    {left : EndpointState leftEnv U leftSource (.proj name index leftValue) leftType}
    {right : EndpointState rightEnv U rightSource (.proj name index rightValue) rightType}
    (leftHead : ProjectionHead left) (rightHead : ProjectionHead right)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : leftEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ leftSource)
    (leftControls : OriginalWorldControls strata leftEnv)
    (rightControls : OriginalWorldControls strata rightEnv)
    {leftContext : ContextDerivation leftEnv U leftSource}
    {rightContext : ContextDerivation rightEnv U rightSource}
    (leftFrame : OriginalRichFrame leftEnv env U registry target leftContext leftLocals σ σ leftAvailable)
    (rightFrame : OriginalRichFrame rightEnv env U registry target rightContext rightLocals τ τ rightAvailable)
    (leftCaptured : WorldEnvironmentProvenance strata U (leftFrame.dependencyEnvironment leftControls.ordered))
    (rightCaptured : WorldEnvironmentProvenance strata U (rightFrame.dependencyEnvironment rightControls.ordered))
    {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (nameEq : record.family.name = name) (member : (index, request) ∈ record.fields)
    (majorQuery : RichObs leftEnv env U registry target (.ref (.right leftHead.major))
      leftLocals σ (Profile.singleton (n := n + 1) (.record record)) majorFootprint)
    (fieldCode : RichCert leftEnv env U registry target leftHead.field leftLocals σ
      true support fieldFootprint)
    (resources : (majorFootprint ++ fieldFootprint).Available leftAvailable)
    (typed : request.input.HasType support)
    (alignment : DomainChain env U registry target request.input request.domain
      (leftHead.fieldType.subst σ))
    (majorCompare : ∀ {footprint},
      RichObs leftEnv env U registry target (.ref (.right leftHead.major)) leftLocals σ
        (Profile.singleton (n := n + 1) (.record record)) footprint →
      footprint.Available leftAvailable →
      CallBelow strata.rules.length
        [originalCallWorld leftControls .expressionReindex (.ref (.right leftHead.major)) leftCaptured,
         originalCallWorld rightControls .expressionReindex (.ref (.right rightHead.major)) rightCaptured]
        [originalCallWorld leftControls .assignedComparison left leftCaptured,
         originalCallWorld rightControls .assignedComparison right rightCaptured] →
      Nonempty (TemplateComparisonResult env U registry target
        (.ref (.right leftHead.major)) (.ref (.right rightHead.major)) leftLocals rightLocals
        σ τ leftAvailable rightAvailable (Profile.singleton (n := n + 1) (.record record))))
    (fieldCompare : ∀ {footprint},
      RichCert leftEnv env U registry target leftHead.field leftLocals σ true support footprint →
      footprint.Available leftAvailable →
      CallBelow strata.rules.length
        [originalCallWorld leftControls .expressionReindex leftHead.field leftCaptured,
         originalCallWorld rightControls .expressionReindex rightHead.field rightCaptured]
        [originalCallWorld leftControls .assignedComparison left leftCaptured,
         originalCallWorld rightControls .assignedComparison right rightCaptured] →
      Nonempty (TemplateCodeResult env U registry target leftHead.field rightHead.field
        rightLocals σ τ rightAvailable true support)) :
    Nonempty (TemplateComparisonResult env U registry target
      (projectionNatural leftHead) (projectionNatural rightHead) leftLocals rightLocals
      σ τ leftAvailable rightAvailable request.input) ∧
    TypeConversion env U target (leftHead.fieldType.subst σ) (rightHead.fieldType.subst τ) := by
  have funding := projectionTemplateChildrenFunding leftHead rightHead leftControls rightControls
    leftCaptured rightCaptured
  have majorResources := fun i need hm => resources i need (List.mem_append_left _ hm)
  have fieldResources := fun i need hm => resources i need (List.mem_append_right _ hm)
  obtain ⟨majorAnswer⟩ := majorCompare majorQuery majorResources funding.1
  obtain ⟨fieldAnswer⟩ := fieldCompare fieldCode fieldResources funding.2
  obtain ⟨answer, _, _, path⟩ := TemplateComparisonResult.projection leftHead rightHead
    henv hscoped below formed substitutions nameEq member fieldCode fieldResources typed alignment
    majorAnswer fieldAnswer
  exact ⟨⟨answer⟩, path⟩


/-- The genuinely empty observation case makes no record request. It uses
only the unconditional raw result of the proper major comparison. In
particular no field certificate, record support, or current assigned-C
answer is fabricated to obtain a raw projection equality. -/
theorem TemplateComparisonResult.projectionEmpty
    {left : EndpointState leftEnv U leftSource (.proj name index leftValue) leftType}
    {right : EndpointState rightEnv U rightSource (.proj name index rightValue) rightType}
    (leftHead : ProjectionHead left) (rightHead : ProjectionHead right)
    (henv : env.Ordered) (below : leftEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ leftSource)
    (majorAnswer : TemplateComparisonResult env U registry target
      (.ref (.right leftHead.major)) (.ref (.right rightHead.major)) leftLocals rightLocals
      σ τ leftAvailable rightAvailable (.empty : Profile n)) :
    ∃ answer : TemplateComparisonResult env U registry target
      (projectionNatural leftHead) (projectionNatural rightHead) leftLocals rightLocals
      σ τ leftAvailable rightAvailable (.empty : Profile n),
      answer.rightQuery.footprint = [] ∧
      (∀ policy, answer.rightQuery.observation.headDepth policy = 0) ∧
      (∀ policy, answer.source.certificate.headDepth policy = 0) := by
  refine ⟨{
    source := .empty
    related := Related.of_singletons (fun _ member => nomatch member)
    raw := ProjectionHead.templateRaw leftHead henv below formed substitutions majorAnswer.raw
    rightQuery := .empty }, rfl, ?_, ?_⟩ <;>
    intro policy <;> simp [RichGradedResult.empty, RichSupportedValue.empty,
      RichObs.headDepth, RichCert.headDepth, SortableObs.headDepth, SortableCert.headDepth,
      Obs.headDepth]

/-- Empty queries recurse with the concrete empty query at the actual major
child. The endpoint-world decrease is computed from the same two originals
as the nonempty step, without requiring a native record-query origin. -/
theorem projectionTemplateEmptyStep
    {left : EndpointState leftEnv U leftSource (.proj name index leftValue) leftType}
    {right : EndpointState rightEnv U rightSource (.proj name index rightValue) rightType}
    (leftHead : ProjectionHead left) (rightHead : ProjectionHead right)
    (henv : env.Ordered) (below : leftEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ leftSource)
    (leftControls : OriginalWorldControls strata leftEnv)
    (rightControls : OriginalWorldControls strata rightEnv)
    {leftContext : ContextDerivation leftEnv U leftSource}
    {rightContext : ContextDerivation rightEnv U rightSource}
    (leftFrame : OriginalRichFrame leftEnv env U registry target leftContext leftLocals σ σ leftAvailable)
    (rightFrame : OriginalRichFrame rightEnv env U registry target rightContext rightLocals τ τ rightAvailable)
    (leftCaptured : WorldEnvironmentProvenance strata U (leftFrame.dependencyEnvironment leftControls.ordered))
    (rightCaptured : WorldEnvironmentProvenance strata U (rightFrame.dependencyEnvironment rightControls.ordered))
    (majorCompare : ∀ {footprint},
      RichObs leftEnv env U registry target (.ref (.right leftHead.major)) leftLocals σ
        (.empty : Profile n) footprint →
      footprint.Available leftAvailable →
      CallBelow strata.rules.length
        [originalCallWorld leftControls .expressionReindex (.ref (.right leftHead.major)) leftCaptured,
         originalCallWorld rightControls .expressionReindex (.ref (.right rightHead.major)) rightCaptured]
        [originalCallWorld leftControls .assignedComparison left leftCaptured,
         originalCallWorld rightControls .assignedComparison right rightCaptured] →
      Nonempty (TemplateComparisonResult env U registry target
        (.ref (.right leftHead.major)) (.ref (.right rightHead.major)) leftLocals rightLocals
        σ τ leftAvailable rightAvailable (.empty : Profile n))) :
    ∃ answer : TemplateComparisonResult env U registry target
      (projectionNatural leftHead) (projectionNatural rightHead) leftLocals rightLocals
      σ τ leftAvailable rightAvailable (.empty : Profile n),
      answer.rightQuery.footprint = [] ∧
      (∀ policy, answer.rightQuery.observation.headDepth policy = 0) ∧
      (∀ policy, answer.source.certificate.headDepth policy = 0) := by
  have funding := projectionTemplateChildrenFunding leftHead rightHead leftControls rightControls
    leftCaptured rightCaptured
  obtain ⟨majorAnswer⟩ := majorCompare (.legacy (.legacy .empty)) (fun _ _ h => nomatch h) funding.1
  exact TemplateComparisonResult.projectionEmpty leftHead rightHead henv below formed substitutions
    majorAnswer


/-- Compare the hidden majors by the original outer major equalities and
an actual assigned-type conversion at the proper displayed-major pair.
This path uses no frozen record, so it also serves an empty prior-hole
query. The input conversion is at the majors' assigned family types, not
at either projection's field type. -/
theorem ProjectionHead.templateSourceMajorRaw
    {left : EndpointState leftEnv U leftSource (.proj name index leftValue) leftType}
    {right : EndpointState rightEnv U rightSource (.proj name index rightValue) rightType}
    (leftHead : ProjectionHead left) (rightHead : ProjectionHead right)
    (henv : env.Ordered) (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (leftSubstitutions : Ctx.SubstEq env U target σ σ leftSource)
    (rightSubstitutions : Ctx.SubstEq env U target τ τ rightSource)
    (displayed : leftValue.subst σ = rightValue.subst τ)
    (familyPath : TypeConversion env U target
      ((mkApps (.const name leftHead.levels) (leftHead.parameters ++ leftHead.indices)).subst σ)
      ((mkApps (.const name rightHead.levels) (rightHead.parameters ++ rightHead.indices)).subst τ)) :
    env.IsDefEq U target (leftHead.sourceMajor.subst σ) (rightHead.sourceMajor.subst τ)
      ((mkApps (.const name leftHead.levels) (leftHead.parameters ++ leftHead.indices)).subst σ) := by
  have leftRaw := (leftHead.major.forget.defeq.mono leftBelow).substDF henv
    leftSubstitutions.wf formed leftSubstitutions
  have rightRaw := (rightHead.major.forget.defeq.mono rightBelow).substDF henv
    rightSubstitutions.wf formed rightSubstitutions
  have back := familyPath.symm.cast rightRaw.symm
  rw [← displayed] at back
  exact leftRaw.trans back

/-- The raw hidden-major bridge obtains its family conversion by querying
only the actual proper major C pair, with the concrete empty formation
certificate. It does not supply or request the current projection C.
Ordinary C eligibility (equal original source displays) belongs to
`majorC`; the target expression equality below is used only to compose the
two already checked raw equalities. -/
theorem projectionTemplateSourceMajorStep
    {left : EndpointState leftEnv U leftSource (.proj name index leftValue) leftType}
    {right : EndpointState rightEnv U rightSource (.proj name index rightValue) rightType}
    (leftHead : ProjectionHead left) (rightHead : ProjectionHead right)
    (henv : env.Ordered) (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (leftSubstitutions : Ctx.SubstEq env U target σ σ leftSource)
    (rightSubstitutions : Ctx.SubstEq env U target τ τ rightSource)
    (displayed : leftValue.subst σ = rightValue.subst τ)
    (leftControls : OriginalWorldControls strata leftEnv)
    (rightControls : OriginalWorldControls strata rightEnv)
    {leftContext : ContextDerivation leftEnv U leftSource}
    {rightContext : ContextDerivation rightEnv U rightSource}
    (leftFrame : OriginalRichFrame leftEnv env U registry target leftContext leftLocals σ σ leftAvailable)
    (rightFrame : OriginalRichFrame rightEnv env U registry target rightContext rightLocals τ τ rightAvailable)
    (leftCaptured : WorldEnvironmentProvenance strata U (leftFrame.dependencyEnvironment leftControls.ordered))
    (rightCaptured : WorldEnvironmentProvenance strata U (rightFrame.dependencyEnvironment rightControls.ordered))
    (majorC : ∀ {footprint},
      RichCert leftEnv env U registry target (EndpointState.ref (.right leftHead.major)).typeFormation.node
        leftLocals σ true (.empty : Profile 0) footprint →
      footprint.Available leftAvailable →
      CallBelow strata.rules.length
        [originalCallWorld leftControls .assignedComparison (.ref (.right leftHead.major)) leftCaptured,
         originalCallWorld rightControls .assignedComparison (.ref (.right rightHead.major)) rightCaptured]
        [originalCallWorld leftControls .assignedComparison left leftCaptured,
         originalCallWorld rightControls .assignedComparison right rightCaptured] →
      Nonempty (TemplateCodeResult env U registry target
        (EndpointState.ref (.right leftHead.major)).typeFormation.node
        (EndpointState.ref (.right rightHead.major)).typeFormation.node
        rightLocals σ τ rightAvailable true (.empty : Profile 0))) :
    env.IsDefEq U target (leftHead.sourceMajor.subst σ) (rightHead.sourceMajor.subst τ)
      ((mkApps (.const name leftHead.levels) (leftHead.parameters ++ leftHead.indices)).subst σ) := by
  have funding := from_both (major_below leftHead leftControls leftCaptured
      .assignedComparison .assignedComparison)
    (major_below rightHead rightControls rightCaptured .assignedComparison .assignedComparison)
  obtain ⟨answer⟩ := majorC (.legacy (.seed .empty (Profile.HasType.empty (Profile.WF.sort true))))
    (fun _ _ h => nomatch h) funding
  exact ProjectionHead.templateSourceMajorRaw leftHead rightHead henv leftBelow rightBelow formed
    leftSubstitutions rightSubstitutions displayed answer.path

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
