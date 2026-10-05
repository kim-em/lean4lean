import Lean4Lean.Theory.Typing.AnchoredOriginalTemplateComparison
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCodePreservation
import Lean4Lean.Theory.Typing.AnchoredFlatSortsGrades
import Lean4Lean.Theory.Typing.AnchoredHeadBeta
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyRequest
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldProjectionParameterFunding
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBoundedCallBank
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedBaseFreeze

/-! A parameter hole uses the actual paired family request and an actual
right query, transported from its retained original argument. The explicit
sort capability belongs to that SAME request's support; it yields a raw type
path even when the value demand is empty. No type-uniqueness theorem or
unconditional path supplied by the caller is used. -/
namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv AnchoredProfiles
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- The assigned-code seed is operationally necessary at empty demand: the
raw request equality is cast using the request's actual semantic support. -/
theorem RequestAdmission.codePath
    {request : DataRequest (Profile n)}
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (admitted : RequestAdmission env U (relations env U registry n) target request left right)
    (member : flag ∈ request.support.sortFlags) :
    TypeConversion env U target left right := by
  rcases admitted with ⟨_, raw, _, _, code, _, _⟩
  have selected := (TypeRelated.sortFlag henv code member).sortAt (m := 0) henv
  have actual := selected target .refl (.refl formed) flag
    (by simp only [Profile.rename_refl, Profile.sort]; exact List.mem_singleton_self _)
  simp only [VExpr.lift'_refl] at actual
  obtain ⟨level, path⟩ := SortRelated.path henv actual
  exact .single (path.cast raw)

end Lean4Lean.AnchoredSemantics.RankedData

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- Consume the concrete query returned by ordinary same-expression replay
from the retained right argument to the actual right field. The paired
admission supplies the cross-template semantics, while the returned query
supplies the certificate at the selected right frame. -/
theorem parameterHoleCode
    {strata : EquationStratification env}
    {left : EndpointState leftEnv U leftSource leftExpression (.sort leftLevel)}
    {right : EndpointState rightEnv U rightSource rightExpression (.sort rightLevel)}
    {request : DataRequest (Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (admitted : RankedData.RequestAdmission env U (relations env U registry n) target request
      (leftExpression.subst σ) (rightExpression.subst τ))
    (member : flag ∈ request.support.sortFlags)
    (sorted : request.input.HasType (.sort relevant))
    (query : RichGradedResult rightEnv env U registry target right rightLocals τ rightAvailable request.input)
    (controls : OriginalWorldControls strata controlSource)
    {frontier : List (VEnv.EquationWorldClosureOrder.World strata.rules.length)}
    (ready : ControlledStoredQuery controls frontier (.observation query.observation)) :
    ∃ result : TemplateCodeResult env U registry target left right rightLocals σ τ
        rightAvailable relevant request.input,
      ∃ controlled : ControlledStoredQuery controls frontier (.certificate result.certificate),
        controlled.annotation.worlds ⊆ ready.annotation.worlds ∧
        ∀ policy, result.certificate.headDepth policy ≤ query.observation.headDepth policy := by
  obtain ⟨footprint, certificate, annotation, resources, worlds, depth⟩ :=
    query.code_worlds_depth henv ready.annotation sorted
  let controlled : ControlledStoredQuery controls frontier (.certificate certificate) := {
    annotation := annotation
    within := fun control active => Nat.le_trans (depth _) (ready.within control active)
    sponsored := fun world member => ready.sponsored world (worlds member) }
  refine ⟨{
    footprint := footprint
    certificate := certificate
    resources := resources
    related := ?_
    path := admitted.codePath henv formed member
  }, controlled, worlds, depth⟩
  have related : Related env U registry target (leftExpression.subst σ)
      (rightExpression.subst τ) request.domain request.input request.support := admitted.2.2.2.2.2.2
  exact related.code_of_sortable henv hscoped formed sorted


/-- A genuine parameter-hole comparison. The paired descriptor supplies
cross-template semantics; the concrete nominal query is replayed at the
actual independent right field by a strictly smaller original R call. Its
selected generated frame, hereditary controls, and coverage remain attached
to the SAME returned certificate. No field-comparison callback is supplied. -/
theorem ProjectionHead.parameterHoleFromBank
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {outer : EndpointState base.sourceEnv U base.source (.proj name index major) assigned}
    (head : ProjectionHead outer)
    {left : EndpointState leftEnv U leftSource leftExpression (.sort leftLevel)}
    {request : DataRequest (Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (controls : OriginalWorldControls strata base.sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (other : World strata.rules.length) (frontier : List (World strata.rules.length))
    (paid : Sponsored frontier [other, originalCallWorld controls .assignedComparison outer baseline])
    (fieldProvenance : EndpointProvenance base.context head.field)
    (realization : OriginalCaptureRealization (.identity base.context) env registry target
      rightLocals base.left base.right rightAvailable)
    (selected : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := OriginalNestedDisplay.identity base head.field fieldProvenance)
      controls baseline frontier realization)
    (nominal : WorldRichFamilySourceRequest controls frontier (.right head.major)
      registry target rightLocals base.left rightAvailable head.fieldType request)
    (argumentProvenance : EndpointProvenance base.context nominal.argument.node)
    (admitted : RankedData.RequestAdmission env U (relations env U registry n) target request
      (leftExpression.subst σ) (head.fieldType.subst base.left))
    (member : flag ∈ request.support.sortFlags)
    (sorted : request.input.HasType (.sort relevant))
    (bank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [other, originalCallWorld controls .assignedComparison outer baseline])) :
    ∃ reply : AmbientBoundedGeneratedQueryReply base caps
        (OriginalNestedDisplay.identity base head.field fieldProvenance)
        base.left base.right request.input
        (environmentCost (realization.frame.dependencyEnvironment controls.ordered)),
      ∃ data : WorldGeneratedQueryReplyData (P := P) controls selected.generation.environment frontier reply,
      ∃ result : TemplateCodeResult env U registry target left head.field
        reply.answer.reply.locals σ base.left reply.answer.reply.available relevant request.input,
      ∃ output : ControlledStoredQuery controls frontier (.certificate result.certificate),
        output.annotation.worlds ⊆ data.query.annotation.worlds ∧
        ∀ policy, result.certificate.headDepth policy ≤
          reply.answer.reply.query.observation.headDepth policy := by
  let leftDisplay := OriginalNestedDisplay.identity base nominal.argument.node argumentProvenance
  let rightDisplay := OriginalNestedDisplay.identity base head.field fieldProvenance
  let actual := selected.generation.environment
  have leftData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := leftDisplay) controls actual frontier realization :=
    ⟨selected.generation, selected.replayable, selected.controlled, selected.compatible,
      selected.closed, Nat.le_refl _, Covered.refl _, selected.hereditary⟩
  have rightData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := rightDisplay) controls actual frontier realization :=
    ⟨selected.generation, selected.replayable, selected.controlled, selected.compatible,
      selected.closed, Nat.le_refl _, Covered.refl _, selected.hereditary⟩
  obtain ⟨decrease, sponsored⟩ := ProjectionHead.parameterFieldSelectedFunding head nominal.argument.location
    controls actual baseline selected.capacity selected.covered other frontier paid
  obtain ⟨rawReply, ⟨rawData⟩⟩ := bank.observation _ decrease base caps leftDisplay rightDisplay
    base.left base.right controls controls rfl rfl actual actual frontier rfl sponsored
    realization leftData realization rightData nominal.argument.query.observation
    nominal.argument.query.resources nominal.controlled
  let query := rawReply.answer.reply.query.adaptRequest henv hscoped formed
    nominal.argument.query.bound nominal.argument.query.adapter
  let reply := rawReply.mapQuery query
  let data : WorldGeneratedQueryReplyData (P := P) controls actual frontier reply := {
    generation := rawData.generation
    replayable := rawData.replayable
    controlled := rawData.controlled
    compatible := rawData.compatible
    query := rawData.query
    covered := rawData.covered
    hereditary := rawData.hereditary }
  obtain ⟨result, output, worlds, depth⟩ := parameterHoleCode (left := left) (right := head.field)
    henv hscoped formed admitted member sorted query controls data.query
  exact ⟨reply, data, result, output, worlds, depth⟩

/-- Select a genuine sortable subrequest of a mixed captured input. The
raw type path still uses the full request's retained assigned support. -/
theorem parameterHoleSelectedCode
    {strata : EquationStratification env}
    {left : EndpointState leftEnv U leftSource leftExpression (.sort leftLevel)}
    {right : EndpointState rightEnv U rightSource rightExpression (.sort rightLevel)}
    {request : DataRequest (Profile n)} {wanted : Profile m}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (admitted : RankedData.RequestAdmission env U (relations env U registry n) target request
      (leftExpression.subst σ) (rightExpression.subst τ))
    (member : flag ∈ request.support.sortFlags)
    (bounded : m ≤ n)
    (included : ∀ atom ∈ (raiseProfile n bounded wanted).atoms, atom ∈ request.input.atoms)
    (sorted : wanted.HasType (.sort relevant))
    (query : RichGradedResult rightEnv env U registry target right rightLocals τ rightAvailable wanted)
    (controls : OriginalWorldControls strata controlSource)
    {frontier : List (World strata.rules.length)}
    (ready : ControlledStoredQuery controls frontier (.observation query.observation)) :
    ∃ result : TemplateCodeResult env U registry target left right rightLocals σ τ
        rightAvailable relevant wanted,
      ∃ controlled : ControlledStoredQuery controls frontier (.certificate result.certificate),
        controlled.annotation.worlds ⊆ ready.annotation.worlds ∧
        ∀ policy, result.certificate.headDepth policy ≤ query.observation.headDepth policy := by
  obtain ⟨footprint, certificate, annotation, resources, worlds, depth⟩ :=
    query.code_worlds_depth henv ready.annotation sorted
  let controlled : ControlledStoredQuery controls frontier (.certificate certificate) := {
    annotation := annotation
    within := fun control active => Nat.le_trans (depth _) (ready.within control active)
    sponsored := fun world member => ready.sponsored world (worlds member) }
  have full : Related env U registry target (leftExpression.subst σ)
      (rightExpression.subst τ) request.domain request.input request.support := admitted.2.2.2.2.2.2
  have selected : Related env U registry target (leftExpression.subst σ)
      (rightExpression.subst τ) request.domain (raiseProfile n bounded wanted) request.support :=
    Related.of_singletons (fun atom present => full.singleton_of_mem (included atom present))
  have lowered := lowerProfile.related bounded henv formed selected
  exact ⟨{
    footprint := footprint
    certificate := certificate
    resources := resources
    related := lowered.code_of_sortable henv hscoped formed sorted
    path := admitted.codePath henv formed member }, controlled, worlds, depth⟩

/-- The actual original replay consumes the complete retained observer,
then a finite selection exposes only the requested code demand. Other old
value demands in the same capture need not be sortable. -/
theorem ProjectionHead.parameterHoleSelectedFromBank
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {outer : EndpointState base.sourceEnv U base.source (.proj name index major) assigned}
    (head : ProjectionHead outer)
    {left : EndpointState leftEnv U leftSource leftExpression (.sort leftLevel)}
    {request : DataRequest (Profile n)} {wanted : Profile m}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (controls : OriginalWorldControls strata base.sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (other : World strata.rules.length) (frontier : List (World strata.rules.length))
    (paid : Sponsored frontier [other, originalCallWorld controls .assignedComparison outer baseline])
    (fieldProvenance : EndpointProvenance base.context head.field)
    (realization : OriginalCaptureRealization (.identity base.context) env registry target
      rightLocals base.left base.right rightAvailable)
    (selected : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := OriginalNestedDisplay.identity base head.field fieldProvenance)
      controls baseline frontier realization)
    (nominal : WorldRichFamilySourceRequest controls frontier (.right head.major)
      registry target rightLocals base.left rightAvailable head.fieldType request)
    (argumentProvenance : EndpointProvenance base.context nominal.argument.node)
    (admitted : RankedData.RequestAdmission env U (relations env U registry n) target request
      (leftExpression.subst σ) (head.fieldType.subst base.left))
    (member : flag ∈ request.support.sortFlags)
    (bounded : m ≤ n)
    (included : ∀ atom ∈ (raiseProfile n bounded wanted).atoms, atom ∈ request.input.atoms)
    (sorted : wanted.HasType (.sort relevant))
    (bank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [other, originalCallWorld controls .assignedComparison outer baseline])) :
    ∃ reply : AmbientBoundedGeneratedQueryReply base caps
        (OriginalNestedDisplay.identity base head.field fieldProvenance)
        base.left base.right wanted
        (environmentCost (realization.frame.dependencyEnvironment controls.ordered)),
      ∃ data : WorldGeneratedQueryReplyData (P := P) controls selected.generation.environment frontier reply,
      ∃ result : TemplateCodeResult env U registry target left head.field
        reply.answer.reply.locals σ base.left reply.answer.reply.available relevant wanted,
      ∃ output : ControlledStoredQuery controls frontier (.certificate result.certificate),
        output.annotation.worlds ⊆ data.query.annotation.worlds ∧
        ∀ policy, result.certificate.headDepth policy ≤
          reply.answer.reply.query.observation.headDepth policy := by
  let leftDisplay := OriginalNestedDisplay.identity base nominal.argument.node argumentProvenance
  let rightDisplay := OriginalNestedDisplay.identity base head.field fieldProvenance
  let actual := selected.generation.environment
  have leftData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := leftDisplay) controls actual frontier realization :=
    ⟨selected.generation, selected.replayable, selected.controlled, selected.compatible,
      selected.closed, Nat.le_refl _, Covered.refl _, selected.hereditary⟩
  have rightData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := rightDisplay) controls actual frontier realization :=
    ⟨selected.generation, selected.replayable, selected.controlled, selected.compatible,
      selected.closed, Nat.le_refl _, Covered.refl _, selected.hereditary⟩
  obtain ⟨decrease, sponsored⟩ := ProjectionHead.parameterFieldSelectedFunding head nominal.argument.location
    controls actual baseline selected.capacity selected.covered other frontier paid
  obtain ⟨rawReply, ⟨rawData⟩⟩ := bank.observation _ decrease base caps leftDisplay rightDisplay
    base.left base.right controls controls rfl rfl actual actual frontier rfl sponsored
    realization leftData realization rightData nominal.argument.query.observation
    nominal.argument.query.resources nominal.controlled
  let full := rawReply.answer.reply.query.adaptRequest henv hscoped formed
    nominal.argument.query.bound nominal.argument.query.adapter
  have selection : GeneralNormalProfileAdapter env U registry target request.input
      (raiseProfile n bounded wanted) :=
    GeneralProfileAdapter.select (by
      intro atom present
      obtain ⟨original, member, rfl⟩ := List.mem_map.mp present
      exact List.mem_map.mpr ⟨original, included original member, rfl⟩)
  let query := full.adaptRequest henv hscoped formed bounded selection
  let reply := rawReply.mapQuery query
  let data : WorldGeneratedQueryReplyData (P := P) controls actual frontier reply := {
    generation := rawData.generation
    replayable := rawData.replayable
    controlled := rawData.controlled
    compatible := rawData.compatible
    query := rawData.query
    covered := rawData.covered
    hereditary := rawData.hereditary }
  obtain ⟨result, output, worlds, depth⟩ := parameterHoleSelectedCode (left := left) (right := head.field)
    henv hscoped formed admitted member bounded included sorted query controls data.query
  exact ⟨reply, data, result, output, worlds, depth⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
