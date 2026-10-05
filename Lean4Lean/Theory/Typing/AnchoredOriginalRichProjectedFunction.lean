import Lean4Lean.Theory.Typing.AnchoredOriginalRichProjectionAmbient
import Lean4Lean.Theory.Typing.AnchoredApplication

/-! Interpret a retained converted projection at its exact ambient assigned
type. This closes the semantic type mismatch before a projected function is
applied. The ambient source certificate is retained, rather than replacing
it by an existential natural field type. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem AmbientProjectionCode.interpretProjection
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source (.proj name index displayedMajor) assigned}
    (head : ProjectionHead node)
    {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (nameEq : record.family.name = name) (member : (index, request) ∈ record.fields)
    (majorQuery : RichObs sourceEnv env U registry target (.ref (.right head.major))
      locals σ (.singleton (n := n + 1) (.record record)) majorFootprint)
    (majorCalls : ValueCalls env registry context majorQuery)
    (packet : AmbientProjectionCode sourceEnv env U registry target
      (.proj head.registered head.levelsWF head.levelCount head.parameterCount head.indexCount
        head.selected head.fieldWF head.field head.major head.closed head.relevance)
      node locals σ available support)
    (fieldCalls : CodeCalls env registry context packet.naturalCode)
    (typed : request.input.HasType support)
    (alignment : DomainChain env U registry target request.input request.domain (head.fieldType.subst σ))
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tails : SortableTailPairedFits env registry target context locals σ σ available)
    (majorResources : majorFootprint.Available available) :
    Related env U registry target ((VExpr.proj name index displayedMajor).subst σ)
      ((VExpr.proj name index displayedMajor).subst σ) (assigned.subst σ) request.input support := by
  obtain ⟨major⟩ := majorCalls.interpret henv hscoped closed formed substitutions tails majorResources
  have field := fieldCalls.interpret henv hscoped closed formed substitutions tails packet.naturalAvailable
  have projected := major.related.projectRecord henv hscoped formed member
  have natural := alignment.related henv typed field projected
  exact Related.convert henv typed packet.bridge (by simpa only [nameEq, subst] using natural)

/-- A projected function with a converted assigned Pi type can now be applied
at that exact type. Both source type certificates below are indexed by their
actual original formation occurrences. Constructing the result certificate
for arbitrary input queries remains the rich application-F obligation. -/
theorem AmbientProjectionCode.applyProjection
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source (.proj name index displayedMajor) (.forallE A B)}
    (head : ProjectionHead node)
    {record : RecordData (Profile (n + 1))} {request : DataRequest (Profile (n + 1))}
    {key : Key n} {output : Atom n}
    (nameEq : record.family.name = name) (member : (index, request) ∈ record.fields)
    (requested : request.input = Profile.fn key output)
    (majorQuery : RichObs sourceEnv env U registry target (.ref (.right head.major))
      locals σ (.singleton (n := n + 2) (.record record)) majorFootprint)
    (majorCalls : ValueCalls env registry context majorQuery)
    (packet : AmbientProjectionCode sourceEnv env U registry target
      (.proj head.registered head.levelsWF head.levelCount head.parameterCount head.indexCount
        head.selected head.fieldWF head.field head.major head.closed head.relevance)
      node locals σ available support)
    (fieldCalls : CodeCalls env registry context packet.naturalCode)
    (typed : request.input.HasType support)
    (alignment : DomainChain env U registry target request.input request.domain (head.fieldType.subst σ))
    (result : EndpointState sourceEnv U source (B.inst argumentExpression) (.sort resultLevel))
    (resultCode : RichCert sourceEnv env U registry target result locals σ true resultSupport resultFootprint)
    (resultCalls : CodeCalls env registry context resultCode)
    (resultTyped : (Profile.singleton output).HasType resultSupport)
    (admitted : Admitted env U registry target key (argumentExpression.subst σ) (argumentExpression.subst σ))
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tails : SortableTailPairedFits env registry target context locals σ σ available)
    (majorResources : majorFootprint.Available available)
    (resultResources : resultFootprint.Available available) :
    Related env U registry target ((VExpr.app (.proj name index displayedMajor) argumentExpression).subst σ)
      ((VExpr.app (.proj name index displayedMajor) argumentExpression).subst σ)
      ((B.inst argumentExpression).subst σ) (.singleton output) resultSupport := by
  have function := packet.interpretProjection henv hscoped head nameEq member majorQuery majorCalls
    fieldCalls typed alignment closed formed substitutions tails majorResources
  have resultRelated := resultCalls.interpret henv hscoped closed formed substitutions tails resultResources
  rw [requested] at function
  simp only [subst] at function
  have application := Related.apply henv hscoped formed resultTyped
    (by simpa only [subst_inst, inst_lift_cons] using resultRelated) function admitted
  simpa only [subst, subst_inst, inst_lift_cons] using application

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
