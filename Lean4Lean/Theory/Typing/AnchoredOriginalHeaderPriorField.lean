import Lean4Lean.Theory.Typing.AnchoredOriginalHeterogeneousTail
import Lean4Lean.Theory.Typing.AnchoredOriginalDependentProjectionInterpretation

/-! A dependent header field whose declared type is a previous captured
field. Both original source occurrences remain explicit: the projected
value owns its recursive field certificate, and the declaration variable
receives a new certificate at its actual original formation occurrence.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- A previous captured field supplies the code query for a later declared
variable domain. The certificate is built at the actual header occurrence;
its semantics comes from the exact stored finite need, not a coherence
callback or a newly synthesized projection typing premise. -/
theorem HeaderValueAlignment.priorField
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (tail : HeaderRichTail header field major env registry target context locals left right available)
    (domain : EndpointRef headerEnv U headerSource (.bvar index) (.sort level))
    (owner : HeaderOwner field major)
    (value : RichBinderValue sourceEnv env U registry target owner.node
      ownerLocals ownerLeft ownerRight ownerAvailable (input : Profile n))
    (needed : Need.mk n value.support ∈ available index)
    (lookup : Lookup headerSource index previousType)
    (same : owner.assigned.subst ownerLeft = left index) :
    Nonempty (HeaderValueAlignment owner domain env registry target ownerLocals locals
      ownerLeft ownerRight left ownerAvailable available input) := by
  obtain ⟨entry⟩ := tail.lookup henv formed needed lookup
  have code := (entry.related.code_of_sortable henv hscoped formed value.certificate.formed).left_diagonal
  refine ⟨{ value := value, aligned := {
    footprint := [(index, Need.mk n value.support)]
    certificate := .legacy (.seed (.var locals left index value.support) value.certificate.formed)
    resources := ?_, related := ?_ }, path := ?_ }⟩
  · intro slot need member
    cases List.mem_singleton.mp member
    exact needed
  · simpa only [same, subst] using code
  · rw [same]
    exact .refl

/-- Select the actual exposed projection occurrence beneath its retained
original route. The source environment and context are inherited from the
physical location, rather than reconstructed from raw equality. -/
def HeaderOwner.projected
    {source current : List VExpr} {assigned : VExpr}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {node : EndpointState sourceEnv U current (.proj name index displayedMajor) assigned}
    (start : Located field node) (head : ProjectionHead node) : HeaderOwner field major :=
  .inl ⟨_, _, _, .proj head.registered head.levelsWF head.levelCount head.parameterCount
    head.indexCount head.selected head.fieldWF head.field head.major head.closed head.relevance,
    head.route.locate start⟩

/-- Interpret the actual projected value using its recursively produced
rich field certificate. Only genuine original leaf calls are used; the
field certificate itself need not belong to the old hereditary core. -/
theorem HeaderOwner.projectedValue
    {source current : List VExpr} {assigned : VExpr}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {node : EndpointState sourceEnv U current (.proj name index displayedMajor) assigned}
    (start : Located field node) (head : ProjectionHead node)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (context : ContextDerivation sourceEnv U current)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ current)
    (tails : SortableTailPairedFits env registry target context locals σ σ available)
    {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (nameEq : record.family.name = name) (member : (index, request) ∈ record.fields)
    (majorQuery : RichObs sourceEnv env U registry target (.ref (.right head.major)) locals σ
      (.singleton (n := n + 1) (.record record)) majorFootprint)
    (majorCalls : ValueCalls env registry context majorQuery)
    (fieldCode : RichCert sourceEnv env U registry target head.field locals σ true support fieldFootprint)
    (fieldCalls : CodeCalls env registry context fieldCode)
    (typed : request.input.HasType support)
    (alignment : DomainChain env U registry target request.input request.domain (head.fieldType.subst σ))
    (majorResources : majorFootprint.Available available)
    (fieldResources : fieldFootprint.Available available) :
    ∃ value : RichBinderValue sourceEnv env U registry target
      (HeaderOwner.projected (major := major) start head).node locals σ σ available request.input,
      value.support = support := by
  obtain ⟨majorValue⟩ := majorCalls.interpret henv hscoped closed formed substitutions tails majorResources
  have fieldValue := fieldCalls.interpret henv hscoped closed formed substitutions tails fieldResources
  have projected := majorValue.related.projectRecord henv hscoped formed member
  refine ⟨{
    support := support
    footprint := fieldFootprint
    certificate := fieldCode
    resources := fieldResources
    typed := typed
    related := ?_ }, rfl⟩
  simpa only [HeaderOwner.projected, HeaderOwner.node, HeaderOwner.expression, HeaderOwner.assigned, subst, nameEq] using
    alignment.related henv typed fieldValue projected

/-- The dependent `Pack` link is a complete source producer. It builds the
first projected TYPE query recursively, interprets the second projected
VALUE query from its original children, creates the declaration-variable
certificate, and extends the real heterogeneous header tail. -/
theorem HeaderRichTail.pushDependentField
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {headerContext : ContextDerivation headerEnv U headerSource}
    {node : EndpointState sourceEnv U current (.proj name secondIndex (.bvar slot)) assigned}
    (start : Located field node) (head : ProjectionHead node)
    (dependent : head.fieldType = .proj name firstIndex (.bvar slot))
    (sortLevel : VLevel)
    (firstSort : (projectionHead (head.field.cast dependent rfl)).fieldType = .sort sortLevel)
    (sortRelevant : Relevant sortLevel true)
    {typeDemand valueDemand : Profile n}
    (typeFormed : typeDemand.HasType (.sort true))
    (valueTyped : valueDemand.HasType typeDemand)
    (family : FamilyData (Profile n)) (familyName : family.name = name)
    (familyRelevant : family.relevant = true)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (headerBelow : headerEnv ≤ env) (sourceBelow : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (sourceContext : ContextDerivation sourceEnv U source)
    (firstMajorF : StateHereditaryFundamental env registry (start.contextDerivation sourceContext)
      (.ref (.right (projectionHead (head.field.cast dependent rfl)).major)))
    (firstFieldF : StateSortableFundamental env registry (start.contextDerivation sourceContext)
      (projectionHead (head.field.cast dependent rfl)).field)
    (secondMajorF : StateHereditaryFundamental env registry (start.contextDerivation sourceContext)
      (.ref (.right head.major)))
    (closed : ownerAvailable.AtomClosed)
    (ownerSubstitutions : Ctx.SubstEq env U target σ σ current)
    (ownerTails : SortableTailPairedFits env registry target (start.contextDerivation sourceContext)
      ownerLocals σ σ ownerAvailable)
    (firstResource : majorNeed (fieldRecord family familyRelevant firstIndex
      (fieldRequest (projectionHead (head.field.cast dependent rfl)) σ typeDemand (.sort true))) ∈
      ownerAvailable slot)
    (secondResource : majorNeed (fieldRecord family familyRelevant secondIndex
      (fieldRequest head σ valueDemand typeDemand)) ∈ ownerAvailable slot)
    (tail : HeaderRichTail header field major env registry target headerContext locals left right available)
    (substitutions : Ctx.SubstEq env U target left right headerSource)
    (domain : EndpointRef headerEnv U headerSource (.bvar previous) (.sort level))
    (location : Located header (.ref domain))
    (lineage : location.contextDerivation .nil = headerContext)
    (priorNeed : Need.mk n typeDemand ∈ available previous)
    (priorLookup : Lookup headerSource previous previousType)
    (priorValue : head.fieldType.subst σ = left previous)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ valueDemand.atoms) :
    Nonempty (HeaderRichTail header field major env registry target (.cons headerContext domain)
      (Locals.push locals)
      (left.cons ((VExpr.proj name secondIndex (.bvar slot)).subst σ))
      (right.cons ((VExpr.proj name secondIndex (.bvar slot)).subst σ)) (available.push needs)) ∧
    Ctx.SubstEq env U target
      (left.cons ((VExpr.proj name secondIndex (.bvar slot)).subst σ))
      (right.cons ((VExpr.proj name secondIndex (.bvar slot)).subst σ))
      (.bvar previous :: headerSource) := by
  obtain ⟨fieldCode, fieldCalls, _, _⟩ := dependentFieldCalls
    (target := target) (locals := ownerLocals) (σ := σ) head dependent sortLevel firstSort
    sortRelevant typeFormed valueTyped family familyName familyRelevant
    (start.contextDerivation sourceContext) firstMajorF firstFieldF secondMajorF
  let record := fieldRecord family familyRelevant secondIndex
    (fieldRequest head σ valueDemand typeDemand)
  let query : RichObs sourceEnv env U registry target (.ref (.right head.major)) ownerLocals σ
      (.singleton (n := n + 1) (.record record)) [(slot, majorNeed record)] :=
    .legacy (.legacy (.var ownerLocals σ slot _))
  have calls : ValueCalls env registry (start.contextDerivation sourceContext) query :=
    .legacy secondMajorF
  have fieldResources : Footprint.Available [(slot, majorNeed (fieldRecord family familyRelevant firstIndex
      (fieldRequest (projectionHead (head.field.cast dependent rfl)) σ typeDemand (.sort true))))]
      ownerAvailable := by
    intro index need member
    cases List.mem_singleton.mp member
    exact firstResource
  have majorResources : Footprint.Available [(slot, majorNeed record)] ownerAvailable := by
    intro index need member
    cases List.mem_singleton.mp member
    exact secondResource
  obtain ⟨value, supportEq⟩ := HeaderOwner.projectedValue (major := major) start head henv hscoped
    (start.contextDerivation sourceContext) closed formed ownerSubstitutions ownerTails
    (show record.family.name = name from familyName) (List.mem_singleton_self _)
    query calls fieldCode fieldCalls valueTyped (.refl _) majorResources fieldResources
  have needed : Need.mk n value.support ∈ available previous := by rw [supportEq]; exact priorNeed
  obtain ⟨alignment⟩ := HeaderValueAlignment.priorField henv hscoped formed tail domain
    (HeaderOwner.projected start head) value needed priorLookup priorValue
  exact tail.pushAligned henv headerBelow sourceBelow formed substitutions domain location lineage
    (HeaderOwner.projected start head) ownerSubstitutions alignment needs bounded covered

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
