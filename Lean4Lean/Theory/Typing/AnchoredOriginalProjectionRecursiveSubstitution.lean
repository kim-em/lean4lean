import Lean4Lean.Theory.Typing.AnchoredOriginalDependentProjectionInterpretation

/-! A recursively projected field query under a known original beta
substitution. The actual argument F constructs the richer tail and every
finite captured query. The result retains the original projection template
and the source action, together with its concrete target interpretation.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- A core argument query embeds without discarding its finite general
adapter or changing the actual original argument endpoint. -/
def RichGradedResult.ofCore
    {node : EndpointState sourceEnv U source expression assigned}
    (result : SortableGradedResult env U registry target locals σ available expression demand) :
    RichGradedResult sourceEnv env U registry target node locals σ available demand where
  rank := result.rank
  bound := result.bound
  raw := result.raw
  footprint := result.footprint
  observation := .legacy result.observation
  adapter := result.adapter
  resources := result.resources
  live := result.live

/-- Build the entire finite replacement list from the one actual argument
answer. Each selected query keeps the same argument source and resources. -/
noncomputable def RichArgumentSupply.ofCore
    {available : Valuation}
    {node : EndpointState sourceEnv U source expression assigned}
    (result : SortableGradedResult env U registry target locals σ available expression (input : Profile n))
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (included : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    RichArgumentSupply sourceEnv env U registry target node locals σ available needs :=
  match needs with
  | [] => .nil
  | need :: rest => .cons
      (RichGradedResult.ofCore (result.localDemand need (bounded need (List.mem_cons_self))
        (included need (List.mem_cons_self))))
      (RichArgumentSupply.ofCore result rest
        (fun next member => bounded next (List.mem_cons_of_mem _ member))
        (fun next member => included next (List.mem_cons_of_mem _ member)))

/-- A usable source suspension: its field certificate and major observer
remain actual recursively rich source syntax, and its interpretation refers
to the displayed instantiated expressions. -/
structure InterpretedProjectionLeaf
    (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    {source : List VExpr} {A argumentExpression major assigned : VExpr} {domainLevel : VLevel}
    (domain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (argument : EndpointRef sourceEnv U source argumentExpression A)
    (template : EndpointRef sourceEnv U (A :: source) (.proj name index major) assigned)
    (context : ContextDerivation sourceEnv U source)
    (locals : List Nat) (σ : Subst) (available : Valuation) (demand : Profile n) where
  leaf : InstantiatedProjectionLeaf sourceEnv env U registry target domain argument template context
    locals σ available demand
  code : TypeRelated env U registry target ((leaf.head.fieldType.inst argumentExpression).subst σ)
    ((leaf.head.fieldType.inst argumentExpression).subst σ) leaf.support
  related : Related env U registry target (((VExpr.proj name index major).inst argumentExpression).subst σ)
    (((VExpr.proj name index major).inst argumentExpression).subst σ)
    ((leaf.head.fieldType.inst argumentExpression).subst σ) demand leaf.support

/-- Interpret a projection suspension with recursively projected field code.
The only nonrecursive semantic input is F for the actual beta argument;
the remaining finite calls are precisely the retained original leaves of the
major and field query trees. Capture rank is independent of output rank. -/
theorem interpretRichProjectionInst
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {A argumentExpression major assigned : VExpr} {domainLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (argument : EndpointRef sourceEnv U source argumentExpression A)
    (template : EndpointRef sourceEnv U (A :: source) (.proj name index major) assigned)
    (head : ProjectionHead (.ref template))
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (argumentF : StateHereditaryFundamental env registry context (.ref argument))
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tails : SortableTailPairedFits env registry target context locals σ σ available)
    {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
    {input packed : Profile captureRank} {support : Profile n}
    (nameEq : record.family.name = name) (member : (index, request) ∈ record.fields)
    (majorQuery : RichObs sourceEnv env U registry target (.ref (.right head.major)) (Locals.push locals)
      (σ.cons (argumentExpression.subst σ)) (.singleton (n := n + 1) (.record record)) majorFootprint)
    (fieldCode : RichCert sourceEnv env U registry target head.field (Locals.push locals)
      (σ.cons (argumentExpression.subst σ)) true support fieldFootprint)
    (majorCalls : ValueCalls env registry (.cons context domain) majorQuery)
    (fieldCalls : CodeCalls env registry (.cons context domain) fieldCode)
    (typed : request.input.HasType support)
    (alignment : DomainChain env U registry target request.input request.domain
      (head.fieldType.subst (σ.cons (argumentExpression.subst σ))))
    (pack : BinderPack captureRank packed (majorFootprint ++ fieldFootprint) outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ input.atoms)
    (outsideResources : outside.Available available)
    (argumentQuery : SortableObs env U registry target locals σ argumentExpression input argumentFootprint)
    (argumentResources : argumentFootprint.Available available) :
    Nonempty (InterpretedProjectionLeaf sourceEnv env U registry target domain argument template context
      locals σ available request.input) := by
  obtain ⟨answer⟩ := argumentF target locals σ σ available closed formed substitutions tails
    argumentQuery argumentResources
  have arguments := answer.requestedRelated henv formed
  let needs := (majorFootprint ++ fieldFootprint).localNeeds ++
    (majorFootprint ++ fieldFootprint).localNeeds.flatMap Need.singletons
  have bounded : ∀ need ∈ needs, need.rank ≤ captureRank := fun need member =>
    (pack.atomized_localNeeds need member).1
  have included : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade captureRank).atoms, atom ∈ input.atoms :=
    fun need member atom present => covered atom ((pack.atomized_localNeeds need member).2 atom present)
  let fitted := tails.pushCertificates domain answer.requestedCertificate answer.requestedCertificate
    answer.typeAvailable answer.typeAvailable answer.requestedTyped answer.requestedTyped
    arguments arguments needs bounded included
  have rawArgument := (argument.sound.defeq.mono below).substDF henv substitutions.wf formed substitutions
  have instantiated : Ctx.SubstEq env U target (σ.cons (argumentExpression.subst σ))
      (σ.cons (argumentExpression.subst σ)) (A :: source) :=
    .cons substitutions (domain.sound.defeq.mono below) rawArgument
  have localClosed := Valuation.push_atomized_closed closed (majorFootprint ++ fieldFootprint).localNeeds
  have resources := pack.available_atomized_localNeeds outsideResources
  obtain ⟨majorValue⟩ := majorCalls.interpret henv hscoped localClosed formed instantiated fitted
    (fun index need member => resources index need (List.mem_append_left _ member))
  have field := fieldCalls.interpret henv hscoped localClosed formed instantiated fitted
    (fun index need member => resources index need (List.mem_append_right _ member))
  have projected := majorValue.related.projectRecord henv hscoped formed member
  have natural := alignment.related henv typed field projected
  let replacements : RichArgumentSupply sourceEnv env U registry target (.ref argument) locals σ
      available needs := RichArgumentSupply.ofCore answer.toSortableGradedResult needs bounded included
  let leaf := retainProjectionInst context domain argument template head nameEq member
    majorQuery fieldCode typed alignment pack outsideResources replacements
  refine ⟨{ leaf := leaf, code := ?_, related := ?_ }⟩
  · simpa only [leaf, retainProjectionInst, subst_inst, inst_lift_cons] using field
  · have natural' : Related env U registry target
        ((VExpr.proj name index major).subst (σ.cons (argumentExpression.subst σ)))
        ((VExpr.proj name index major).subst (σ.cons (argumentExpression.subst σ)))
        (head.fieldType.subst (σ.cons (argumentExpression.subst σ))) request.input support := by
      simpa only [nameEq, subst] using natural
    simpa only [leaf, retainProjectionInst, subst_inst, inst_lift_cons] using natural' 

/-- The dependent Pack link under an actual beta argument. Both record
requests are packed at rank `n + 1`; all source certificates, replacement
queries and the suspended semantic result are constructed here. -/
theorem dependentFieldInst
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {A argumentExpression assigned : VExpr} {domainLevel : VLevel}
    {name : Name} {firstIndex secondIndex : Nat}
    (context : ContextDerivation sourceEnv U source)
    (domain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (argument : EndpointRef sourceEnv U source argumentExpression A)
    (template : EndpointRef sourceEnv U (A :: source) (.proj name secondIndex (.bvar 0)) assigned)
    (head : ProjectionHead (.ref template))
    (dependent : head.fieldType = .proj name firstIndex (.bvar 0))
    (sortLevel : VLevel)
    (firstSort : (projectionHead (head.field.cast dependent rfl)).fieldType = .sort sortLevel)
    (sortLevelRelevant : Relevant sortLevel true)
    {typeDemand valueDemand : Profile n}
    (typeFormed : typeDemand.HasType (.sort true))
    (valueTyped : valueDemand.HasType typeDemand)
    (family : FamilyData (Profile n)) (familyName : family.name = name)
    (familyRelevant : family.relevant = true)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (argumentF : StateHereditaryFundamental env registry context (.ref argument))
    (firstMajorF : StateHereditaryFundamental env registry (.cons context domain)
      (.ref (.right (projectionHead (head.field.cast dependent rfl)).major)))
    (firstFieldF : StateSortableFundamental env registry (.cons context domain)
      (projectionHead (head.field.cast dependent rfl)).field)
    (secondMajorF : StateHereditaryFundamental env registry (.cons context domain) (.ref (.right head.major)))
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tails : SortableTailPairedFits env registry target context locals σ σ available) :
    let realization := σ.cons (argumentExpression.subst σ)
    let first := projectionHead (head.field.cast dependent rfl)
    let firstRecord := fieldRecord family familyRelevant firstIndex
      (fieldRequest first realization typeDemand (.sort true))
    let secondRecord := fieldRecord family familyRelevant secondIndex
      (fieldRequest head realization valueDemand typeDemand)
    let input := (majorNeed secondRecord).atGrade (n + 1) |>.union
      ((majorNeed firstRecord).atGrade (n + 1) |>.union .empty)
    ∀ {argumentFootprint},
      SortableObs env U registry target locals σ argumentExpression input argumentFootprint →
      argumentFootprint.Available available →
      Nonempty (InterpretedProjectionLeaf sourceEnv env U registry target domain argument template context
        locals σ available valueDemand) := by
  dsimp only
  intro argumentFootprint argumentQuery argumentResources
  let realization := σ.cons (argumentExpression.subst σ)
  let first := projectionHead (head.field.cast dependent rfl)
  let firstRecord := fieldRecord family familyRelevant firstIndex
    (fieldRequest first realization typeDemand (.sort true))
  let secondRecord := fieldRecord family familyRelevant secondIndex
    (fieldRequest head realization valueDemand typeDemand)
  obtain ⟨certificate, codeCalls, _, _⟩ := dependentFieldCalls
    (target := target) (locals := Locals.push locals) (σ := realization) head dependent sortLevel firstSort
    sortLevelRelevant typeFormed valueTyped family familyName familyRelevant (.cons context domain)
    firstMajorF firstFieldF secondMajorF
  let majorQuery : RichObs sourceEnv env U registry target (.ref (.right head.major))
      (Locals.push locals) realization (.singleton (n := n + 1) (.record secondRecord))
      [(0, majorNeed secondRecord)] := .legacy (.legacy (.var _ _ 0 _))
  have pack : BinderPack (n + 1)
      ((majorNeed secondRecord).atGrade (n + 1) |>.union
        ((majorNeed firstRecord).atGrade (n + 1) |>.union .empty))
      ([(0, majorNeed secondRecord)] ++ [(0, majorNeed firstRecord)]) [] :=
    .local _ (Nat.le_refl _) (.local _ (Nat.le_refl _) .nil)
  exact interpretRichProjectionInst context domain argument template head henv hscoped below argumentF
    closed formed substitutions tails (show secondRecord.family.name = name from familyName)
    (List.mem_singleton_self _) majorQuery certificate (.legacy secondMajorF) codeCalls
    valueTyped (.refl _) pack (fun _ member => member) (by intro _ _ member; cases member)
    argumentQuery argumentResources

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
