import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionRecursiveInterpretation

/-! A dependent field query with a recursively interpreted projected type.
For `Pack(T : Type)(x : T)`, the second field's original formation child is
the first projection. Only its original sort child and the two original
major children are fundamental calls; no fundamental call is assumed for
the richer projected type query itself.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem CodeCalls.ofCast
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source expression assigned}
    (expressionEq : expression = nextExpression) (typeEq : assigned = nextType)
    {certificate : RichCert sourceEnv env U registry target (node.cast expressionEq typeEq)
      locals σ relevant profile footprint}
    (calls : CodeCalls env registry context certificate) :
    CodeCalls env registry context (RichCert.ofCast expressionEq typeEq certificate) := by
  cases expressionEq
  cases typeEq
  exact calls

/-- Construct both actual source queries and their finite original leaf
ledger. The dependent projected type is produced recursively, rather than
passed as a certificate or a semantic answer. -/
theorem dependentFieldCalls
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {name : Name} {firstIndex secondIndex slot : Nat} {assigned : VExpr}
    {node : EndpointState sourceEnv U source (.proj name secondIndex (.bvar slot)) assigned}
    (head : ProjectionHead node)
    (dependent : head.fieldType = .proj name firstIndex (.bvar slot))
    (sortLevel : VLevel)
    (firstSort : (projectionHead (head.field.cast dependent rfl)).fieldType = .sort sortLevel)
    (sortLevelRelevant : Relevant sortLevel true)
    {typeDemand valueDemand : Profile n}
    (typeFormed : typeDemand.HasType (.sort true))
    (valueTyped : valueDemand.HasType typeDemand)
    (family : FamilyData (Profile n)) (familyName : family.name = name)
    (familyRelevant : family.relevant = true)
    (context : ContextDerivation sourceEnv U source)
    (firstMajorF : StateHereditaryFundamental env registry context
      (.ref (.right (projectionHead (head.field.cast dependent rfl)).major)))
    (firstFieldF : StateSortableFundamental env registry context
      (projectionHead (head.field.cast dependent rfl)).field)
    (secondMajorF : StateHereditaryFundamental env registry context (.ref (.right head.major))) :
    let first := projectionHead (head.field.cast dependent rfl)
    let firstRequest := fieldRequest first σ typeDemand (.sort true)
    let secondRequest := fieldRequest head σ valueDemand typeDemand
    let firstRecord := fieldRecord family familyRelevant firstIndex firstRequest
    let secondRecord := fieldRecord family familyRelevant secondIndex secondRequest
    ∃ certificate : RichCert sourceEnv env U registry target head.field locals σ true typeDemand
        [(slot, majorNeed firstRecord)],
      CodeCalls env registry context certificate ∧
      ∃ observation : RichObs sourceEnv env U registry target node locals σ valueDemand
          ([(slot, majorNeed secondRecord)] ++ [(slot, majorNeed firstRecord)]),
        ValueCalls env registry context observation := by
  dsimp only
  let first := projectionHead (head.field.cast dependent rfl)
  let firstRequest := fieldRequest first σ typeDemand (.sort true)
  let secondRequest := fieldRequest head σ valueDemand typeDemand
  let firstRecord := fieldRecord family familyRelevant firstIndex firstRequest
  let secondRecord := fieldRecord family familyRelevant secondIndex secondRequest
  have firstCode : SortableCert env U registry target locals σ first.fieldType true
      (Profile.sort (n := n) true) [] := by
    rw [show first.fieldType = .sort sortLevel from firstSort]
    exact .seed (.sort sortLevelRelevant) (Profile.HasType.sort true)
  let firstMajor : RichObs sourceEnv env U registry target (.ref (.right first.major)) locals σ
      (.singleton (n := n + 1) (.record firstRecord)) [(slot, majorNeed firstRecord)] :=
    .legacy (.legacy (.var locals σ slot _))
  have firstSource : ∃ query : RichObs sourceEnv env U registry target
      (head.field.cast dependent rfl) locals σ typeDemand [(slot, majorNeed firstRecord)],
      ValueCalls env registry context query := by
    have calls : ValueCalls env registry context
        (RichObs.projection first (show firstRecord.family.name = name from familyName)
          (List.mem_singleton_self _) firstMajor (.legacy firstCode) typeFormed (.refl _)) :=
      .projection (.legacy firstMajorF) (.legacy firstFieldF)
    exact ⟨_, calls⟩
  obtain ⟨firstQuery, firstCalls⟩ := firstSource
  let actualFieldCode : RichCert sourceEnv env U registry target head.field locals σ true typeDemand
      [(slot, majorNeed firstRecord)] :=
    RichCert.ofCast dependent rfl (.observe firstQuery typeFormed)
  have actualFieldCalls : CodeCalls env registry context actualFieldCode :=
    CodeCalls.ofCast dependent rfl (.observe firstCalls)
  let secondMajor : RichObs sourceEnv env U registry target (.ref (.right head.major)) locals σ
      (.singleton (n := n + 1) (.record secondRecord)) [(slot, majorNeed secondRecord)] :=
    .legacy (.legacy (.var locals σ slot _))
  refine ⟨actualFieldCode, actualFieldCalls,
    RichObs.projection head (show secondRecord.family.name = name from familyName)
      (List.mem_singleton_self _) secondMajor actualFieldCode valueTyped (.refl _), ?_⟩
  exact .projection (.legacy secondMajorF) actualFieldCalls

/-- The produced first projection is interpreted as the actual second field
type. This works with either empty or inhabited finite field requests. -/
theorem dependentField_interpret
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {name : Name} {firstIndex secondIndex slot : Nat} {assigned : VExpr}
    {node : EndpointState sourceEnv U source (.proj name secondIndex (.bvar slot)) assigned}
    (head : ProjectionHead node)
    (dependent : head.fieldType = .proj name firstIndex (.bvar slot))
    (sortLevel : VLevel)
    (firstSort : (projectionHead (head.field.cast dependent rfl)).fieldType = .sort sortLevel)
    (sortLevelRelevant : Relevant sortLevel true)
    {typeDemand valueDemand : Profile n}
    (typeFormed : typeDemand.HasType (.sort true))
    (valueTyped : valueDemand.HasType typeDemand)
    (family : FamilyData (Profile n)) (familyName : family.name = name)
    (familyRelevant : family.relevant = true)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (context : ContextDerivation sourceEnv U source)
    (firstMajorF : StateHereditaryFundamental env registry context
      (.ref (.right (projectionHead (head.field.cast dependent rfl)).major)))
    (firstFieldF : StateSortableFundamental env registry context
      (projectionHead (head.field.cast dependent rfl)).field)
    (secondMajorF : StateHereditaryFundamental env registry context (.ref (.right head.major)))
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tails : SortableTailPairedFits env registry target context locals σ σ available)
    (firstResource : majorNeed (fieldRecord family familyRelevant firstIndex
      (fieldRequest (projectionHead (head.field.cast dependent rfl)) σ typeDemand (.sort true))) ∈ available slot)
    (secondResource : majorNeed (fieldRecord family familyRelevant secondIndex
      (fieldRequest head σ valueDemand typeDemand)) ∈ available slot) :
    TypeRelated env U registry target (head.fieldType.subst σ) (head.fieldType.subst σ) typeDemand ∧
    Related env U registry target ((VExpr.proj name secondIndex (.bvar slot)).subst σ)
      ((VExpr.proj name secondIndex (.bvar slot)).subst σ) (head.fieldType.subst σ)
      valueDemand typeDemand := by
  obtain ⟨certificate, codeCalls, observation, valueCalls⟩ := dependentFieldCalls
    (target := target) (locals := locals) (σ := σ) head dependent sortLevel firstSort
    sortLevelRelevant typeFormed valueTyped family familyName familyRelevant context
    firstMajorF firstFieldF secondMajorF
  constructor
  · apply codeCalls.interpret henv hscoped closed formed substitutions tails
    intro index need member
    cases List.mem_singleton.mp member
    exact firstResource
  · let record := fieldRecord family familyRelevant secondIndex
      (fieldRequest head σ valueDemand typeDemand)
    let majorQuery : SortableObs env U registry target locals σ (.bvar slot)
        (.singleton (n := n + 1) (.record record)) [(slot, majorNeed record)] :=
      .legacy (.var locals σ slot _)
    obtain ⟨majorAnswer⟩ := secondMajorF target locals σ σ available closed formed
      substitutions tails majorQuery (by
        intro index need member
        cases List.mem_singleton.mp member
        exact secondResource)
    have projected := (majorAnswer.requestedRelated henv formed).projectRecord henv hscoped formed
      (show (secondIndex, fieldRequest head σ valueDemand typeDemand) ∈ record.fields from
        List.mem_singleton_self _)
    simpa only [record, fieldRecord, fieldRequest, familyName, subst] using projected

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
