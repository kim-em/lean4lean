import Lean4Lean.Theory.Typing.AnchoredOriginalScopedCaptureGeneration
import Lean4Lean.Theory.Typing.AnchoredOriginalGroupedParameterReserve

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- Both contexts are captured by the SAME raw owner expressions. Their
original domain annotations may differ. No target equality is used to
manufacture this source display. -/
def OriginalCaptureMap.parameterCellDisplay
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (provenance : EndpointProvenance context (.ref domain)) :
    OriginalNestedDisplay U common (A.subst raw) (.sort level) := {
  sourceEnv := sourceEnv, source := source, sourceExpression := A, sourceType := .sort level
  context := context, node := .ref domain, provenance := provenance, raw := raw, graph := graph
  expression_eq := rfl, type_eq := rfl }

/-- One retained equality cell, read backwards, converts an actual family
parameter query to the common parameter. The source reindex edge has the
same raw expression and shared capture map; the second edge is literally
the original equality, not an inferred equality of assigned types. -/
theorem parameterCellBackward
    {commonSource familySource : List VExpr}
    (henv : env.Ordered) (below : base ≤ env)
    (formed : OnCtx target (env.IsType U))
    (cell : Derivation base U commonSource A B (.sort level))
    (domain : EndpointRef familyEnv U familySource B (.sort familyLevel))
    (substitutions : Ctx.SubstEq env U target σ σ commonSource)
    (sourceR : RichCodeTransfer env U registry target (.ref domain) (.ref (.right cell))
      familyLocals commonLocals σ σ familyAvailable commonAvailable)
    (equalityF : RichCodeTransfer env U registry target (.ref (.right cell)) (.ref (.left cell))
      commonLocals commonLocals σ σ commonAvailable commonAvailable) :
    RichCodeTransfer env U registry target (.ref domain) (.ref (.left cell))
      familyLocals commonLocals σ σ familyAvailable commonAvailable ∧
    TypeConversion env U target (B.subst σ) (A.subst σ) := by
  constructor
  · intro relevant n profile footprint query resources
    obtain ⟨first⟩ := sourceR query resources
    obtain ⟨second⟩ := equalityF first.certificate first.resources
    exact ⟨{ second with related := first.related.trans henv second.related }⟩
  · have raw := (cell.forget.defeq.mono below).substDF henv substitutions.wf formed substitutions
    exact .single raw.symm

/-- Convert one existing aligned owner through a computed parameter-cell
answer, retaining the SAME owner frame, original query, and input profile. -/
noncomputable def RichGroupedCaptureEntry.realign
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {oldDomain : EndpointRef oldEnv U oldSource A (.sort oldLevel)}
    {newDomain : EndpointRef newEnv U newSource B (.sort newLevel)}
    (henv : env.Ordered)
    (entry : RichGroupedCaptureEntry (field := field) (major := major) oldDomain env registry target
      oldLocals oldSubst oldAvailable ownerInitial rawCapture leftValue rightValue)
    (transfer : RichCodeTransfer env U registry target (.ref oldDomain) (.ref newDomain)
      oldLocals newLocals oldSubst newSubst oldAvailable newAvailable)
    (path : TypeConversion env U target (A.subst oldSubst) (B.subst newSubst)) :
    RichGroupedCaptureEntry (field := field) (major := major) newDomain env registry target
      newLocals newSubst newAvailable ownerInitial rawCapture leftValue rightValue := by
  let changed := Classical.choice (transfer entry.answer.aligned.certificate entry.answer.aligned.resources)
  exact {
    owner := entry.owner, ownerLocals := entry.ownerLocals, ownerLeft := entry.ownerLeft
    ownerRight := entry.ownerRight, ownerAvailable := entry.ownerAvailable
    initialContext := entry.initialContext, frame := entry.frame, substitutions := entry.substitutions
    frame_environment_le := entry.frame_environment_le, depth := entry.depth
    sourcePrefix := entry.sourcePrefix, source_eq := entry.source_eq, depth_eq := entry.depth_eq
    expression_eq := entry.expression_eq, left_eq := entry.left_eq, right_eq := entry.right_eq
    rank := entry.rank, input := entry.input
    queryRank := entry.queryRank, queryInput := entry.queryInput
    queryBound := entry.queryBound, queryAdapter := entry.queryAdapter
    footprint := entry.footprint, query := entry.query
    queryAvailable := entry.queryAvailable
    answer := {
      value := entry.answer.value
      aligned := { changed with related := entry.answer.aligned.related.trans henv changed.related }
      path := entry.answer.path.trans path } }

/-- Every atom of the finite slot is replayed against the one prior frame.
The next valuation is unchanged: no new owner demands are invented when
converting the already-discovered declared parameter domain. -/
noncomputable def realignParameterEntries
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {oldDomain : EndpointRef oldEnv U oldSource A (.sort oldLevel)}
    {newDomain : EndpointRef newEnv U newSource B (.sort newLevel)}
    (henv : env.Ordered)
    (entries : List (RichGroupedCaptureEntry (field := field) (major := major) oldDomain env registry target
      oldLocals oldSubst oldAvailable ownerInitial rawCapture leftValue rightValue))
    (transfer : RichCodeTransfer env U registry target (.ref oldDomain) (.ref newDomain)
      oldLocals newLocals oldSubst newSubst oldAvailable newAvailable)
    (path : TypeConversion env U target (A.subst oldSubst) (B.subst newSubst)) :=
  entries.map (fun entry => entry.realign henv transfer path)

theorem realignParameterEntries_needs
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {oldDomain : EndpointRef oldEnv U oldSource A (.sort oldLevel)}
    {newDomain : EndpointRef newEnv U newSource B (.sort newLevel)}
    (henv : env.Ordered)
    (entries : List (RichGroupedCaptureEntry (field := field) (major := major) oldDomain env registry target
      oldLocals oldSubst oldAvailable ownerInitial rawCapture leftValue rightValue))
    (transfer : RichCodeTransfer env U registry target (.ref oldDomain) (.ref newDomain)
      oldLocals newLocals oldSubst newSubst oldAvailable newAvailable)
    (path : TypeConversion env U target (A.subst oldSubst) (B.subst newSubst)) :
    (realignParameterEntries henv entries transfer path).flatMap (fun entry => captureNeeds entry.input) =
      entries.flatMap (fun entry => captureNeeds entry.input) := by
  simp only [realignParameterEntries, List.flatMap_map]
  rfl

/-- The changed parameter slot is an actual generated capture frame, with
all original owner-frame extensions preserved. In particular this step does
not assume validity of the common-prefix group it is constructing. -/
theorem realignParameterEntries_generated
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation headerEnv U headerSource}
    {graph : OriginalCaptureMap (common := common) context raw}
    {tail : OriginalRichFrame headerEnv env U registry target context locals σ τ available}
    (generated : ScopedCaptureGenerated base commonLeft commonRight graph tail.raw)
    (domain : EndpointRef headerEnv U headerSource B (.sort level))
    {ownerContext : ContextDerivation ownerEnv U ownerSource}
    {ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw}
    {ownerFrame : RawOriginalRichFrame ownerEnv env U registry target ownerContext ownerLocals ownerLeft ownerRight ownerAvailable}
    (ownerGenerated : ScopedCaptureGenerated base commonLeft commonRight ownerGraph ownerFrame)
    {nominalContext : ContextDerivation nominalEnv U nominalSource}
    (nominalGraph : OriginalCaptureMap (common := common) nominalContext nominalRaw)
    (nominal : EndpointState nominalEnv U nominalSource argument assigned)
    (provenance : EndpointProvenance nominalContext nominal)
    (displayed : rawCapture.subst ownerRaw = argument.subst nominalRaw)
    {field : EndpointRef ownerEnv U ownerSource fieldExpression fieldType}
    {major : EndpointRef ownerEnv U ownerSource majorExpression majorType}
    (ownerOrdered : ownerEnv.Ordered) (ownerInitial : List Closure)
    {oldDomain : EndpointRef oldEnv U oldSource A (.sort oldLevel)}
    (henv : env.Ordered)
    (entries : List (RichGroupedCaptureEntry (field := field) (major := major) oldDomain env registry target
      oldLocals oldSubst oldAvailable ownerInitial rawCapture (rawCapture.subst ownerLeft) (rawCapture.subst ownerRight)))
    (transfer : RichCodeTransfer env U registry target (.ref oldDomain) (.ref domain)
      oldLocals locals oldSubst σ oldAvailable available)
    (path : TypeConversion env U target (A.subst oldSubst) (B.subst σ))
    (owners : ∀ entry ∈ entries, Nonempty (OriginalFrameExtension ownerFrame entry.frame.raw)) :
    ScopedCaptureGenerated base commonLeft commonRight
      (.capture graph domain nominalGraph nominal provenance)
      (tail.group domain ownerOrdered ownerInitial (realignParameterEntries henv entries transfer path)).raw := by
  apply ScopedCaptureGenerated.group generated domain ownerGenerated nominalGraph nominal provenance
    displayed ownerOrdered ownerInitial (realignParameterEntries henv entries transfer path)
  intro changed member
  change changed ∈ entries.map (fun entry => entry.realign henv transfer path) at member
  obtain ⟨entry, originalMember, rfl⟩ := List.mem_map.mp member
  exact owners entry originalMember

/-- Actual semantic groups also compute the mixed declaration ledger. A
parameter equality cell needs no fabricated location in the constructor
header: its independently retained original dependency is the domain. -/
noncomputable def RichGroupedCapture.parameterLedgerStep
    (ordered : sourceEnv.Ordered)
    {header : EndpointRef headerEnv U headerSource headerExpression headerType}
    {domain : EndpointRef domainEnv U domainSource A (.sort level)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (declared : Dependency.ParameterDomain headerOrdered header roots)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      domainLocals declaredLeft domainAvailable ownerInitial rawCapture leftValue rightValue) :
    Dependency.GroupedParameterStep headerOrdered ordered header field major roots := {
  domain := declared
  owners := .inl ⟨_, _, _, .ref field, .here⟩ :: .inr ⟨_, _, _, .ref major, .here⟩ ::
    entries.map (fun entry => entry.owner.map (Dependency.measureLocated ordered)
    (Dependency.measureLocated ordered)) }

theorem OriginalRichFrame.group_parameterLedger
    (ordered : sourceEnv.Ordered) (domainOrdered : domainEnv.Ordered)
    {header : EndpointRef headerEnv U headerSource headerExpression headerType}
    {domain : EndpointRef domainEnv U domainSource A (.sort level)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation domainEnv U domainSource}
    (declared : Dependency.ParameterDomain headerOrdered header roots)
    (original : declared.origin = domain.dependencyOrigin domainOrdered)
    (tail : OriginalRichFrame domainEnv env U registry target context
      domainLocals declaredLeft declaredRight domainAvailable)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      domainLocals declaredLeft domainAvailable ownerInitial rawCapture leftValue rightValue)
    (steps : List (Dependency.GroupedParameterStep headerOrdered ordered header field major roots))
    (ledger : tail.dependencyEnvironment domainOrdered = Dependency.groupedParameterEnvironment steps ownerInitial) :
    (tail.group domain ordered ownerInitial entries).dependencyEnvironment domainOrdered =
      Dependency.groupedParameterEnvironment (entries.parameterLedgerStep ordered declared :: steps) ownerInitial := by
  rw [OriginalRichFrame.group_environment, ledger]
  have owners : ∀ declaredClosure : Closure,
      entries.map (fun entry => Closure.bundle (entry.owner.dependencyClosure ordered ownerInitial) declaredClosure) =
      entries.map (fun entry => Closure.bundle
        (Dependency.groupedOwnerClosure (entry.owner.map (Dependency.measureLocated ordered)
          (Dependency.measureLocated ordered)) ownerInitial) declaredClosure) := by
    intro declaredClosure
    apply List.map_congr_left
    intro entry _
    cases entry.owner <;> rfl
  simp only [RichGroupedCapture.environment, Dependency.groupedParameterEnvironment,
    RichGroupedCapture.parameterLedgerStep, original, List.map_cons, List.map_map, Function.comp_def]
  rw [← owners]
  rfl

/-- The two declaration legs and universe bridge stay three independent
original proofs. Four same-SOURCE-expression reindex calls connect their
actual occurrences; no context equality is composed through uniqueness of
typing. All seven answers retain their outgoing source certificates. -/
theorem parameterCellsTransfer
    {familyContext seedContext requestedContext ctorContext : List VExpr}
    (henv : env.Ordered) (baseBelow : base ≤ env) (typesBelow : types ≤ env)
    (formed : OnCtx target (env.IsType U))
    (familyCell : Derivation base U seedContext seedDomain familyDomain (.sort familySort))
    (universeCell : Derivation base U seedContext seedDomain requestedDomain (.sort universeSort))
    (ctorCell : Derivation types U requestedContext requestedDomain ctorDomain (.sort ctorSort))
    (family : EndpointRef familyEnv U familyContext familyDomain (.sort familyLevel))
    (constructor : EndpointRef ctorEnv U ctorContext ctorDomain (.sort ctorLevel))
    (seedSubstitutions : Ctx.SubstEq env U target σ σ seedContext)
    (requestedSubstitutions : Ctx.SubstEq env U target σ σ requestedContext)
    (familyR : RichCodeTransfer env U registry target (.ref family) (.ref (.right familyCell))
      familyLocals seedLocals σ σ familyAvailable seedAvailable)
    (familyF : RichCodeTransfer env U registry target (.ref (.right familyCell)) (.ref (.left familyCell))
      seedLocals seedLocals σ σ seedAvailable seedAvailable)
    (seedR : RichCodeTransfer env U registry target (.ref (.left familyCell)) (.ref (.left universeCell))
      seedLocals seedLocals σ σ seedAvailable seedAvailable)
    (universeF : RichCodeTransfer env U registry target (.ref (.left universeCell)) (.ref (.right universeCell))
      seedLocals seedLocals σ σ seedAvailable seedAvailable)
    (requestedR : RichCodeTransfer env U registry target (.ref (.right universeCell)) (.ref (.left ctorCell))
      seedLocals requestedLocals σ σ seedAvailable requestedAvailable)
    (ctorF : RichCodeTransfer env U registry target (.ref (.left ctorCell)) (.ref (.right ctorCell))
      requestedLocals requestedLocals σ σ requestedAvailable requestedAvailable)
    (ctorR : RichCodeTransfer env U registry target (.ref (.right ctorCell)) (.ref constructor)
      requestedLocals ctorLocals σ σ requestedAvailable ctorAvailable) :
    RichCodeTransfer env U registry target (.ref family) (.ref constructor)
      familyLocals ctorLocals σ σ familyAvailable ctorAvailable ∧
    TypeConversion env U target (familyDomain.subst σ) (ctorDomain.subst σ) := by
  obtain ⟨firstLeg, firstPath⟩ := parameterCellBackward henv baseBelow formed familyCell family
    seedSubstitutions familyR familyF
  constructor
  · intro relevant n profile footprint query resources
    obtain ⟨first⟩ := firstLeg query resources
    obtain ⟨second⟩ := seedR first.certificate first.resources
    obtain ⟨third⟩ := universeF second.certificate second.resources
    obtain ⟨fourth⟩ := requestedR third.certificate third.resources
    obtain ⟨fifth⟩ := ctorF fourth.certificate fourth.resources
    obtain ⟨sixth⟩ := ctorR fifth.certificate fifth.resources
    exact ⟨{ sixth with related := first.related.trans henv (second.related.trans henv
      (third.related.trans henv (fourth.related.trans henv (fifth.related.trans henv sixth.related)))) }⟩
  · have middle := (universeCell.forget.defeq.mono baseBelow).substDF henv
      seedSubstitutions.wf formed seedSubstitutions
    have last := (ctorCell.forget.defeq.mono typesBelow).substDF henv
      requestedSubstitutions.wf formed requestedSubstitutions
    exact (firstPath.trans (.single middle)).trans (.single last)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
