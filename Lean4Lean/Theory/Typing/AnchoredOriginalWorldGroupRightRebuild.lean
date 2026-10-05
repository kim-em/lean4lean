import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFrameRightRebuild
import Lean4Lean.Theory.Typing.AnchoredOriginalRightFrameTranscript

/-! Fixed-support reconstruction of an actual grouped owner's alignment.
The owner query, owner assigned certificate and declared certificate are
interpreted separately at their actual frames. The old advertised support is
preserved, so the three selected outputs can be installed together. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

private theorem pairLeftCall {count : Nat} {child left right : World count}
    (smaller : WorldBelow count child left) (frontier : List (World count)) :
    CallBelow count (frontier ++ [child]) (frontier ++ [left, right]) := by
  have drop : CallBelow count [child] [child, right] :=
    (EquationWorldPolynomial.lower_mass (mass := []) (world := right)
      (by intro value member; cases member)).cons child
  have replace : CallBelow count [child, right] [left, right] :=
    .single (.head (tail := [right]) (replacement := [child]) (by
      intro value member; cases List.mem_singleton.mp member; exact smaller))
  have step := drop.trans replace
  induction frontier with
  | nil => exact step
  | cons head tail ih => exact ih.cons head

private theorem pairRightCall {count : Nat} {child left right : World count}
    (smaller : WorldBelow count child right) (frontier : List (World count)) :
    CallBelow count (frontier ++ [child]) (frontier ++ [left, right]) := by
  have drop : CallBelow count [child] [left, child] :=
    .single (.head (replacement := []) (by intro value member; cases member))
  have replace : CallBelow count [left, child] [left, right] :=
    (EquationWorldPolynomial.lower_mass (mass := [child]) (by
      intro value member; cases List.mem_singleton.mp member; exact smaller)).cons left
  have step := drop.trans replace
  induction frontier with
  | nil => exact step
  | cons head tail ih => exact ih.cons head

private theorem sponsorChild {count : Nat} {child parent : World count}
    {frontier : List (World count)} (parentSponsored : Sponsored frontier [parent])
    (lower : WorldBelow count child parent) : Sponsored frontier [child] := by
  intro value member
  cases List.mem_singleton.mp member
  obtain ⟨sponsor, present, bound⟩ := parentSponsored _ (List.mem_singleton_self _)
  exact ⟨sponsor, present, EquationWorldClosureOrder.trans
    (r := @EquationControlMeasure.Less count) EquationControlMeasure.less_trans lower bound⟩

/-- Two real code calls are paid by the retained owner/domain R pair.
The raw conversion path uses the original substitutions, including at empty
support; no semantic uniqueness or new comparison answer is assumed. -/
theorem rebuildWorldRightAlignment
    {strata : EquationStratification env} {P : VEnv → Prop}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {headerContext : ContextDerivation headerEnv U headerSource}
    (owner : HeaderOwner field major)
    (initial : ContextDerivation sourceEnv U source)
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    (ownerFrame : OriginalRichFrame sourceEnv env U registry target
      (owner.context initial) ownerLocals ownerLeft ownerRight ownerAvailable)
    (headerFrame : OriginalRichFrame headerEnv env U registry target headerContext
      headerLocals declaredLeft declaredRight headerAvailable)
    (ownerControls : OriginalWorldControls strata sourceEnv)
    (headerControls : OriginalWorldControls strata headerEnv)
    (ownerCaptured : WorldEnvironmentProvenance strata U (ownerFrame.dependencyEnvironment ownerControls.ordered))
    (headerCaptured : WorldEnvironmentProvenance strata U (headerFrame.dependencyEnvironment headerControls.ordered))
    {ownerEnvironment headerEnvironment}
    (ownerBaseline : WorldEnvironmentProvenance strata U ownerEnvironment)
    (headerBaseline : WorldEnvironmentProvenance strata U headerEnvironment)
    (ownerCapacity : environmentCost (ownerFrame.dependencyEnvironment ownerControls.ordered) ≤ environmentCost ownerEnvironment)
    (headerCapacity : environmentCost (headerFrame.dependencyEnvironment headerControls.ordered) ≤ environmentCost headerEnvironment)
    (ownerCovered : Covered (@EquationControlMeasure.Less strata.rules.length) ownerCaptured.worlds ownerBaseline.worlds)
    (headerCovered : Covered (@EquationControlMeasure.Less strata.rules.length) headerCaptured.worlds headerBaseline.worlds)
    (frontier : List (World strata.rules.length))
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld ownerControls .expressionReindex owner.node ownerBaseline,
        originalCallWorld headerControls .expressionReindex (.ref domain) headerBaseline]))
    (sponsored : Sponsored frontier
      [originalCallWorld ownerControls .expressionReindex owner.node ownerBaseline,
       originalCallWorld headerControls .expressionReindex (.ref domain) headerBaseline])
    (ownerData : WorldUnaryFrameData P ownerControls frontier ownerFrame ownerCaptured)
    (headerData : WorldUnaryFrameData P headerControls frontier headerFrame headerCaptured)
    (domainProvenance : EndpointProvenance headerContext (.ref domain))
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ownerClosed : ownerAvailable.AtomClosed) (headerClosed : headerAvailable.AtomClosed)
    (ownerSubstitutions : Ctx.SubstEq env U target ownerLeft ownerRight owner.source)
    (headerSubstitutions : Ctx.SubstEq env U target declaredLeft declaredRight headerSource)
    (old : HeaderValueAlignment owner domain env registry target ownerLocals headerLocals
      ownerLeft ownerRight declaredLeft ownerAvailable headerAvailable (input : Profile n))
    (valueReady : ControlledStoredQuery ownerControls frontier (.certificate old.value.certificate))
    (domainReady : ControlledStoredQuery headerControls frontier (.certificate old.aligned.certificate)) :
    ∃ next : HeaderValueAlignment owner domain env registry target ownerLocals headerLocals
      ownerRight ownerRight declaredRight ownerAvailable headerAvailable input,
      next.value.support = old.value.support ∧
      Nonempty (ControlledStoredQuery ownerControls frontier (.certificate next.value.certificate)) ∧
      Nonempty (ControlledStoredQuery headerControls frontier (.certificate next.aligned.certificate)) := by
  have ownerProvenance : EndpointProvenance (owner.context initial) owner.node := by
    cases owner with
    | inl selected => exact .ofLocation selected.location initial
    | inr selected => exact .ofLocation selected.location initial
  have formationProvenance : EndpointProvenance (owner.context initial) owner.node.typeFormation.node := {
    ownerProvenance with
    location := .assignedFormation ownerProvenance.location }
  have ownerLower : WorldBelow strata.rules.length
      (originalCallWorld ownerControls .fundamental owner.node.typeFormation.node ownerBaseline)
      (originalCallWorld ownerControls .expressionReindex owner.node ownerBaseline) := by
    apply original_child
    have bound := owner.node.typeFormation_dependency_cost_le ownerControls.ordered ownerEnvironment
    simp only [richSchedule, RichPhase.code]
    omega
  have domainLower : WorldBelow strata.rules.length
      (originalCallWorld headerControls .fundamental (.ref domain) headerBaseline)
      (originalCallWorld headerControls .expressionReindex (.ref domain) headerBaseline) := by
    apply original_child
    simp only [richSchedule, RichPhase.code]
    omega
  have ownerSponsored := sponsorChild
    (fun value member => sponsored value (by
      cases List.mem_singleton.mp member; exact List.mem_cons_self)) ownerLower
  have domainSponsored := sponsorChild
    (fun value member => sponsored value (List.mem_cons_of_mem _ member)) domainLower
  obtain ⟨ownerAnswer, _, ⟨ownerReady⟩⟩ :=
    (bank _ (pairLeftCall ownerLower frontier)).computational owner.node.typeFormation.node
      formationProvenance ownerControls ownerFrame ownerCaptured ownerBaseline frontier
      ownerCapacity ownerCovered rfl ownerSponsored ownerData ownerClosed formed ownerSubstitutions
      (.code old.value.certificate) old.value.resources {
        annotation := .code valueReady.annotation
        within := by
          intro control active
          simpa only [StoredOriginalQuery.headDepth, RichObs.headDepth] using valueReady.within control active
        sponsored := valueReady.sponsored }
  obtain ⟨ownerFootprint, ownerCode, ownerCodeReady, ownerResources, _⟩ :=
    ownerAnswer.rightQuery.code_controlled henv ownerControls ownerReady old.value.certificate.formed
  have ownerRelated := ownerAnswer.related.code_of_sortable henv hscoped formed old.value.certificate.formed
  obtain ⟨domainAnswer, _, ⟨domainAnswerReady⟩⟩ :=
    (bank _ (pairRightCall domainLower frontier)).computational (.ref domain)
      domainProvenance headerControls headerFrame headerCaptured headerBaseline frontier
      headerCapacity headerCovered rfl domainSponsored headerData headerClosed formed headerSubstitutions
      (.code old.aligned.certificate) old.aligned.resources {
        annotation := .code domainReady.annotation
        within := by
          intro control active
          simpa only [StoredOriginalQuery.headDepth, RichObs.headDepth] using domainReady.within control active
        sponsored := domainReady.sponsored }
  obtain ⟨domainFootprint, domainCode, domainCodeReady, domainResources, _⟩ :=
    domainAnswer.rightQuery.code_controlled henv headerControls domainAnswerReady old.aligned.certificate.formed
  have domainRelated := domainAnswer.related.code_of_sortable henv hscoped formed old.aligned.certificate.formed
  have ownerRaw := (owner.node.typeFormation.sound.defeq.mono ownerData.ambient.below).substDF
    henv ownerSubstitutions.wf formed ownerSubstitutions
  have declaredRaw := (domain.sound.defeq.mono headerData.ambient.below).substDF
    henv headerSubstitutions.wf formed headerSubstitutions
  let next : HeaderValueAlignment owner domain env registry target ownerLocals headerLocals
      ownerRight ownerRight declaredRight ownerAvailable headerAvailable input := {
    value := {
      support := old.value.support
      footprint := ownerFootprint
      certificate := ownerCode
      resources := ownerResources
      typed := old.value.typed
      related := (old.value.related.symm henv).left_diagonal.convert henv old.value.typed ownerRelated }
    aligned := {
      footprint := domainFootprint
      certificate := domainCode
      resources := domainResources
      related := (ownerRelated.symm henv old.value.typed.wf_type).trans henv
        (old.aligned.related.trans henv domainRelated) }
    path := (TypeConversion.single ownerRaw).symm.trans (old.path.trans (.single declaredRaw)) }
  exact ⟨next, rfl, ⟨ownerCodeReady⟩, ⟨domainCodeReady⟩⟩


/-- The actual selected owner frame is shared with the recursive transcript.
This constructs the full raw entry, including the newly composed graded-query
adapter and both certificates, rather than merely a semantic alignment. -/
theorem rebuildWorldRightGroupEntry
    {strata : EquationStratification env} {P : VEnv → Prop}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {headerContext : ContextDerivation headerEnv U headerSource}
    (entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (rightOwner : OriginalRichFrame sourceEnv env U registry target
      (entry.owner.context entry.initialContext) entry.ownerLocals entry.ownerRight entry.ownerRight entry.ownerAvailable)
    (ownerTranscript : RawFrameRightRebuilt env U registry target entry.frame.raw rightOwner.raw)
    (headerFrame : OriginalRichFrame headerEnv env U registry target headerContext
      headerLocals declaredLeft declaredRight headerAvailable)
    (ownerControls : OriginalWorldControls strata sourceEnv)
    (headerControls : OriginalWorldControls strata headerEnv)
    (ownerCaptured : WorldEnvironmentProvenance strata U (entry.frame.dependencyEnvironment ownerControls.ordered))
    (headerCaptured : WorldEnvironmentProvenance strata U (headerFrame.dependencyEnvironment headerControls.ordered))
    {ownerEnvironment headerEnvironment}
    (ownerBaseline : WorldEnvironmentProvenance strata U ownerEnvironment)
    (headerBaseline : WorldEnvironmentProvenance strata U headerEnvironment)
    (ownerCapacity : environmentCost (entry.frame.dependencyEnvironment ownerControls.ordered) ≤ environmentCost ownerEnvironment)
    (headerCapacity : environmentCost (headerFrame.dependencyEnvironment headerControls.ordered) ≤ environmentCost headerEnvironment)
    (ownerCovered : Covered (@EquationControlMeasure.Less strata.rules.length) ownerCaptured.worlds ownerBaseline.worlds)
    (headerCovered : Covered (@EquationControlMeasure.Less strata.rules.length) headerCaptured.worlds headerBaseline.worlds)
    (frontier : List (World strata.rules.length))
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld ownerControls .expressionReindex entry.owner.node ownerBaseline,
        originalCallWorld headerControls .expressionReindex (.ref domain) headerBaseline]))
    (sponsored : Sponsored frontier
      [originalCallWorld ownerControls .expressionReindex entry.owner.node ownerBaseline,
       originalCallWorld headerControls .expressionReindex (.ref domain) headerBaseline])
    (ownerData : WorldUnaryFrameData P ownerControls frontier entry.frame ownerCaptured)
    (headerData : WorldUnaryFrameData P headerControls frontier headerFrame headerCaptured)
    (domainProvenance : EndpointProvenance headerContext (.ref domain))
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ownerClosed : entry.ownerAvailable.AtomClosed) (headerClosed : headerAvailable.AtomClosed)
    (headerSubstitutions : Ctx.SubstEq env U target declaredLeft declaredRight headerSource)
    (queryReady : ControlledStoredQuery ownerControls frontier (.observation entry.query))
    (valueReady : ControlledStoredQuery ownerControls frontier (.certificate entry.answer.value.certificate))
    (domainReady : ControlledStoredQuery headerControls frontier (.certificate entry.answer.aligned.certificate)) :
    ∃ next : RawRichGroupEntry (field := field) (major := major) domain env registry target
      headerLocals declaredRight headerAvailable ownerInitial rawCapture rightValue rightValue entry.rank entry.input,
      Nonempty (RawEntryRightRebuilt env U registry target entry.toRaw next) ∧
      Nonempty (ControlledStoredQuery ownerControls frontier (.observation next.query)) ∧
      Nonempty (ControlledStoredQuery ownerControls frontier (.certificate next.answer.value.certificate)) ∧
      Nonempty (ControlledStoredQuery headerControls frontier (.certificate next.answer.aligned.certificate)) := by
  obtain ⟨alignment, supportEq, ⟨valueReady'⟩, ⟨domainReady'⟩⟩ :=
    rebuildWorldRightAlignment entry.owner entry.initialContext domain entry.frame headerFrame
      ownerControls headerControls ownerCaptured headerCaptured ownerBaseline headerBaseline
      ownerCapacity headerCapacity ownerCovered headerCovered frontier bank sponsored ownerData headerData
      domainProvenance henv hscoped formed ownerClosed headerClosed entry.substitutions headerSubstitutions
      entry.answer valueReady domainReady
  have ownerProvenance : EndpointProvenance (entry.owner.context entry.initialContext) entry.owner.node := by
    cases h : entry.owner with
    | inl selected => exact .ofLocation selected.location entry.initialContext
    | inr selected => exact .ofLocation selected.location entry.initialContext
  have lower : WorldBelow strata.rules.length
      (originalCallWorld ownerControls .fundamental entry.owner.node ownerBaseline)
      (originalCallWorld ownerControls .expressionReindex entry.owner.node ownerBaseline) := by
    apply original_child
    simp only [richSchedule, RichPhase.code]
    omega
  have funded := pairLeftCall (right := originalCallWorld headerControls .expressionReindex (.ref domain) headerBaseline)
    lower frontier
  have ownerSponsored := sponsorChild
    (fun value member => sponsored value (by cases List.mem_singleton.mp member; exact List.mem_cons_self)) lower
  obtain ⟨answer, _, ⟨answerReady⟩⟩ := (bank _ funded).computational entry.owner.node ownerProvenance
    ownerControls entry.frame ownerCaptured ownerBaseline frontier ownerCapacity ownerCovered rfl ownerSponsored
    ownerData ownerClosed formed entry.substitutions entry.query entry.queryAvailable queryReady
  let query := answer.rightQuery.adaptRequest henv hscoped formed entry.queryBound entry.queryAdapter
  have rightSubstitutions := (entry.substitutions.symm henv formed).left
  let next : RawRichGroupEntry (field := field) (major := major) domain env registry target
      headerLocals declaredRight headerAvailable ownerInitial rawCapture rightValue rightValue entry.rank entry.input :=
    .mk entry.owner entry.ownerLocals entry.ownerRight entry.ownerRight entry.ownerAvailable
      entry.initialContext rightOwner.raw rightSubstitutions entry.depth entry.sourcePrefix entry.source_eq
      entry.depth_eq entry.expression_eq entry.right_eq entry.right_eq query.rank query.raw query.bound
      query.adapter query.footprint query.observation query.resources alignment
  refine ⟨next, ⟨?_⟩, ⟨answerReady⟩, ⟨valueReady'⟩, ⟨domainReady'⟩⟩
  exact .mk entry.owner entry.initialContext ownerTranscript entry.substitutions rightSubstitutions
    entry.depth entry.sourcePrefix entry.source_eq entry.depth_eq entry.expression_eq entry.left_eq entry.right_eq
    entry.queryBound entry.queryAdapter entry.query entry.queryAvailable entry.answer
    query.bound query.adapter query.observation query.resources alignment

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
