import Lean4Lean.Theory.Typing.AnchoredOriginalCapturedQuerySelection
import Lean4Lean.Theory.Typing.AnchoredOriginalOwnCaptureReindex
import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationCaptureReplayBudget

/-! A used capture slot selects a finite original source query, including its
actual common-binder scope and adapter. Selection does not run semantics. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private needAdapter from Lean4Lean.Theory.Typing.AnchoredOriginalCapturedQuerySelection
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

private theorem groupedHeadQuery
    {base : OriginalCaptureBase env U registry target}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {context : ContextDerivation headerEnv U headerSource}
    (tail : OriginalRichFrame headerEnv env U registry target context locals σ τ available)
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ available initial rawCapture leftValue rightValue)
    (scopes : ∀ entry ∈ entries, CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps entry.depth
      (entry.owner.context entry.initialContext))
    (owners : ∀ entry member, CappedCaptureGenerated base (scopes entry member).caps (scopes entry member).left
      (scopes entry member).right (scopes entry member).graph entry.frame.raw)
    (need : Need) (member : need ∈ entries.needs) :
    Nonempty (CapturedHeadQuery base commonCaps common commonLeft commonRight (rawCapture.subst ownerRaw) need
      (environmentCost ((tail.group domain ordered initial entries).dependencyEnvironment headerOrdered))) := by
  obtain ⟨entry, present, requested⟩ := List.mem_flatMap.mp member
  let scope := scopes entry present
  have generated := owners entry present
  obtain ⟨realized, capped, sameEnvironment⟩ := generated.realize entry.frame entry.substitutions
  have needBound := (captureNeeds_covered entry.input need requested).1
  have needCovered := (captureNeeds_covered entry.input need requested).2
  refine ⟨{
    depth := entry.depth, scope := scope.scope, insertion := scope.insertion
    left := scope.left, right := scope.right, leftTail := scope.leftTail, rightTail := scope.rightTail
    caps := scope.caps, capsTail := scope.capsTail
    assigned := entry.owner.assigned.subst scope.raw, display := entry.scopeDisplay scope
    ordered := ordered, locals := entry.ownerLocals, available := entry.ownerAvailable
    realization := realized, capped := capped
    rank := entry.queryRank, bound := Nat.le_trans needBound entry.queryBound,
    profile := entry.queryInput, footprint := entry.footprint
    query := ?_, resources := entry.queryAvailable
    adapter := ?_, cost := ?_ }⟩
  · change RichObs sourceEnv env U registry target entry.owner.node entry.ownerLocals
      (scope.raw.comp scope.left) entry.queryInput entry.footprint
    rw [← generated.generated.realizations.1]
    exact entry.query
  · exact needAdapter entry.queryBound entry.queryAdapter needBound needCovered
  · rw [sameEnvironment]
    exact entries.ownerQuery_cost_le_environment ordered headerOrdered tail present

private theorem ownHeadQuery
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (ordered : sourceEnv.Ordered)
    (tail : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (capped : CappedCaptureGenerated base commonCaps commonLeft commonRight graph tail.raw)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (initial : ContextDerivation sourceEnv U rootSource)
    (argument : EndpointState sourceEnv U source a A)
    (location : Located root argument)
    (lineage : location.contextDerivation initial = context)
    (query : RichObs sourceEnv env U registry target argument locals σ (rawInput : Profile k) argumentFootprint)
    (queryAvailable : argumentFootprint.Available available)
    (queryBound : n ≤ k)
    (queryAdapter : GeneralNormalProfileAdapter env U registry target rawInput (raiseProfile k queryBound (input : Profile n)))
    (certificate : RichCert sourceEnv env U registry target (.ref domain) locals σ true (support : Profile n) footprint)
    (resources : footprint.Available available) (typed : input.HasType support)
    (arguments : Related env U registry target (a.subst σ) (a.subst τ) (A.subst σ) input support)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms)
    (need : Need) (member : need ∈ needs) :
    Nonempty (CapturedHeadQuery base commonCaps common commonLeft commonRight (a.subst raw) need
      (environmentCost ((tail.capture domain initial argument location lineage query queryAvailable certificate resources
        typed arguments needs bounded covered).dependencyEnvironment ordered))) := by
  obtain ⟨realized, generated, environment⟩ := capped.realize tail substitutions
  let display : OriginalNestedDisplay U common ((a.subst raw).lift' (.skipN .refl 0)) (A.subst raw) := {
    sourceEnv := sourceEnv, source := source, sourceExpression := a, sourceType := A
    context := context, node := argument, provenance := ⟨_, _, _, root, initial, location, lineage.symm⟩
    raw := raw, graph := graph, expression_eq := by simp only [Lift.skipN, lift'_refl]
    type_eq := rfl }
  refine ⟨{
    depth := 0, scope := common, insertion := .refl
    left := commonLeft, right := commonRight, leftTail := rfl, rightTail := rfl
    caps := commonCaps, capsTail := rfl, assigned := A.subst raw, display := display, ordered := ordered
    locals := locals, available := available, realization := realized, capped := generated
    rank := k, bound := Nat.le_trans (bounded need member) queryBound
    profile := rawInput, footprint := argumentFootprint, query := ?_, resources := queryAvailable
    adapter := needAdapter queryBound queryAdapter (bounded need member) (covered need member)
    cost := ?_ }⟩
  · change RichObs sourceEnv env U registry target argument locals (raw.comp commonLeft) rawInput argumentFootprint
    rw [← capped.generated.realizations.1]
    exact query
  · rw [environment]
    exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_max_left _ _)

private def capturedHeadInvariant
    (base : OriginalCaptureBase env U registry target) (commonCaps : CaptureCaps)
    (commonLeft commonRight : Subst)
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available) : Prop :=
  match graph with
  | .capture .. => frame.Valid → Ctx.SubstEq env U target σ τ source →
      ∀ ordered : sourceEnv.Ordered, ∀ need ∈ available 0,
      Nonempty (CapturedHeadQuery base commonCaps common commonLeft commonRight (raw 0) need
        (environmentCost (frame.dependencyEnvironment ordered)))
  | _ => True

private theorem capturedHeadInvariant_merge
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {left : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ leftAvailable}
    {right : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ rightAvailable}
    (first : capturedHeadInvariant base commonCaps commonLeft commonRight graph left)
    (second : capturedHeadInvariant base commonCaps commonLeft commonRight graph right) :
    capturedHeadInvariant base commonCaps commonLeft commonRight graph (.merge left right) := by
  cases graph <;> try trivial
  intro valid substitutions ordered need member
  simp only [RawOriginalRichFrame.Valid] at valid
  rcases List.mem_append.mp member with member | member
  · obtain ⟨answer⟩ := first valid.1 substitutions ordered need member
    exact ⟨answer.enlarge (by
      change _ ≤ environmentCost (left.dependencyEnvironment ordered ++ right.dependencyEnvironment ordered)
      rw [merge_environmentCost_append]
      exact Nat.le_max_left _ _)⟩
  · obtain ⟨answer⟩ := second valid.2 substitutions ordered need member
    exact ⟨answer.enlarge (by
      change _ ≤ environmentCost (left.dependencyEnvironment ordered ++ right.dependencyEnvironment ordered)
      rw [merge_environmentCost_append]
      exact Nat.le_max_right _ _)⟩

private theorem CappedCaptureGenerated.headQueryInvariant
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph frame) :
    capturedHeadInvariant base commonCaps commonLeft commonRight graph frame := by
  induction generated with
  | merge _ _ first second => exact capturedHeadInvariant_merge first second
  | identity | empty | tail | bind | weaken => trivial
  | reserveCapture _ closures ih =>
    intro valid substitutions ordered need member
    simp only [RawOriginalRichFrame.Valid] at valid
    obtain ⟨answer⟩ := ih valid substitutions ordered need member
    exact ⟨answer.enlarge (by
      change _ ≤ environmentCost (closures ++ _)
      rw [merge_environmentCost_append]
      exact Nat.le_max_right _ _)⟩
  | reserveBind => trivial
  | capture generated domain initial argument location lineage query queryAvailable queryBound queryAdapter
      certificate resources typed arguments needs bounded covered _ =>
    intro valid substitutions ordered need member
    simp only [RawOriginalRichFrame.Valid] at valid
    have tailSubstitutions := by cases substitutions with | cons tail _ _ => exact tail
    exact ownHeadQuery ordered ⟨_, valid⟩ generated tailSubstitutions domain initial argument location lineage query
      queryAvailable queryBound queryAdapter certificate resources typed arguments needs bounded covered need member
  | scopedGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered ownerInitial
      seed seedScope seedGenerated entries scopes owners _ _ _ =>
    intro valid substitutions ordered need member
    simp only [RawOriginalRichFrame.Valid] at valid
    change Nonempty (CapturedHeadQuery _ _ _ _ _ (VExpr.subst _ _) _ _)
    rw [← displayed]
    exact groupedHeadQuery ⟨_, valid.1⟩ ownerOrdered ordered entries scopes owners need member
  | historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedGenerated domainProvenance prior history historyWellFormed historyGenerated tailBound entries scopes owners _ _ _ _ =>
    intro valid substitutions ordered need member
    simp only [RawOriginalRichFrame.Valid] at valid
    change Nonempty (CapturedHeadQuery _ _ _ _ _ (VExpr.subst _ _) _ _)
    rw [← displayed]
    obtain ⟨answer⟩ := groupedHeadQuery ⟨_, valid.1⟩ ownerOrdered ordered entries scopes owners need member
    exact ⟨answer.enlarge (by
      change _ ≤ environmentCost (_ ++ _)
      rw [merge_environmentCost_append]
      exact Nat.le_max_right _ _)⟩
  | group generated domain ownerGenerated nominalGraph nominal provenance displayed ownerOrdered ownerInitial
      seed seedExtension entries owners _ _ =>
    intro valid substitutions ordered need member
    simp only [RawOriginalRichFrame.Valid] at valid
    obtain ⟨entry, present, requested⟩ := List.mem_flatMap.mp member
    obtain ⟨extension⟩ := owners entry present
    obtain ⟨scopeCommon, scopeRaw, scopeLeft, scopeRight, scopeCaps, scopeGraph, scopeGenerated,
      rawEq, insertion, leftTail, rightTail, capsTail⟩ := extension.generateCappedScope ownerGenerated
    have depthEq := (entry.extensionRealizations extension).1
    rw [depthEq] at rawEq insertion leftTail rightTail capsTail
    let scope : CappedOwnerScope _ _ _ _ _ _ _ := {
      scope := scopeCommon, raw := scopeRaw, left := scopeLeft, right := scopeRight, graph := scopeGraph
      raw_eq := rawEq, insertion := insertion, leftTail := leftTail, rightTail := rightTail
      caps := scopeCaps, capsTail := capsTail }
    obtain ⟨realized, cap, environment⟩ := scopeGenerated.realize entry.frame entry.substitutions
    have needBound := (captureNeeds_covered entry.input need requested).1
    have needCovered := (captureNeeds_covered entry.input need requested).2
    change Nonempty (CapturedHeadQuery _ _ _ _ _ (VExpr.subst _ _) _ _)
    rw [← displayed]
    refine ⟨{
      depth := entry.depth, scope := scopeCommon, insertion := insertion
      left := scopeLeft, right := scopeRight, leftTail := leftTail, rightTail := rightTail
      caps := scopeCaps, capsTail := capsTail, assigned := entry.owner.assigned.subst scopeRaw
      display := entry.scopeDisplay scope, ordered := ownerOrdered, locals := entry.ownerLocals
      available := entry.ownerAvailable, realization := realized, capped := cap
      rank := entry.queryRank, bound := Nat.le_trans needBound entry.queryBound,
      profile := entry.queryInput, footprint := entry.footprint
      query := ?_, resources := entry.queryAvailable
      adapter := needAdapter entry.queryBound entry.queryAdapter needBound needCovered
      cost := ?_ }⟩
    · change RichObs _ _ _ _ _ entry.owner.node _ (scopeRaw.comp scopeLeft) _ _
      rw [← scopeGenerated.generated.realizations.1]
      exact entry.query
    · rw [environment]
      exact entries.ownerQuery_cost_le_environment ownerOrdered ordered ⟨_, valid.1⟩ present

/-- Every demanded capture need has a concrete bounded source query. This
covers merged own captures and heterogeneous groups at arbitrary scope. -/
theorem CappedCaptureGenerated.headQuery
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation headerEnv U headerSource}
    {graph : OriginalCaptureMap (common := common) context raw}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {ownerContext : ContextDerivation ownerEnv U ownerSource}
    {ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw}
    {owner : EndpointState ownerEnv U ownerSource argument assigned}
    {provenance : EndpointProvenance ownerContext owner}
    {frame : RawOriginalRichFrame headerEnv env U registry target (.cons context domain) locals σ τ available}
    (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight
      (.capture graph domain ownerGraph owner provenance) frame)
    (valid : frame.Valid) (substitutions : Ctx.SubstEq env U target σ τ (A :: headerSource))
    (ordered : headerEnv.Ordered) (need : Need) (member : need ∈ available 0) :
    Nonempty (CapturedHeadQuery base commonCaps common commonLeft commonRight (argument.subst ownerRaw) need
      (environmentCost (frame.dependencyEnvironment ordered))) :=
  generated.headQueryInvariant valid substitutions ordered need member

/-- Replay uses the exact selected owner and source frame. Its original
scope is removed only after the actual bounded R call has returned. -/
theorem CapturedHeadQuery.replay
    {assigned : VExpr} {available : Valuation} {locals : List Nat}
    {base : OriginalCaptureBase env U registry target}
    (head : CapturedHeadQuery base commonCaps common commonLeft commonRight expression need capacity)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (baseClosed : base.available.AtomClosed)
    (destination : OriginalNestedDisplay U common expression assigned)
    (ordered : destination.sourceEnv.Ordered)
    (frame : OriginalCaptureRealization destination.graph env registry target locals commonLeft commonRight available)
    (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight destination.graph frame.frame.raw)
    (closed : available.AtomClosed)
    (scheduled : richSchedule .expressionReindex
      (capacity + (Closure.close (destination.node.dependencyOrigin ordered) (frame.frame.dependencyEnvironment ordered)).cost) < limit)
    (reindex : GeneratedObservationCall base head.caps head.display (destination.weaken head.insertion)
      head.left head.right head.ordered ordered limit) :
    Nonempty (BoundedGeneratedQueryReply base commonCaps destination commonLeft commonRight need.profile
      (environmentCost (frame.frame.dependencyEnvironment ordered))) := by
  obtain ⟨sourceAvailable, source, sourceCapped, included, sourceClosed, sourceEnvironment⟩ :=
    head.realization.closeResources head.capped baseClosed
  obtain ⟨next, nextCapped, sameEnvironment⟩ := frame.weakenCapped generated head.insertion
    head.leftTail head.rightTail head.capsTail
  have bound : richSchedule .expressionReindex
      ((Closure.close (head.display.node.dependencyOrigin head.ordered) (source.frame.dependencyEnvironment head.ordered)).cost +
       (Closure.close (destination.node.dependencyOrigin ordered) (next.frame.dependencyEnvironment ordered)).cost) < limit := by
    rw [sourceEnvironment, sameEnvironment]
    exact Nat.lt_of_le_of_lt (by
      change 3 * (_ + _) + 2 ≤ 3 * (_ + _) + 2
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 3 (Nat.add_le_add_right head.cost _)) 2) scheduled
  obtain ⟨answer⟩ := reindex source sourceCapped sourceClosed next nextCapped closed bound head.query
    (fun i n h => included i n (head.resources i n h))
  rw [sameEnvironment ordered] at answer
  exact (answer.mapQuery (answer.answer.reply.query.adaptRequest henv hscoped formed head.bound head.adapter)).unweaken
    head.insertion head.leftTail head.rightTail head.capsTail

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
