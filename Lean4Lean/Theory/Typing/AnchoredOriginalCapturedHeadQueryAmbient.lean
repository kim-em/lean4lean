import Lean4Lean.Theory.Typing.AnchoredOriginalCapturedArgumentSupply
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientCaptureGeneration

/-! Select a captured head together with ambient inclusion of its actual
retained owner frame. The witness is constructed during selection, not
recovered from an unrelated existential query. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private needAdapter from Lean4Lean.Theory.Typing.AnchoredOriginalCapturedQuerySelection
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
set_option Elab.async false

structure AmbientCapturedHeadQuery
    (base : OriginalCaptureBase env U registry target) (commonCaps : CaptureCaps)
    (common : List VExpr) (commonLeft commonRight : Subst) (expression : VExpr)
    (need : Need) (capacity : Nat)
    extends CapturedHeadQuery base commonCaps common commonLeft commonRight expression need capacity where
  generated : AmbientCaptureGenerated base caps left right display.graph realization.frame.raw

def AmbientCapturedHeadQuery.enlarge
    (head : AmbientCapturedHeadQuery base commonCaps common commonLeft commonRight expression need capacity)
    (bound : capacity ≤ nextCapacity) :
    AmbientCapturedHeadQuery base commonCaps common commonLeft commonRight expression need nextCapacity :=
  ⟨head.toCapturedHeadQuery.enlarge bound, head.generated⟩

theorem AmbientCapturedHeadQuery.frameAmbient
    {base : OriginalCaptureBase env U registry target}
    (head : AmbientCapturedHeadQuery base commonCaps common commonLeft commonRight expression need capacity) :
    head.realization.frame.Ambient := head.generated.ambient.2

theorem AmbientCapturedHeadQuery.graphAmbient
    {base : OriginalCaptureBase env U registry target}
    (head : AmbientCapturedHeadQuery base commonCaps common commonLeft commonRight expression need capacity) :
    head.display.graph.Ambient env := head.generated.ambient.1

theorem AmbientCapturedHeadQuery.sourceBelow
    {base : OriginalCaptureBase env U registry target}
    (head : AmbientCapturedHeadQuery base commonCaps common commonLeft commonRight expression need capacity) :
    head.display.sourceEnv ≤ env := head.frameAmbient.below

/-- Realization packages exactly the same raw frame and preserves its
hereditary inclusion evidence under the substitution equalities. -/
theorem AmbientCaptureGenerated.realize
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (generated : AmbientCaptureGenerated base commonCaps commonLeft commonRight graph frame.raw)
    (substitutions : Ctx.SubstEq env U target σ τ source) :
    ∃ result : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available,
      AmbientCaptureGenerated base commonCaps commonLeft commonRight graph result.frame.raw ∧
      (∀ ordered : sourceEnv.Ordered, result.frame.dependencyEnvironment ordered= frame.dependencyEnvironment ordered) := by
  obtain ⟨left, right⟩ := generated.capped.generated.realizations
  subst σ
  subst τ
  exact ⟨⟨frame, substitutions⟩, generated, fun _ => rfl⟩

private theorem groupedHeadQueryAmbient
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
    (owners : ∀ entry member, AmbientCaptureGenerated base (scopes entry member).caps (scopes entry member).left
      (scopes entry member).right (scopes entry member).graph entry.frame.raw)
    (need : Need) (member : need ∈ entries.needs) :
    Nonempty (AmbientCapturedHeadQuery base commonCaps common commonLeft commonRight (rawCapture.subst ownerRaw) need
      (environmentCost ((tail.group domain ordered initial entries).dependencyEnvironment headerOrdered))) := by
  obtain ⟨entry, present, requested⟩ := List.mem_flatMap.mp member
  let scope := scopes entry present
  have generated := owners entry present
  obtain ⟨realized, ownerGenerated, sameEnvironment⟩ := generated.realize entry.frame entry.substitutions
  have needBound := (captureNeeds_covered entry.input need requested).1
  have needCovered := (captureNeeds_covered entry.input need requested).2
  refine ⟨{
    depth := entry.depth, scope := scope.scope, insertion := scope.insertion
    left := scope.left, right := scope.right, leftTail := scope.leftTail, rightTail := scope.rightTail
    caps := scope.caps, capsTail := scope.capsTail
    assigned := entry.owner.assigned.subst scope.raw, display := entry.scopeDisplay scope
    ordered := ordered, locals := entry.ownerLocals, available := entry.ownerAvailable
    realization := realized, capped := ownerGenerated.capped
    rank := entry.queryRank, bound := Nat.le_trans needBound entry.queryBound,
    profile := entry.queryInput, footprint := entry.footprint
    query := ?_, resources := entry.queryAvailable
    adapter := ?_, cost := ?_, generated := ownerGenerated }⟩
  · change RichObs sourceEnv env U registry target entry.owner.node entry.ownerLocals
      (scope.raw.comp scope.left) entry.queryInput entry.footprint
    rw [← generated.capped.generated.realizations.1]
    exact entry.query
  · exact needAdapter entry.queryBound entry.queryAdapter needBound needCovered
  · rw [sameEnvironment]
    exact entries.ownerQuery_cost_le_environment ordered headerOrdered tail present

private theorem ownHeadQueryAmbient
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (ordered : sourceEnv.Ordered)
    (tail : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (capped : AmbientCaptureGenerated base commonCaps commonLeft commonRight graph tail.raw)
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
    Nonempty (AmbientCapturedHeadQuery base commonCaps common commonLeft commonRight (a.subst raw) need
      (environmentCost ((tail.capture domain initial argument location lineage query queryAvailable certificate resources
        typed arguments needs bounded covered).dependencyEnvironment ordered))) := by
  obtain ⟨realized, ownerGenerated, environment⟩ := capped.realize tail substitutions
  let display : OriginalNestedDisplay U common ((a.subst raw).lift' (.skipN .refl 0)) (A.subst raw) := {
    sourceEnv := sourceEnv, source := source, sourceExpression := a, sourceType := A
    context := context, node := argument, provenance := ⟨_, _, _, root, initial, location, lineage.symm⟩
    raw := raw, graph := graph, expression_eq := by simp only [Lift.skipN, lift'_refl]
    type_eq := rfl }
  refine ⟨{
    depth := 0, scope := common, insertion := .refl
    left := commonLeft, right := commonRight, leftTail := rfl, rightTail := rfl
    caps := commonCaps, capsTail := rfl, assigned := A.subst raw, display := display, ordered := ordered
    locals := locals, available := available, realization := realized, capped := ownerGenerated.capped
    rank := k, bound := Nat.le_trans (bounded need member) queryBound
    profile := rawInput, footprint := argumentFootprint, query := ?_, resources := queryAvailable
    adapter := needAdapter queryBound queryAdapter (bounded need member) (covered need member)
    cost := ?_, generated := ownerGenerated }⟩
  · change RichObs sourceEnv env U registry target argument locals (raw.comp commonLeft) rawInput argumentFootprint
    rw [← capped.capped.generated.realizations.1]
    exact query
  · rw [environment]
    exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_max_left _ _)

private def capturedAmbientInvariant
    (base : OriginalCaptureBase env U registry target) (commonCaps : CaptureCaps)
    (commonLeft commonRight : Subst)
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available) : Prop :=
  match graph with
  | .capture .. => frame.Valid → Ctx.SubstEq env U target σ τ source →
      ∀ ordered : sourceEnv.Ordered, ∀ need ∈ available 0,
      Nonempty (AmbientCapturedHeadQuery base commonCaps common commonLeft commonRight (raw 0) need
        (environmentCost (frame.dependencyEnvironment ordered)))
  | _ => True

private theorem capturedAmbientInvariant_merge
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {left : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ leftAvailable}
    {right : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ rightAvailable}
    (first : capturedAmbientInvariant base commonCaps commonLeft commonRight graph left)
    (second : capturedAmbientInvariant base commonCaps commonLeft commonRight graph right) :
    capturedAmbientInvariant base commonCaps commonLeft commonRight graph (.merge left right) := by
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

private theorem AmbientCaptureGenerated.headQueryInvariant
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : AmbientCaptureGenerated base commonCaps commonLeft commonRight graph frame) :
    capturedAmbientInvariant base commonCaps commonLeft commonRight graph frame := by
  induction generated with
  | merge _ _ first second => exact capturedAmbientInvariant_merge first second
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
    exact ownHeadQueryAmbient ordered ⟨_, valid⟩ generated tailSubstitutions domain initial argument location lineage query
      queryAvailable queryBound queryAdapter certificate resources typed arguments needs bounded covered need member
  | historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedGenerated domainProvenance prior history historyWellFormed historyGenerated tailBound entries scopes owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient _ _ _ _ =>
    intro valid substitutions ordered need member
    simp only [RawOriginalRichFrame.Valid] at valid
    change Nonempty (AmbientCapturedHeadQuery _ _ _ _ _ (VExpr.subst _ _) _ _)
    rw [← displayed]
    obtain ⟨answer⟩ := groupedHeadQueryAmbient ⟨_, valid.1⟩ ownerOrdered ordered entries scopes owners need member
    exact ⟨answer.enlarge (by
      change _ ≤ environmentCost (_ ++ _)
      rw [merge_environmentCost_append]
      exact Nat.le_max_right _ _)⟩

/-- Every demanded capture need has a concrete bounded source query. This
covers merged own captures and heterogeneous groups at arbitrary scope. -/
theorem AmbientCaptureGenerated.headQuery
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation headerEnv U headerSource}
    {graph : OriginalCaptureMap (common := common) context raw}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {ownerContext : ContextDerivation ownerEnv U ownerSource}
    {ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw}
    {owner : EndpointState ownerEnv U ownerSource argument assigned}
    {provenance : EndpointProvenance ownerContext owner}
    {frame : RawOriginalRichFrame headerEnv env U registry target (.cons context domain) locals σ τ available}
    (generated : AmbientCaptureGenerated base commonCaps commonLeft commonRight
      (.capture graph domain ownerGraph owner provenance) frame)
    (valid : frame.Valid) (substitutions : Ctx.SubstEq env U target σ τ (A :: headerSource))
    (ordered : headerEnv.Ordered) (need : Need) (member : need ∈ available 0) :
    Nonempty (AmbientCapturedHeadQuery base commonCaps common commonLeft commonRight (argument.subst ownerRaw) need
      (environmentCost (frame.dependencyEnvironment ordered))) :=
  generated.headQueryInvariant valid substitutions ordered need member


/-- Every member carries the positive generation proof of its selected
original owner, including dormant history and its actual scope graph. -/
def CapturedArgumentQueries.AmbientGenerated
    {base : OriginalCaptureBase env U registry target}
    (queries : CapturedArgumentQueries base commonCaps common commonLeft commonRight expression capacity needs) : Prop :=
  match queries with
  | .nil => True
  | .cons head tail =>
      AmbientCaptureGenerated base head.caps head.left head.right head.display.graph head.realization.frame.raw ∧
      tail.AmbientGenerated

/-- Construct the complete finite argument ledger from the actual demanded
needs. All ambient witnesses certify those same returned queries. -/
theorem AmbientCaptureGenerated.argumentQueries
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation headerEnv U headerSource}
    {graph : OriginalCaptureMap (common := common) context raw}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {ownerContext : ContextDerivation ownerEnv U ownerSource}
    {ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw}
    {owner : EndpointState ownerEnv U ownerSource argument assigned}
    {provenance : EndpointProvenance ownerContext owner}
    {frame : RawOriginalRichFrame headerEnv env U registry target (.cons context domain) locals σ τ available}
    (generated : AmbientCaptureGenerated base commonCaps commonLeft commonRight
      (.capture graph domain ownerGraph owner provenance) frame)
    (valid : frame.Valid) (substitutions : Ctx.SubstEq env U target σ τ (A :: headerSource))
    (ordered : headerEnv.Ordered) (needs : List Need)
    (resources : ∀ need ∈ needs, need ∈ available 0)
    (budget : environmentCost (frame.dependencyEnvironment ordered) ≤ capacity) :
    ∃ queries : CapturedArgumentQueries base commonCaps common commonLeft commonRight
      (argument.subst ownerRaw) capacity needs, queries.AmbientGenerated := by
  induction needs with
  | nil => exact ⟨.nil, trivial⟩
  | cons need needs ih =>
    obtain ⟨head⟩ := generated.headQuery valid substitutions ordered need (resources need List.mem_cons_self)
    obtain ⟨tail, tailAmbient⟩ := ih (fun need member => resources need (List.mem_cons_of_mem _ member))
    exact ⟨.cons (head.enlarge budget).toCapturedHeadQuery tail, head.generated, tailAmbient⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
