import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiHistory
import Lean4Lean.Theory.Typing.AnchoredOriginalRawTypeRouteGeneration
import Lean4Lean.Theory.Typing.AnchoredOriginalCappedCaptureRealization
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedSeedData

/-! A family-prefix application supplies the actual pending argument owner
and its next declared-domain history. This constructor is deliberately for
an application at the major's own source context, with no intervening binder.
General applications under binders use the separate own-capture producer. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

private theorem nestedDisplay_heq
    (context : ContextDerivation sourceEnv U source)
    (node : EndpointState sourceEnv U source expression assigned)
    (provenance : EndpointProvenance context node)
    (graph : OriginalCaptureMap (common := common) context raw)
    (first : firstExpression = expression.subst raw)
    (second : secondExpression = expression.subst raw)
    (typed : commonType = assigned.subst raw) :
    HEq
      (OriginalNestedDisplay.mk sourceEnv source expression assigned context node provenance raw graph first typed)
      (OriginalNestedDisplay.mk sourceEnv source expression assigned context node provenance raw graph second typed) := by
  cases first
  cases second
  rfl

private theorem routeRightTransport
    {first : OriginalNestedDisplay U common firstExpression firstType}
    {last : OriginalNestedDisplay U common lastExpression lastType}
    {next : OriginalNestedDisplay U common nextExpression lastType}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight first last initial final)
    (generated : route.Generated base commonCaps)
    (expressionEq : lastExpression = nextExpression) (endpointEq : HEq last next) :
    ∃ nextRoute : RawGeneratedTypeRoute env registry target commonLeft commonRight first next initial final,
      nextRoute.Generated base commonCaps ∧ nextRoute.reserve = route.reserve := by
  cases expressionEq
  cases eq_of_heq endpointEq
  exact ⟨route, generated, rfl⟩

/-- The complete stored seed history includes its exact declaration-scope
reframe. Its reserve is independent of the incidental seed query. -/
noncomputable def OriginalApplyPiHistory.argumentSeedReserve
    {left : OriginalApplicationTypeRouteSide U common}
    {right : OriginalPiTypeRouteSide U common}
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight left right) : List Closure :=
  history.argumentDomainRoute.reserve ++
    [Closure.bundle (.close (right.domain.dependencyOrigin history.rightOrdered) history.final)
      (.close (history.rightDomain.dependencyOrigin history.rightOrdered) history.final)]

section
variable
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  {major : EndpointRef sourceEnv U source majorExpression majorType}
  (initial : ContextDerivation sourceEnv U source)
  (domain : EndpointRef sourceEnv U source A (.sort u))
  (body : EndpointState sourceEnv U (A :: source) B (.sort v))
  (function : EndpointState sourceEnv U source f (.forallE A B))
  (argument : EndpointState sourceEnv U source a A)
  (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
  (hu : u.WF U) (hv : v.WF U)
  (location : Located major (.app hu hv (.ref domain) body function argument result))
  (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)


variable {right : OriginalPiTypeRouteSide U common}
  (history : OriginalApplyPiHistory env registry target commonLeft commonRight (originalApplicationTypeRouteSide initial domain body function argument result hu hv location graph) right)

/-- The stored query belongs to the actual family argument occurrence. Its
source frame is the independent caller baseline retained by the history. -/
noncomputable def OriginalApplyPiHistory.argumentSeed
    (noBinders : location.binderPrefix = [])
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (query : RichObs sourceEnv env U registry target argument history.sourceFrame.locals
      (raw.comp commonLeft) (input : Profile n) footprint)
    (resources : footprint.Available history.sourceFrame.available) :
    PendingRichCapture (field := field) (major := major) history.rightDomain env registry target
      history.headerFrame.locals (right.raw.comp commonLeft) history.headerFrame.available ownerInitial
      a (a.subst (raw.comp commonLeft)) (a.subst (raw.comp commonRight)) where
  owner := .inr ⟨source, a, A, argument, .appArgument location⟩
  ownerLocals := history.sourceFrame.locals
  ownerLeft := raw.comp commonLeft
  ownerRight := raw.comp commonRight
  ownerAvailable := history.sourceFrame.available
  ownerClosed := history.sourceFrame.closed
  initialContext := initial
  frame := history.sourceFrame.realization.frame
  substitutions := history.sourceFrame.realization.substitutions
  frame_environment_le := sourceBound
  depth := 0
  sourcePrefix := []
  source_eq := rfl
  depth_eq := rfl
  expression_eq := by simp [HeaderOwner.expression]
  left_eq := rfl
  right_eq := rfl
  rank := n
  input := input
  footprint := footprint
  query := query
  queryAvailable := resources

noncomputable def OriginalApplyPiHistory.argumentSeedScope
    (noBinders : location.binderPrefix = [])
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (query : RichObs sourceEnv env U registry target argument history.sourceFrame.locals
      (raw.comp commonLeft) (input : Profile n) footprint)
    (resources : footprint.Available history.sourceFrame.available) :
    OriginalOwnerScope common raw commonLeft commonRight
      (history.argumentSeed (field := field) initial domain body function argument result hu hv location graph noBinders sourceBound query resources).depth
      ((history.argumentSeed (field := field) initial domain body function argument result hu hv location graph noBinders sourceBound query resources).owner.context initial) where
  scope := common
  raw := raw
  left := commonLeft
  right := commonRight
  graph := graph
  insertion := .refl
  raw_eq := by simp [OriginalApplyPiHistory.argumentSeed, Subst.liftN]
  leftTail := rfl
  rightTail := rfl

noncomputable def OriginalApplyPiHistory.headerDomainProvenance :
    EndpointProvenance (right.location.contextDerivation right.initial) (.ref history.rightDomain) := by
  simpa only [Located.contextDerivation, history.rightDomainEq] using
    EndpointProvenance.ofLocation (.piDomain right.location) right.initial

/-- The source endpoint of the stored history is exactly the pending
owner's original assigned formation, including its occurrence path. -/
theorem OriginalApplyPiHistory.argumentSeed_source
    (noBinders : location.binderPrefix = [])
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (query : RichObs sourceEnv env U registry target argument history.sourceFrame.locals
      (raw.comp commonLeft) (input : Profile n) footprint)
    (resources : footprint.Available history.sourceFrame.available) :
    (history.argumentSeed (field := field) initial domain body function argument result hu hv location graph
      noBinders sourceBound query resources).assignedOwnerScopeDisplay
        (history.argumentSeedScope initial domain body function argument result hu hv location graph
          noBinders sourceBound query resources) = ((originalApplicationTypeRouteSide initial domain body function argument result hu hv location graph)).argumentDisplay.formationDisplay := rfl

/-- All three legs are finite original history: the argument's actual type
formation, the previous Pi-domain history, and the separately charged zero-scope
declaration reframe. Both independent baseline frames are retained. -/
theorem OriginalApplyPiHistory.argumentSeedHistory
    {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
    (noBinders : location.binderPrefix = [])
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (query : RichObs sourceEnv env U registry target argument history.sourceFrame.locals
      (raw.comp commonLeft) (input : Profile n) footprint)
    (resources : footprint.Available history.sourceFrame.available)
    (sourceGenerated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph
      history.sourceFrame.realization.frame.raw)
    (headerGenerated : CappedCaptureGenerated base commonCaps commonLeft commonRight right.graph
      history.headerFrame.realization.frame.raw)
    (wholeGenerated : history.whole.Generated base commonCaps) :
    ∃ result : OriginalSeedTypeHistory
        (history.argumentSeed (field := field) initial domain body function argument result hu hv location graph
          noBinders sourceBound query resources)
        (history.argumentSeedScope initial domain body function argument result hu hv location graph
          noBinders sourceBound query resources)
        right.graph (history.headerDomainProvenance initial domain body function argument result hu hv location graph)
        history.headerFrame.realization history.leftOrdered history.rightOrdered,
      result.route.Generated base commonCaps ∧ result.route.reserve = history.argumentSeedReserve := by
  let seed := history.argumentSeed (field := field) initial domain body function argument result hu hv location graph
    noBinders sourceBound query resources
  let scope := history.argumentSeedScope (field := field) initial domain body function argument result hu hv location graph
    noBinders sourceBound query resources
  let provenance := history.headerDomainProvenance initial domain body function argument result hu hv location graph
  obtain ⟨header, headerCapped, environmentEq⟩ := history.headerFrame.realization.weakenCapped headerGenerated
    (Ctx.Lift'.refl (Γ := common)) (nextLeft := commonLeft) (nextRight := commonRight)
    (nextCaps := commonCaps) rfl rfl rfl
  let destination : OriginalNestedDisplay U common (right.A.subst right.raw) (.sort right.u) := {
    sourceEnv := right.sourceEnv, source := right.source, sourceExpression := right.A, sourceType := .sort right.u
    context := right.location.contextDerivation right.initial, node := .ref history.rightDomain
    provenance := provenance, raw := right.raw.lift_r .refl
    graph := .weaken right.graph .refl
    expression_eq := by rw [← lift'_subst, lift'_refl]
    type_eq := rfl }
  let destinationFrame : OriginalTypeRouteFrame env registry target destination.graph commonLeft commonRight :=
    ⟨history.headerFrame.locals, history.headerFrame.available, header, history.headerFrame.closed⟩
  let last := RawGeneratedTypeRoute.same right.domainDisplay destination history.rightOrdered history.rightOrdered
    history.final destinationFrame
  let combined := history.argumentDomainRoute.trans last
  have generated : combined.Generated base commonCaps := by
    refine ⟨?_, ?_⟩
    · dsimp only [combined]
      rw [RawGeneratedTypeRoute.WellFormed.eq_def]
      constructor
      · rw [OriginalApplyPiHistory.argumentDomainRoute, RawGeneratedTypeRoute.WellFormed.eq_def]
        constructor
        · rw [RawGeneratedTypeRoute.WellFormed.eq_def]; trivial
        · rw [RawGeneratedTypeRoute.WellFormed.eq_def]
          exact wholeGenerated.wellFormed
      · dsimp only [last]
        rw [RawGeneratedTypeRoute.WellFormed.eq_def]; trivial
    · intro boxed member
      simp only [combined, last, OriginalApplyPiHistory.argumentDomainRoute, RawGeneratedTypeRoute.frames,
        List.mem_append, List.mem_singleton] at member
      rcases member with (rfl | member) | rfl
      · exact sourceGenerated
      · exact wholeGenerated.frames boxed member
      · exact headerCapped
  have seedSource : seed.assignedOwnerScopeDisplay scope =
      (originalApplicationTypeRouteSide initial domain body function argument result hu hv location graph).argumentDisplay.formationDisplay := rfl
  have finalEq : header.frame.dependencyEnvironment history.rightOrdered = history.final := environmentEq history.rightOrdered
  have combinedReserve : combined.reserve = history.argumentSeedReserve := by
    simp only [combined, last, RawGeneratedTypeRoute.reserve, destinationFrame, destination,
      OriginalPiTypeRouteSide.domainDisplay, OriginalNestedDisplay.ofOccurrence, OriginalApplyPiHistory.argumentSeedReserve,
      EndpointState.dependencyOrigin, finalEq]
  have output : ∃ route : RawGeneratedTypeRoute env registry target commonLeft commonRight
      (seed.assignedOwnerScopeDisplay scope) destination
      (seed.frame.dependencyEnvironment history.leftOrdered) history.final,
      route.Generated base commonCaps ∧ route.reserve = history.argumentSeedReserve := by
    rw [seedSource, ← finalEq]
    exact ⟨combined, generated, combinedReserve⟩
  obtain ⟨route, generated, reserveEq⟩ := output
  have endpointEq : HEq destination (scope.declaredTypeDisplay right.graph provenance) := by
    dsimp only [destination, scope, OriginalApplyPiHistory.argumentSeedScope,
      OriginalOwnerScope.declaredTypeDisplay, seed, OriginalApplyPiHistory.argumentSeed, Lift.skipN]
    exact nestedDisplay_heq _ _ _ _ _ _ _
  obtain ⟨nextRoute, nextGenerated, sameReserve⟩ := routeRightTransport route generated lift'_refl.symm endpointEq
  exact ⟨⟨nextRoute⟩, nextGenerated, sameReserve.trans reserveEq⟩

end
/-- Requerying changes resources, never the retained original assigned
formation or its displayed source syntax. The history keeps its old baseline. -/
theorem PendingRichCapture.requery_assignedOwnerScopeDisplay
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (seed : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (graph : OriginalCaptureMap (common := common) (seed.owner.context seed.initialContext) raw)
    (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph seed.frame.raw)
    (ordered : sourceEnv.Ordered)
    (answer : BoundedGeneratedQueryReply base commonCaps (seed.seedDisplay graph)
      commonLeft commonRight (requested : Profile n)
      (environmentCost (seed.frame.dependencyEnvironment ordered)))
    (scope : OriginalOwnerScope outerCommon ownerRaw outerLeft outerRight seed.depth
      (seed.owner.context seed.initialContext)) :
    (seed.requery graph generated ordered answer).assignedOwnerScopeDisplay scope =
      seed.assignedOwnerScopeDisplay scope := rfl

/-- Updating the declaration resource table also leaves the independent
owner baseline and its original assigned formation untouched. -/
theorem PendingRichCapture.reheader_assignedOwnerScopeDisplay
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (seed : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (scope : OriginalOwnerScope common ownerRaw commonLeft commonRight seed.depth
      (seed.owner.context seed.initialContext))
    (nextLocals : List Nat) (nextLeft : Subst) (nextAvailable : Valuation) :
    (seed.reheader nextLocals nextLeft nextAvailable).assignedOwnerScopeDisplay scope =
      seed.assignedOwnerScopeDisplay scope := rfl

theorem PendingRichCapture.requery_baseline_bound
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (seed : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (graph : OriginalCaptureMap (common := common) (seed.owner.context seed.initialContext) raw)
    (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph seed.frame.raw)
    (ordered : sourceEnv.Ordered)
    (answer : BoundedGeneratedQueryReply base commonCaps (seed.seedDisplay graph)
      commonLeft commonRight (requested : Profile n)
      (environmentCost (seed.frame.dependencyEnvironment ordered))) :
    ∀ nextOrdered : sourceEnv.Ordered,
      environmentCost ((seed.requery graph generated ordered answer).frame.dependencyEnvironment nextOrdered) ≤
      environmentCost (seed.frame.dependencyEnvironment ordered) := answer.bounded

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
