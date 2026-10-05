import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiSeedHistory
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientApplyPiHistoryGeneration
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientCapturedArgumentSupply

/-! The original argument seed and its exact finite history retain positive
hereditary generation through the declaration-scope reframe. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

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

private theorem ambientRouteRightTransport
    {first : OriginalNestedDisplay U common firstExpression firstType}
    {last : OriginalNestedDisplay U common lastExpression lastType}
    {next : OriginalNestedDisplay U common nextExpression lastType}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight first last initial final)
    (generated : route.AmbientGenerated base commonCaps)
    (expressionEq : lastExpression = nextExpression) (endpointEq : HEq last next) :
    ∃ nextRoute : RawGeneratedTypeRoute env registry target commonLeft commonRight first next initial final,
      nextRoute.AmbientGenerated base commonCaps ∧ nextRoute.reserve = route.reserve := by
  cases expressionEq
  cases eq_of_heq endpointEq
  exact ⟨route, generated, rfl⟩

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

/-- All three legs are finite original history: the argument's actual type
formation, the previous Pi-domain history, and the separately charged zero-scope
declaration reframe. Both independent baseline frames are retained. -/
theorem OriginalApplyPiHistory.argumentSeedHistoryAmbient
    {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
    (noBinders : location.binderPrefix = [])
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (query : RichObs sourceEnv env U registry target argument history.sourceFrame.locals
      (raw.comp commonLeft) (input : Profile n) footprint)
    (resources : footprint.Available history.sourceFrame.available)
    (sourceGenerated : AmbientCaptureGenerated base commonCaps commonLeft commonRight graph
      history.sourceFrame.realization.frame.raw)
    (headerGenerated : AmbientCaptureGenerated base commonCaps commonLeft commonRight right.graph
      history.headerFrame.realization.frame.raw)
    (wholeGenerated : history.whole.AmbientGenerated base commonCaps) :
    ∃ result : OriginalSeedTypeHistory
        (history.argumentSeed (field := field) initial domain body function argument result hu hv location graph
          noBinders sourceBound query resources)
        (history.argumentSeedScope initial domain body function argument result hu hv location graph
          noBinders sourceBound query resources)
        right.graph (history.headerDomainProvenance initial domain body function argument result hu hv location graph)
        history.headerFrame.realization history.leftOrdered history.rightOrdered,
      result.route.AmbientGenerated base commonCaps ∧ result.route.reserve = history.argumentSeedReserve := by
  let seed := history.argumentSeed (field := field) initial domain body function argument result hu hv location graph
    noBinders sourceBound query resources
  let scope := history.argumentSeedScope (field := field) initial domain body function argument result hu hv location graph
    noBinders sourceBound query resources
  let provenance := history.headerDomainProvenance initial domain body function argument result hu hv location graph
  obtain ⟨header, headerCapped, environmentEq⟩ := history.headerFrame.realization.weakenAmbient headerGenerated
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
  have generated : combined.AmbientGenerated base commonCaps := by
    refine ⟨?_, ?_, ?_⟩
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
    · dsimp only [combined]
      rw [RawGeneratedTypeRoute.Ambient.eq_def]
      constructor
      · rw [OriginalApplyPiHistory.argumentDomainRoute, RawGeneratedTypeRoute.Ambient.eq_def]
        constructor
        · rw [RawGeneratedTypeRoute.Ambient.eq_def]
          exact ⟨sourceGenerated.ambient.2.below, sourceGenerated.ambient.2.below⟩
        · rw [RawGeneratedTypeRoute.Ambient.eq_def]
          exact wholeGenerated.ambient
      · dsimp only [last]
        rw [RawGeneratedTypeRoute.Ambient.eq_def]
        exact ⟨headerGenerated.ambient.2.below, headerGenerated.ambient.2.below⟩
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
      route.AmbientGenerated base commonCaps ∧ route.reserve = history.argumentSeedReserve := by
    rw [seedSource, ← finalEq]
    exact ⟨combined, generated, combinedReserve⟩
  obtain ⟨route, generated, reserveEq⟩ := output
  have endpointEq : HEq destination (scope.declaredTypeDisplay right.graph provenance) := by
    dsimp only [destination, scope, OriginalApplyPiHistory.argumentSeedScope,
      OriginalOwnerScope.declaredTypeDisplay, seed, OriginalApplyPiHistory.argumentSeed, Lift.skipN]
    exact nestedDisplay_heq _ _ _ _ _ _ _
  obtain ⟨nextRoute, nextGenerated, sameReserve⟩ := ambientRouteRightTransport route generated lift'_refl.symm endpointEq
  exact ⟨⟨nextRoute⟩, nextGenerated, sameReserve.trans reserveEq⟩

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
