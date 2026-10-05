import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientParameterPrefixCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientApplyPiSeedHistory

/-! An actual family argument supplies the independent empty seed for an
auxiliary declaration context. Its computed Pi-domain history is followed by
the retained cell route and a paid declaration-scope reframe. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail OriginalEndpointFactor.Dependency
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option Elab.async false
open private nestedDisplay_heq ambientRouteRightTransport
  from Lean4Lean.Theory.Typing.AnchoredOriginalAmbientApplyPiSeedHistory

private theorem routeFinalTransport
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final)
    (generated : route.AmbientGenerated base caps) (same : final = next) :
    ∃ output : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial next,
      output.AmbientGenerated base caps ∧ output.reserve = route.reserve := by
  subst next
  exact ⟨route, generated, rfl⟩

/-- The declaration is phantom in pending data: changing it preserves every
original owner, frame, source query and depth witness. -/
def PendingRichCapture.redeclare
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {headerAvailable : Valuation}
    (pending : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (nextDomain : EndpointRef nextEnv U nextSource nextA (.sort nextLevel))
    (nextLocals : List Nat) (nextLeft : Subst) (nextAvailable : Valuation) :
    PendingRichCapture (field := field) (major := major) nextDomain env registry target
      nextLocals nextLeft nextAvailable ownerInitial rawCapture leftValue rightValue where
  owner := pending.owner
  ownerLocals := pending.ownerLocals
  ownerLeft := pending.ownerLeft
  ownerRight := pending.ownerRight
  ownerAvailable := pending.ownerAvailable
  ownerClosed := pending.ownerClosed
  initialContext := pending.initialContext
  frame := pending.frame
  substitutions := pending.substitutions
  frame_environment_le := pending.frame_environment_le
  depth := pending.depth
  sourcePrefix := pending.sourcePrefix
  source_eq := pending.source_eq
  depth_eq := pending.depth_eq
  expression_eq := pending.expression_eq
  left_eq := pending.left_eq
  right_eq := pending.right_eq
  rank := pending.rank
  input := pending.input
  footprint := pending.footprint
  query := pending.query
  queryAvailable := pending.queryAvailable

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
  (sourceGraph : OriginalCaptureMap (common := common) (location.contextDerivation initial) sourceRaw)
  {right : OriginalPiTypeRouteSide U common}
  (history : OriginalApplyPiHistory env registry target commonLeft commonRight
    (originalApplicationTypeRouteSide initial domain body function argument result hu hv location sourceGraph) right)
  (noBinders : location.binderPrefix = [])
  (sourceBound : ∀ ordered : sourceEnv.Ordered,
    environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost (location.dependencyEnvironment ordered ownerInitial))
  {nextContext : ContextDerivation nextEnv U nextSource}
  (nextGraph : OriginalCaptureMap (common := common) nextContext nextRaw)
  (nextDomain : EndpointRef nextEnv U nextSource nextA (.sort nextLevel))
  (nextProvenance : EndpointProvenance nextContext (.ref nextDomain))
  (nextOrdered : nextEnv.Ordered)
  {base : OriginalCaptureBase env U registry target}
  (nextFrame : AmbientParameterReplyFrame base commonCaps nextGraph commonLeft commonRight)

local notation "sourceSide" => originalApplicationTypeRouteSide initial domain body function argument result hu hv location sourceGraph

noncomputable def OriginalApplyPiHistory.emptyArgumentSeedAt :
    PendingRichCapture (field := field) (major := major) nextDomain env registry target
      nextFrame.locals (nextRaw.comp commonLeft) nextFrame.available ownerInitial
      a (a.subst (sourceRaw.comp commonLeft)) (a.subst (sourceRaw.comp commonRight)) :=
  (history.argumentSeed (field := field) initial domain body function argument result hu hv location sourceGraph
    noBinders sourceBound (.legacy (.legacy .empty) : RichObs sourceEnv env U registry target argument
      history.sourceFrame.locals (sourceRaw.comp commonLeft) (Profile.empty : Profile 0) [])
    (fun _ _ member => nomatch member)).redeclare nextDomain nextFrame.locals (nextRaw.comp commonLeft) nextFrame.available

noncomputable def OriginalApplyPiHistory.emptyArgumentScopeAt :
    CappedOwnerScope common sourceRaw commonLeft commonRight commonCaps
      (history.emptyArgumentSeedAt (field := field) initial domain body function argument result hu hv location sourceGraph
        noBinders sourceBound nextGraph nextDomain nextFrame).depth
      ((history.emptyArgumentSeedAt (field := field) initial domain body function argument result hu hv location sourceGraph
        noBinders sourceBound nextGraph nextDomain nextFrame).owner.context initial) := {
  toOriginalOwnerScope := history.argumentSeedScope (field := field) initial domain body function argument result hu hv
    location sourceGraph noBinders sourceBound (.legacy (.legacy .empty) : RichObs sourceEnv env U registry target argument
      history.sourceFrame.locals (sourceRaw.comp commonLeft) (Profile.empty : Profile 0) [])
    (fun _ _ member => nomatch member)
  caps := commonCaps
  capsTail := rfl }

/-- The new declaration history is generated entirely from the actual
family application and a finite original cell path. It carries no semantic
alignment answer and preserves the original argument as its fixed seed. -/
theorem OriginalApplyPiHistory.argumentCellHistoryAmbient
    (generated : history.AmbientGenerated base commonCaps)
    (cells : RawGeneratedTypeRoute env registry target commonLeft commonRight right.domainDisplay
      (nextGraph.parameterCellDisplay nextDomain nextProvenance) history.final
      (nextFrame.realization.frame.dependencyEnvironment nextOrdered))
    (cellsGenerated : cells.AmbientGenerated base commonCaps) :
    ∃ packet : OriginalSeedTypeHistory
        (history.emptyArgumentSeedAt (field := field) initial domain body function argument result hu hv location sourceGraph
          noBinders sourceBound nextGraph nextDomain nextFrame)
        (history.emptyArgumentScopeAt (field := field) initial domain body function argument result hu hv location sourceGraph
          noBinders sourceBound nextGraph nextDomain nextFrame).toOriginalOwnerScope
        nextGraph nextProvenance nextFrame.realization history.leftOrdered nextOrdered,
      packet.route.AmbientGenerated base commonCaps ∧
      packet.route.reserve = (history.argumentDomainRoute.reserve ++ cells.reserve) ++
        [Closure.bundle (.close (nextDomain.dependencyOrigin nextOrdered)
            (nextFrame.realization.frame.dependencyEnvironment nextOrdered))
          (.close (nextDomain.dependencyOrigin nextOrdered)
            (nextFrame.realization.frame.dependencyEnvironment nextOrdered))] := by
  let seed := history.emptyArgumentSeedAt (field := field) initial domain body function argument result hu hv location sourceGraph
    noBinders sourceBound nextGraph nextDomain nextFrame
  let scope := history.emptyArgumentScopeAt (field := field) initial domain body function argument result hu hv location sourceGraph
    noBinders sourceBound nextGraph nextDomain nextFrame
  obtain ⟨destinationFrame, destinationGenerated, environmentEq⟩ :=
    nextFrame.realization.weakenAmbient nextFrame.generation (Ctx.Lift'.refl (Γ := common))
      (nextLeft := commonLeft) (nextRight := commonRight) (nextCaps := commonCaps) rfl rfl rfl
  let destination : OriginalNestedDisplay U common (nextA.subst nextRaw) (.sort nextLevel) := {
    sourceEnv := nextEnv, source := nextSource, sourceExpression := nextA, sourceType := .sort nextLevel
    context := nextContext, node := .ref nextDomain, provenance := nextProvenance
    raw := nextRaw.lift_r .refl, graph := .weaken nextGraph .refl
    expression_eq := by rw [← lift'_subst, lift'_refl]
    type_eq := rfl }
  let framed : OriginalTypeRouteFrame env registry target destination.graph commonLeft commonRight :=
    ⟨nextFrame.locals, nextFrame.available, destinationFrame, nextFrame.closed⟩
  let final := RawGeneratedTypeRoute.same (nextGraph.parameterCellDisplay nextDomain nextProvenance) destination
    nextOrdered nextOrdered (nextFrame.realization.frame.dependencyEnvironment nextOrdered) framed
  let route := (history.argumentDomainRoute.trans cells).trans final
  have domainGenerated : history.argumentDomainRoute.AmbientGenerated base commonCaps := by
    refine ⟨?_, ?_, ?_⟩
    · rw [OriginalApplyPiHistory.argumentDomainRoute, RawGeneratedTypeRoute.WellFormed.eq_def]
      constructor
      · rw [RawGeneratedTypeRoute.WellFormed.eq_def]; trivial
      · rw [RawGeneratedTypeRoute.WellFormed.eq_def]
        exact generated.whole.wellFormed
    · rw [OriginalApplyPiHistory.argumentDomainRoute, RawGeneratedTypeRoute.Ambient.eq_def]
      constructor
      · rw [RawGeneratedTypeRoute.Ambient.eq_def]
        exact ⟨history.leftBelow, history.leftBelow⟩
      · rw [RawGeneratedTypeRoute.Ambient.eq_def]
        exact generated.whole.ambient
    · intro boxed member
      simp only [OriginalApplyPiHistory.argumentDomainRoute, RawGeneratedTypeRoute.frames,
        List.mem_append, List.mem_singleton] at member
      rcases member with rfl | member
      · exact generated.source
      · exact generated.whole.frames boxed member
  have finalGenerated : final.AmbientGenerated base commonCaps := by
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [final]
      rw [RawGeneratedTypeRoute.WellFormed.eq_def]; trivial
    · dsimp only [final]
      rw [RawGeneratedTypeRoute.Ambient.eq_def]
      exact ⟨nextFrame.generation.ambient.2.below, nextFrame.generation.ambient.2.below⟩
    · intro boxed member
      dsimp only [final] at member
      rw [RawGeneratedTypeRoute.frames.eq_def, List.mem_singleton] at member
      subst boxed
      exact destinationGenerated
  have allGenerated := (domainGenerated.trans cellsGenerated).trans finalGenerated
  have frameEq := environmentEq nextOrdered
  have reserveEq : route.reserve = (history.argumentDomainRoute.reserve ++ cells.reserve) ++
      [Closure.bundle (.close (nextDomain.dependencyOrigin nextOrdered)
          (nextFrame.realization.frame.dependencyEnvironment nextOrdered))
        (.close (nextDomain.dependencyOrigin nextOrdered)
          (nextFrame.realization.frame.dependencyEnvironment nextOrdered))] := by
    simp only [route, final, RawGeneratedTypeRoute.reserve, destination, framed,
      OriginalCaptureMap.parameterCellDisplay, EndpointState.dependencyOrigin,
      frameEq]
  obtain ⟨nextRoute, ambient, sameReserve⟩ := routeFinalTransport route allGenerated frameEq
  have destinationEq : HEq destination (scope.toOriginalOwnerScope.declaredTypeDisplay nextGraph nextProvenance) := by
    dsimp only [destination, scope, OriginalApplyPiHistory.emptyArgumentScopeAt,
      OriginalApplyPiHistory.argumentSeedScope, OriginalOwnerScope.declaredTypeDisplay,
      seed, OriginalApplyPiHistory.emptyArgumentSeedAt, PendingRichCapture.redeclare,
      OriginalApplyPiHistory.argumentSeed, Lift.skipN]
    exact nestedDisplay_heq _ _ _ _ _ _ _
  obtain ⟨finalRoute, nextGenerated, finalReserve⟩ :=
    ambientRouteRightTransport nextRoute ambient lift'_refl.symm destinationEq
  exact ⟨⟨finalRoute⟩, nextGenerated, finalReserve.trans (sameReserve.trans reserveEq)⟩


include noBinders sourceBound in
/-- The actual argument, its fixed empty seed and the target prefix are all
computed here. Only the original finite cell route and the lower call bank
are inputs; no completed owner or declared-domain alignment is assumed. -/
theorem OriginalApplyPiHistory.captureCellAmbient
    (generated : history.AmbientGenerated base commonCaps)
    (cells : RawGeneratedTypeRoute env registry target commonLeft commonRight right.domainDisplay
      (nextGraph.parameterCellDisplay nextDomain nextProvenance) history.final
      (nextFrame.realization.frame.dependencyEnvironment nextOrdered))
    (cellsGenerated : cells.AmbientGenerated base commonCaps)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (bank : OriginalLowerCallBank env U registry limit)
    (paid : richSchedule .expressionReindex (environmentCost
      ((history.argumentDomainRoute.reserve ++ cells.reserve) ++
        [Closure.bundle (.close (nextDomain.dependencyOrigin nextOrdered)
            (nextFrame.realization.frame.dependencyEnvironment nextOrdered))
          (.close (nextDomain.dependencyOrigin nextOrdered)
            (nextFrame.realization.frame.dependencyEnvironment nextOrdered))])) < limit) :
    ∃ captured : AmbientParameterReplyFrame base commonCaps
        (.capture nextGraph nextDomain sourceGraph argument (.ofLocation (.appArgument location) initial))
        commonLeft commonRight,
      environmentCost (captured.realization.frame.dependencyEnvironment nextOrdered) =
        environmentCost (groupCaptureHistoryReserve field major nextDomain history.leftOrdered nextOrdered ownerInitial
          (nextFrame.realization.frame.dependencyEnvironment nextOrdered)
          ((history.argumentDomainRoute.reserve ++ cells.reserve) ++
            [Closure.bundle (.close (nextDomain.dependencyOrigin nextOrdered)
                (nextFrame.realization.frame.dependencyEnvironment nextOrdered))
              (.close (nextDomain.dependencyOrigin nextOrdered)
                (nextFrame.realization.frame.dependencyEnvironment nextOrdered))])) := by
  let seed := history.emptyArgumentSeedAt (field := field) initial domain body function argument result hu hv location sourceGraph
    noBinders sourceBound nextGraph nextDomain nextFrame
  let scope := history.emptyArgumentScopeAt (field := field) initial domain body function argument result hu hv location sourceGraph
    noBinders sourceBound nextGraph nextDomain nextFrame
  obtain ⟨packet, packetGenerated, reserveEq⟩ := history.argumentCellHistoryAmbient (field := field)
    initial domain body function argument result hu hv location sourceGraph noBinders sourceBound
    nextGraph nextDomain nextProvenance nextOrdered nextFrame generated cells cellsGenerated
  have scheduled : packet.route.schedule < limit := by
    apply Nat.lt_of_le_of_lt packet.route.schedule_le
    rwa [reserveEq]
  obtain ⟨captured, equal⟩ := packet.captureEmptyAmbient history.leftOrdered nextOrdered sourceGraph sourceGraph argument
    (.ofLocation (.appArgument location) initial) rfl seed scope generated.source
    nextProvenance nextFrame.realization packetGenerated henv hscoped formed
    generated.source.ambient.1 generated.source.ambient.1 nextFrame.generation.ambient.2 bank scheduled
  exact ⟨captured, by simpa only [reserveEq] using equal⟩


include noBinders sourceBound in
/-- The seed path and final scope edge are charged at this same slot.
The actual original application is the owner occurrence for the source leg. -/
theorem OriginalApplyPiHistory.captureCellAmbient_counted
    (seedHeader requestedHeader : ParameterRouteHeader sourceEnv U)
    (generated : history.AmbientGenerated base commonCaps)
    (cells : RawGeneratedTypeRoute env registry target commonLeft commonRight right.domainDisplay
      (nextGraph.parameterCellDisplay nextDomain nextProvenance) history.final
      (nextFrame.realization.frame.dependencyEnvironment nextOrdered))
    (cellsGenerated : cells.AmbientGenerated base commonCaps)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (bank : OriginalLowerCallBank env U registry limit)
    (sources : ParameterRouteSources sourceEnv U :=
      ⟨history.leftOrdered, source, fieldExpression, fieldType, majorExpression, majorType,
        field, major, seedHeader, requestedHeader⟩)
    (sourcesEq : sources =
      ⟨history.leftOrdered, source, fieldExpression, fieldType, majorExpression, majorType,
        field, major, seedHeader, requestedHeader⟩ := by rfl)
    (wholeCharged : history.whole.Charged sources ownerInitial count)
    (cellsCharged : cells.Charged sources ownerInitial count)
    (occurrence : ParameterRouteOccurrence sources nextOrdered (.ref nextDomain))
    (previous : ParameterRouteLedger sources ownerInitial count
      (nextFrame.realization.frame.dependencyEnvironment nextOrdered))
    (paid : richSchedule .expressionReindex
      (2 * sources.weight * parameterRouteCapacity sources count ownerInitial) < limit) :
    ∃ captured : AmbientParameterReplyFrame base commonCaps
        (.capture nextGraph nextDomain sourceGraph argument (.ofLocation (.appArgument location) initial))
        commonLeft commonRight,
      Nonempty (ParameterRouteLedger sources ownerInitial (count+1)
        (captured.realization.frame.dependencyEnvironment nextOrdered)) := by
  subst sources
  let sources : ParameterRouteSources sourceEnv U :=
    ⟨history.leftOrdered, source, fieldExpression, fieldType, majorExpression, majorType,
      field, major, seedHeader, requestedHeader⟩
  have argumentCharged := history.argumentDomainRoute_charged sources ownerInitial wholeCharged
    (.major location) (sourceBound history.leftOrdered)
  have charges := ((history.argumentDomainRoute.chargedReserve argumentCharged).append
    (cells.chargedReserve cellsCharged)).append
      (.cons (.reindex occurrence occurrence previous previous) .nil)
  have budget : richSchedule .expressionReindex (environmentCost
      ((history.argumentDomainRoute.reserve ++ cells.reserve) ++
        [Closure.bundle (.close (nextDomain.dependencyOrigin nextOrdered)
            (nextFrame.realization.frame.dependencyEnvironment nextOrdered))
          (.close (nextDomain.dependencyOrigin nextOrdered)
            (nextFrame.realization.frame.dependencyEnvironment nextOrdered))])) < limit := by
    apply Nat.lt_of_le_of_lt _ paid
    change 3 * _ + 2 ≤ 3 * _ + 2
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 3 charges.bound) 2
  obtain ⟨captured, equal⟩ := history.captureCellAmbient (field := field) initial domain body function argument result
    hu hv location sourceGraph noBinders sourceBound nextGraph nextDomain nextProvenance nextOrdered nextFrame
    generated cells cellsGenerated henv hscoped formed bank budget
  exact ⟨captured, ⟨.bounded (occurrence.historyGroupLedger sources previous charges) _ (Nat.le_of_eq equal)⟩⟩

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
