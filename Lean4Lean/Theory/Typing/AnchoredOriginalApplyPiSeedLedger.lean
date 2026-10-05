import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiHistoryLedger
import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiSeedHistory
import Lean4Lean.Theory.Typing.AnchoredOriginalGroupBaselineBudget

/-! The complete seed history and the actual empty-group envelope consume
one parameter slot. Both original source roots remain prepaid independently
of the selected argument queries. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail OriginalEndpointFactor.Dependency
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable def _root_.Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.Dependency.ParameterRouteSources.rootOwners
    (sources : ParameterRouteSources sourceEnv U) : List sources.Owner :=
  [.inl ⟨_, _, _, .ref sources.field, .here⟩,
   .inr ⟨_, _, _, .ref sources.major, .here⟩]

variable {left : OriginalApplicationTypeRouteSide U common}
  {right : OriginalPiTypeRouteSide U common}

/-- The scope reframe is a real final route edge and is charged at the exact
original header domain, using the same retained preceding ledger. -/
noncomputable def OriginalApplyPiHistory.argumentSeedReserve_charged
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight left right)
    (sources : ParameterRouteSources left.sourceEnv U) (initial : List Closure)
    (whole : history.whole.Charged sources initial count)
    (application : ParameterRouteOwnerOccurrence sources left.node)
    (sourceBound : environmentCost
        (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered) ≤
      environmentCost (application.environment initial))
    (domain : ParameterRouteOccurrence sources history.rightOrdered (.ref history.rightDomain))
    (prefixLedger : ParameterRouteLedger sources initial count history.final) :
    ParameterRouteCharges sources initial count history.argumentSeedReserve := by
  unfold argumentSeedReserve
  rw [history.rightDomainEq]
  exact (history.argumentDomainRoute.chargedReserve
    (history.argumentDomainRoute_charged sources initial whole application sourceBound)).append
    (.cons (.reindex domain domain prefixLedger prefixLedger) .nil)

/-- This envelope uses the field and major ROOTS, including for an empty
query group. It is the actual public group representation's capacity. -/
noncomputable def OriginalApplyPiHistory.seedCaptureLedger
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight left right)
    (sources : ParameterRouteSources left.sourceEnv U) (initial : List Closure)
    (whole : history.whole.Charged sources initial count)
    (application : ParameterRouteOwnerOccurrence sources left.node)
    (sourceBound : environmentCost
        (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered) ≤
      environmentCost (application.environment initial))
    (domain : ParameterRouteOccurrence sources history.rightOrdered (.ref history.rightDomain))
    (prefixLedger : ParameterRouteLedger sources initial count history.final) :
    ParameterRouteLedger sources initial (count + 1)
      (history.argumentSeedReserve ++ groupCaptureBaseline sources.field sources.major history.rightDomain
        sources.ordered history.rightOrdered initial history.final) := by
  let paid := history.argumentSeedReserve_charged sources initial whole application sourceBound domain prefixLedger
  let next := ParameterRouteLedger.capture domain.captureDomain sources.rootOwners prefixLedger paid
  apply ParameterRouteLedger.bounded next
  simpa only [actualParameterRouteStepEnvironment, groupCaptureBaseline,
    ParameterRouteSources.rootOwners, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, groupedOwnerClosure, Dependency.LocatedOrigin.closure, Located.dependencyEnvironment,
    EndpointState.dependencyOrigin] using
    domain.actualStep_bound sources.rootOwners history.final history.argumentSeedReserve initial

/-- The semantic producer may return a different, smaller preceding frame
and any finite adapted query group. Its concrete reserved output still has
the exact successor ledger; no equality with the baseline frame is assumed. -/
noncomputable def OriginalApplyPiHistory.capturedFrameLedger
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight left right)
    (sources : ParameterRouteSources left.sourceEnv U) (initial : List Closure)
    (whole : history.whole.Charged sources initial count)
    (application : ParameterRouteOwnerOccurrence sources left.node)
    (sourceBound : environmentCost
        (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered) ≤
      environmentCost (application.environment initial))
    (domain : ParameterRouteOccurrence sources history.rightOrdered (.ref history.rightDomain))
    (prefixLedger : ParameterRouteLedger sources initial count history.final)
    (tail : OriginalRichFrame right.sourceEnv env U registry target
      (right.location.contextDerivation right.initial) locals σ τ available)
    (entries : RichGroupedCapture (field := sources.field) (major := sources.major) history.rightDomain
      env registry target locals σ available initial rawCapture leftValue rightValue)
    (tailBound : environmentCost (tail.dependencyEnvironment history.rightOrdered) ≤ environmentCost history.final) :
    ParameterRouteLedger sources initial (count + 1)
      (((tail.group history.rightDomain sources.ordered initial entries).reserve
        (groupCaptureHistoryReserve sources.field sources.major history.rightDomain sources.ordered history.rightOrdered
          initial history.final history.argumentSeedReserve)).dependencyEnvironment history.rightOrdered) :=
  .bounded (history.seedCaptureLedger sources initial whole application sourceBound domain prefixLedger) _
    (Nat.le_of_eq (tail.historyGroup_environmentCost sources.ordered history.rightOrdered entries
      history.final history.argumentSeedReserve tailBound))

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
