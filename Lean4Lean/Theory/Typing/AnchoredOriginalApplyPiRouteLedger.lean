import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiRoute
import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiSeedLedger

/-! One actual family application advances the declared-prefix ledger.
The source occurrence is the retained application under the actual major,
and the output carries its entire seed history and fixed group envelope. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail OriginalEndpointFactor.Dependency
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace OriginalApplyPiHistory
section
variable {env : VEnv} {registry : CanonicalHead.Registry} {target : List VExpr}
  {commonLeft commonRight : Subst}
variable
  (sources : ParameterRouteSources sourceEnv U)
  (initial : ContextDerivation sourceEnv U sources.source)
  (domain : EndpointRef sourceEnv U sources.source A (.sort u))
  (body : EndpointState sourceEnv U (A :: sources.source) B (.sort v))
  (function : EndpointState sourceEnv U sources.source f (.forallE A B))
  (argument : EndpointState sourceEnv U sources.source a A)
  (result : EndpointState sourceEnv U sources.source (B.inst a) (.sort v))
  (hu : u.WF U) (hv : v.WF U)
  (location : Located sources.major (.app hu hv (.ref domain) body function argument result))
  (sourceGraph : OriginalCaptureMap (common := common) (location.contextDerivation initial) sourceRaw)
  {headerRoot : EndpointRef headerEnv U headerRootSource headerExpression headerType}
  (headerInitial : ContextDerivation headerEnv U headerRootSource)
  (headerDomain : EndpointRef headerEnv U headerSource C (.sort cu))
  (headerBody : EndpointState headerEnv U (C :: headerSource) D (.sort dv))
  (hcu : cu.WF U) (hdv : dv.WF U)
  (headerLocation : Located headerRoot (.pi hcu hdv (.ref headerDomain) headerBody))
  (headerGraph : OriginalCaptureMap (common := common) (headerLocation.contextDerivation headerInitial) headerRaw)

local notation "sourceSide" => originalApplicationTypeRouteSide initial domain body function argument result hu hv location sourceGraph
local notation "headerSide" => originalNativePiRouteSide headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph

/-- The recursive child and the two actual parent occurrences pay exactly
this applyPi node's computed reserve. -/
noncomputable def applyRoute_charged
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight sourceSide headerSide)
    (noBinders : location.binderPrefix = []) (ownerInitial : List Closure)
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
        environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (headerBelow : headerEnv ≤ env)
    (whole : history.whole.Charged sources ownerInitial count)
    (headerOccurrence : ParameterRouteOccurrence sources history.rightOrdered (headerSide).display.node)
    (prefixLedger : ParameterRouteLedger sources ownerInitial count history.final)
    : (history.applyRoute (field := sources.field) initial domain body function argument result hu hv location sourceGraph
      headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph noBinders ownerInitial sourceBound headerBelow).Charged sources ownerInitial count := by
  rw [applyRoute, RawGeneratedTypeRoute.Charged.eq_def]
  exact ⟨whole,
    .ownerPair (.major location) (.major location) _ _ (sourceBound sources.ordered) (sourceBound sources.ordered),
    .reindex headerOccurrence headerOccurrence prefixLedger prefixLedger⟩

/-- Both the output environment and the reusable route have the successor
prefix index. Widening preserves every original proof and closure list. -/
noncomputable def applyRoute_successorLedger
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight sourceSide headerSide)
    (noBinders : location.binderPrefix = []) (ownerInitial : List Closure)
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
        environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (headerBelow : headerEnv ≤ env)
    (whole : history.whole.Charged sources ownerInitial count)
    (headerOccurrence : ParameterRouteOccurrence sources history.rightOrdered (headerSide).display.node)
    (domainOccurrence : ParameterRouteOccurrence sources history.rightOrdered (.ref history.rightDomain))
    (prefixLedger : ParameterRouteLedger sources ownerInitial count history.final)
    : (history.applyRoute (field := sources.field) initial domain body function argument result hu hv location sourceGraph
      headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph noBinders ownerInitial sourceBound headerBelow).Charged sources ownerInitial (count + 1) ×
      ParameterRouteLedger sources ownerInitial (count + 1)
        (groupCaptureHistoryReserve sources.field sources.major headerDomain history.leftOrdered history.rightOrdered
          ownerInitial history.final history.argumentSeedReserve) := by
  have charged := applyRoute_charged sources initial domain body function argument result hu hv location sourceGraph
    headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph history noBinders ownerInitial sourceBound
    headerBelow whole headerOccurrence prefixLedger
  refine ⟨RawGeneratedTypeRoute.widenCharged _ charged (Nat.le_succ _), ?_⟩
  have headerEq : history.rightDomain = headerDomain :=
    (EndpointState.ref.inj history.rightDomainEq).symm
  have output := history.seedCaptureLedger sources ownerInitial whole (.major location)
    (sourceBound sources.ordered) domainOccurrence prefixLedger
  simpa only [groupCaptureHistoryReserve, headerEq] using output

end
end OriginalApplyPiHistory
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
