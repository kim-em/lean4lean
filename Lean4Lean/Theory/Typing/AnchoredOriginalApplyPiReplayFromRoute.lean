import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedApplyPiHistory

/-! Compatibility wrapper supplying the single whole-history recursive call
from the existing route replay theorem. The step itself is replay-free. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

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
  {headerRoot : EndpointRef headerEnv U headerRootSource headerExpression headerType}
  (headerInitial : ContextDerivation headerEnv U headerRootSource)
  (headerDomain : EndpointRef headerEnv U headerSource C (.sort cu))
  (headerBody : EndpointState headerEnv U (C :: headerSource) D (.sort dv))
  (hcu : cu.WF U) (hdv : dv.WF U)
  (headerLocation : Located headerRoot (.pi hcu hdv (.ref headerDomain) headerBody))
  (headerGraph : OriginalCaptureMap (common := common) (headerLocation.contextDerivation headerInitial) headerRaw)

local notation "sourceSide" => originalApplicationTypeRouteSide initial domain body function argument result hu hv location sourceGraph
local notation "headerSide" => originalNativePiRouteSide headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph

theorem OriginalApplyPiHistory.replayApplication
    {n : Nat} {profile : Profile n}
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight sourceSide headerSide)
    {base : OriginalCaptureBase env U registry target}
    (generated : history.Generated base commonCaps)
    (selected : OriginalTypeRouteFrame env registry target sourceGraph commonLeft commonRight)
    (selectedGenerated : CappedCaptureGenerated base commonCaps commonLeft commonRight sourceGraph selected.realization.frame.raw)
    (selectedBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (selected.realization.frame.dependencyEnvironment ordered) ≤
        environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered))
    (noBinders : location.binderPrefix = [])
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (bodyR : GeneratedObservationCall (selected.realization.frame.captureBase selected.realization.substitutions)
      (selected.realization.frame.captureBase selected.realization.substitutions).initialCaps
      (applicationResultDisplay initial domain body function argument result hu hv location (.identity _))
      (applicationBodyDisplay initial domain body function argument result hu hv location (.identity _))
      (sourceRaw.comp commonLeft) (sourceRaw.comp commonRight) history.leftOrdered history.leftOrdered
      limit)
    (domainF : OriginalCodeInductionAt env registry history.leftOrdered initial (.appDomain location)
      (Closure.close ((sourceSide).node.dependencyOrigin history.leftOrdered)
        (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)).cost)
    (argumentF : OriginalComputationalInductionAt env registry history.leftOrdered initial (.appArgument location)
      (Closure.close ((sourceSide).node.dependencyOrigin history.leftOrdered)
        (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)).cost)
    (argumentR : ∀ packet : ApplicationBackwardQueries initial domain body function argument result hu hv location
        selected.realization.frame selected.realization.substitutions history.leftOrdered true profile,
      packet.queries.Calls
        (OriginalNestedDisplay.identity (selected.realization.frame.captureBase selected.realization.substitutions)
          argument (.ofLocation (.appArgument location) initial)) history.leftOrdered
        limit)
    (argumentFormationR : GeneratedObservationCall
      (selected.realization.frame.captureBase selected.realization.substitutions)
      (selected.realization.frame.captureBase selected.realization.substitutions).initialCaps
      (applicationDomainDisplay (frame := selected.realization.frame) (substitutions := selected.realization.substitutions))
      (applicationArgumentFormationDisplay (frame := selected.realization.frame) (substitutions := selected.realization.substitutions))
      (sourceRaw.comp commonLeft) (sourceRaw.comp commonRight) history.leftOrdered history.leftOrdered
      limit)
    (piF : OriginalCodeInductionAt env registry history.leftOrdered initial (.appPiFormation location)
      (Closure.close ((sourceSide).node.dependencyOrigin history.leftOrdered)
        (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)).cost)
    (headerDomainF : OriginalCodeInductionAt env registry history.rightOrdered headerInitial (.piDomain headerLocation)
      (((EndpointState.pi hcu hdv (.ref headerDomain) headerBody).dependencyOrigin history.rightOrdered).weight *
        (1 + environmentCost history.final)))
    (headerBodyF : OriginalCodeInductionAt env registry history.rightOrdered headerInitial (.piBody headerLocation)
      (((EndpointState.pi hcu hdv (.ref headerDomain) headerBody).dependencyOrigin history.rightOrdered).weight *
        (1 + environmentCost history.final)))
    (historyCalls : history.whole.Calls base commonCaps limit)
    (scheduled : history.schedule < limit)
    (certificate : RichCert sourceEnv env U registry target result selected.locals
      (sourceRaw.comp commonLeft) true (profile : Profile n) footprint)
    (resources : footprint.Available selected.available) :
    Nonempty (OriginalApplyPiReplayResult history field major ownerInitial base commonCaps profile) := by
  exact history.replayApplicationStep initial domain body function argument result hu hv location sourceGraph
    headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph generated selected selectedGenerated
    selectedBound noBinders sourceBound henv hscoped headerBelow formed bodyR domainF argumentF argumentR
    argumentFormationR piF headerDomainF headerBodyF
    (fun childScheduled {queryRank} {start} {queryProfile} incoming sorted => history.whole.replay generated.whole henv hscoped formed
      historyCalls childScheduled incoming sorted)
    scheduled certificate resources

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
