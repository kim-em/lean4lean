import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientFamilyApplyPiChain
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientRawTypeRouteReplay

/-! The successor baseline is obtained by the actual ambient-qualified
application producer and the finite raw-history interpreter. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option Elab.async false

section
variable {env : VEnv} {registry : CanonicalHead.Registry} {target : List VExpr}
  {commonLeft commonRight : Subst}
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

/-- Compute the next header baseline with an actual empty incoming source
query. Every nontrivial obligation is an original child call already stored
in the application/whole-history call ledgers. -/
theorem OriginalApplyPiHistory.baselineReplayAmbient
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight sourceSide headerSide)
    {base : OriginalCaptureBase env U registry target}
    (generated : history.AmbientGenerated base commonCaps)
    (noBinders : location.binderPrefix = [])
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
        environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (bank : OriginalLowerCallBank env U registry limit)
    (scheduled : history.schedule < limit) :
    Nonempty (AmbientApplyPiReplayResult history field major ownerInitial base commonCaps (Profile.empty : Profile 0)) := by
  exact history.replayApplicationAmbientStep (field := field) initial domain body function argument result hu hv location sourceGraph
    headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
    generated history.sourceFrame generated.source (fun _ => Nat.le_refl _)
    noBinders sourceBound henv hscoped headerBelow formed bank
    (fun paid {_ _ _} incoming sorted => history.whole.replayAmbient generated.whole henv hscoped formed bank paid incoming sorted)
    scheduled (.legacy (.seed .empty (Profile.HasType.empty (Profile.WF.sort true))))
    (fun _ _ member => nomatch member)

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
