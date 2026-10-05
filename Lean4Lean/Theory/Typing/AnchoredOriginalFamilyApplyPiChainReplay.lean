import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyApplyPiChain
import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationReplayCalls
import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiReplayFromRoute

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
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
theorem OriginalApplyPiHistory.baselineReplay
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight sourceSide headerSide)
    {base : OriginalCaptureBase env U registry target}
    (generated : history.Generated base commonCaps)
    (noBinders : location.binderPrefix = [])
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
        environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (calls : history.ApplicationCalls initial domain body function argument result hu hv location sourceGraph
      headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph limit)
    (historyCalls : history.whole.Calls base commonCaps limit)
    (scheduled : history.schedule < limit) :
    Nonempty (OriginalApplyPiReplayResult history field major ownerInitial base commonCaps (Profile.empty : Profile 0)) := by
  have applicationPaid : richSchedule .fundamental (Closure.close ((sourceSide).node.dependencyOrigin history.leftOrdered)
      (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)).cost < limit :=
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) scheduled
  have headerPaid : richSchedule .fundamental
      (((EndpointState.pi hcu hdv (.ref headerDomain) headerBody).dependencyOrigin history.rightOrdered).weight *
        (1 + environmentCost history.final)) < limit :=
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) scheduled
  exact history.replayApplication (field := field) initial domain body function argument result hu hv location sourceGraph
    headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
    generated history.sourceFrame generated.source (fun _ => Nat.le_refl _)
    noBinders sourceBound henv hscoped headerBelow formed
    (calls.bodyR history.sourceFrame) (calls.domainF applicationPaid) (calls.argumentF applicationPaid)
    (calls.argumentR history.sourceFrame) (calls.argumentFormationR history.sourceFrame) (calls.piF applicationPaid)
    (calls.headerDomainF headerPaid) (calls.headerBodyF headerPaid) historyCalls scheduled
    (.legacy (.seed .empty (Profile.HasType.empty (Profile.WF.sort true))))
    (fun _ _ member => nomatch member)

include field in
/-- The actual dependent successor creates its captured baseline internally;
no completed alignment or outgoing frame is supplied by the caller. -/
theorem OriginalApplyPiHistory.nextParameterGenerated
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight sourceSide headerSide)
    {base : OriginalCaptureBase env U registry target}
    (generated : history.Generated base commonCaps)
    (noBinders : location.binderPrefix = [])
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
        environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (calls : history.ApplicationCalls initial domain body function argument result hu hv location sourceGraph
      headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph limit)
    (historyCalls : history.whole.Calls base commonCaps limit)
    (scheduled : history.schedule < limit)
    (next : OriginalApplicationTypeRouteSide U common)
    (nextOrdered : next.sourceEnv.Ordered) (nextBelow : next.sourceEnv ≤ env)
    (nextFrame : OriginalTypeRouteFrame env registry target next.graph commonLeft commonRight)
    (nextGenerated : CappedCaptureGenerated base commonCaps commonLeft commonRight next.graph nextFrame.realization.frame.raw)
    (adjacent : (VExpr.app f a).subst sourceRaw = next.f.subst next.raw)
    (headerShape : D = .forallE nextDomain nextBody) :
    ∃ nextHeader : OriginalPiTypeRouteSide U common,
      ∃ nextHistory : OriginalApplyPiHistory env registry target commonLeft commonRight next nextHeader,
        nextHistory.Generated base commonCaps ∧
        nextHistory.sourceFrame = nextFrame ∧
        nextHeader.sourceEnv = headerEnv ∧ nextHeader.sourceEnv ≤ env ∧
        nextHeader.A = nextDomain ∧ nextHeader.B = nextBody ∧
        nextHeader.raw = headerRaw.cons (a.subst sourceRaw) := by
  obtain ⟨replayed⟩ := history.baselineReplay (field := field) initial domain body function argument result hu hv location sourceGraph
    headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph generated noBinders sourceBound
    henv hscoped headerBelow formed calls historyCalls scheduled
  exact history.nextParameter (field := field) initial domain body function argument result hu hv location sourceGraph
    headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph noBinders ownerInitial sourceBound
    headerBelow generated replayed next nextOrdered nextBelow nextFrame nextGenerated adjacent headerShape

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
