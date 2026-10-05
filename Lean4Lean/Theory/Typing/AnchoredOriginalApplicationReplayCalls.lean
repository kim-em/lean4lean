import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiReplayBound

/-! Only smaller original clauses for an application-history node. The
structural interpreter supplies the single whole-history child replay. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

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

structure OriginalApplyPiHistory.ApplicationCalls
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight sourceSide headerSide)
    (limit : Nat) : Prop where
  bodyR : ∀ selected : OriginalTypeRouteFrame env registry target sourceGraph commonLeft commonRight,
    GeneratedObservationCall (selected.realization.frame.captureBase selected.realization.substitutions)
      (selected.realization.frame.captureBase selected.realization.substitutions).initialCaps
      (applicationResultDisplay initial domain body function argument result hu hv location (.identity _))
      (applicationBodyDisplay initial domain body function argument result hu hv location (.identity _))
      (sourceRaw.comp commonLeft) (sourceRaw.comp commonRight) history.leftOrdered history.leftOrdered limit
  domainF : richSchedule .fundamental (Closure.close ((sourceSide).node.dependencyOrigin history.leftOrdered)
        (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)).cost < limit →
    OriginalCodeInductionAt env registry history.leftOrdered initial (.appDomain location)
      (Closure.close ((sourceSide).node.dependencyOrigin history.leftOrdered)
        (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)).cost
  argumentF : richSchedule .fundamental (Closure.close ((sourceSide).node.dependencyOrigin history.leftOrdered)
        (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)).cost < limit →
    OriginalComputationalInductionAt env registry history.leftOrdered initial (.appArgument location)
      (Closure.close ((sourceSide).node.dependencyOrigin history.leftOrdered)
        (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)).cost
  argumentR : ∀ selected : OriginalTypeRouteFrame env registry target sourceGraph commonLeft commonRight,
    ∀ {n : Nat} {profile : Profile n},
    ∀ packet : ApplicationBackwardQueries initial domain body function argument result hu hv location
        selected.realization.frame selected.realization.substitutions history.leftOrdered true profile,
      packet.queries.Calls
        (OriginalNestedDisplay.identity (selected.realization.frame.captureBase selected.realization.substitutions)
          argument (.ofLocation (.appArgument location) initial)) history.leftOrdered limit
  argumentFormationR : ∀ selected : OriginalTypeRouteFrame env registry target sourceGraph commonLeft commonRight,
    GeneratedObservationCall
      (selected.realization.frame.captureBase selected.realization.substitutions)
      (selected.realization.frame.captureBase selected.realization.substitutions).initialCaps
      (applicationDomainDisplay (frame := selected.realization.frame) (substitutions := selected.realization.substitutions))
      (applicationArgumentFormationDisplay (frame := selected.realization.frame) (substitutions := selected.realization.substitutions))
      (sourceRaw.comp commonLeft) (sourceRaw.comp commonRight) history.leftOrdered history.leftOrdered limit
  piF : richSchedule .fundamental (Closure.close ((sourceSide).node.dependencyOrigin history.leftOrdered)
        (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)).cost < limit →
    OriginalCodeInductionAt env registry history.leftOrdered initial (.appPiFormation location)
      (Closure.close ((sourceSide).node.dependencyOrigin history.leftOrdered)
        (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)).cost
  headerDomainF : richSchedule .fundamental
      (((EndpointState.pi hcu hdv (.ref headerDomain) headerBody).dependencyOrigin history.rightOrdered).weight *
        (1 + environmentCost history.final)) < limit →
    OriginalCodeInductionAt env registry history.rightOrdered headerInitial (.piDomain headerLocation)
      (((EndpointState.pi hcu hdv (.ref headerDomain) headerBody).dependencyOrigin history.rightOrdered).weight *
        (1 + environmentCost history.final))
  headerBodyF : richSchedule .fundamental
      (((EndpointState.pi hcu hdv (.ref headerDomain) headerBody).dependencyOrigin history.rightOrdered).weight *
        (1 + environmentCost history.final)) < limit →
    OriginalCodeInductionAt env registry history.rightOrdered headerInitial (.piBody headerLocation)
      (((EndpointState.pi hcu hdv (.ref headerDomain) headerBody).dependencyOrigin history.rightOrdered).weight *
        (1 + environmentCost history.final))

/-- Convert the selected incoming support through the application step and
compose its semantic path with the preceding history. No query or alignment
answer is supplied by the call package. -/
theorem OriginalApplyPiHistory.replayApplicationReplyStep
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
    (wholeReplay : history.whole.schedule < limit →
      ∀ {queryRank : Nat} {start : VExpr} {queryProfile : Profile queryRank},
        BoundedParameterReply base commonCaps start (sourceSide).pi.display commonLeft commonRight queryProfile
          (environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)) →
        queryProfile.HasType (.sort true) →
        Nonempty (BoundedParameterReply base commonCaps start (headerSide).display commonLeft commonRight
          queryProfile (environmentCost history.final)))
    (scheduled : history.schedule < limit)
    (incoming : BoundedParameterReply base commonCaps start (sourceSide).resultDisplay commonLeft commonRight
      (profile : Profile n) (environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)))
    (sorted : profile.HasType (.sort true)) :
    Nonempty (BoundedParameterReply base commonCaps start history.destination commonLeft commonRight profile
      (environmentCost (history.outputEnvironment field major ownerInitial))) := by
  let selected : OriginalTypeRouteFrame env registry target sourceGraph commonLeft commonRight := {
    locals := incoming.reply.answer.reply.locals
    available := incoming.reply.answer.reply.available
    realization := incoming.reply.answer.reply.realization
    closed := incoming.reply.answer.reply.closed }
  obtain ⟨footprint, ⟨certificate⟩, resources⟩ := incoming.reply.answer.reply.query.code henv sorted
  have applicationPaid : richSchedule .fundamental (Closure.close ((sourceSide).node.dependencyOrigin history.leftOrdered)
      (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)).cost < limit :=
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) scheduled
  have headerPaid : richSchedule .fundamental
      (((EndpointState.pi hcu hdv (.ref headerDomain) headerBody).dependencyOrigin history.rightOrdered).weight *
        (1 + environmentCost history.final)) < limit :=
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) scheduled
  obtain ⟨answer⟩ := history.replayApplicationStep (field := field) initial domain body function argument result hu hv location sourceGraph
    headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph generated selected incoming.reply.answer.capped
    (fun ordered => incoming.reply.bounded ordered) noBinders sourceBound henv hscoped headerBelow formed
    (calls.bodyR selected) (calls.domainF applicationPaid) (calls.argumentF applicationPaid)
    (calls.argumentR selected) (calls.argumentFormationR selected) (calls.piF applicationPaid)
    (calls.headerDomainF headerPaid) (calls.headerBodyF headerPaid) wholeReplay scheduled certificate resources
  let completed := answer.boundedReply
  have sourceRelated : TypeRelated env U registry target start ((B.inst a).subst (sourceRaw.comp commonLeft)) profile := by
    simpa only [OriginalApplicationTypeRouteSide.resultDisplay, OriginalNestedDisplay.ofOccurrence, subst_subst, originalApplicationTypeRouteSide] using incoming.related
  have sourcePath : TypeConversion env U target start ((B.inst a).subst (sourceRaw.comp commonLeft)) := by
    simpa only [OriginalApplicationTypeRouteSide.resultDisplay, OriginalNestedDisplay.ofOccurrence, subst_subst, originalApplicationTypeRouteSide] using incoming.path
  exact ⟨{ reply := completed.reply
           related := sourceRelated.trans henv completed.related
           path := sourcePath.trans completed.path }⟩

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
