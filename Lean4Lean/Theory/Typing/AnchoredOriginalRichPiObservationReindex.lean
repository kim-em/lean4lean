import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiQueryReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPrefixMeasure

/-! Complete Pi expression-query reindexing through the full rich grammar.
Only domain/body original comparisons reconstruct source data; formation
semantics uses one strictly smaller unary F at the actual source node. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

noncomputable def RichCert.graded
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant (profile : Profile n) footprint)
    (resources : footprint.Available available) :
    RichGradedResult sourceEnv env U registry target node locals σ available profile :=
  ⟨n, Nat.le_refl _, profile, footprint, .code certificate,
    by rw [raiseProfile_self]; exact .refl _, resources, Profile.HasType.sortable_live certificate.formed⟩

section
variable
  {leftHeader : EndpointRef leftEnv U [] lhe lht}
  {leftField : EndpointRef leftOriginEnv U leftOriginSource lfe lft}
  {leftMajor : EndpointRef leftOriginEnv U leftOriginSource lme lmt}
  {rightHeader : EndpointRef rightEnv U [] rhe rht}
  {rightField : EndpointRef rightOriginEnv U rightOriginSource rfe rft}
  {rightMajor : EndpointRef rightOriginEnv U rightOriginSource rme rmt}
  {leftContext : ContextDerivation leftEnv U leftSource}
  {rightContext : ContextDerivation rightEnv U rightSource}
  {leftDomain : EndpointRef leftEnv U leftSource A (.sort u)}
  {rightDomain : EndpointRef rightEnv U rightSource C (.sort u')}
  {leftNode : EndpointState leftEnv U leftSource (.forallE A B) leftAssigned}
  {rightNode : EndpointState rightEnv U rightSource (.forallE C D) rightAssigned}
  (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
  (lf : leftEnv.Ordered) (lo : leftOriginEnv.Ordered)
  (rf : rightEnv.Ordered) (ro : rightOriginEnv.Ordered) (leftInitial rightInitial : List Closure)
  (leftFrame : HeaderBinderFrame leftHeader leftField leftMajor env registry target leftContext leftLocals σ σ leftAvailable)
  (leftLocation : Located leftHeader (.ref leftDomain))
  (leftLineage : leftLocation.contextDerivation .nil = leftContext)
  (rightFrame : HeaderBinderFrame rightHeader rightField rightMajor env registry target rightContext rightLocals τ τ rightAvailable)
  (rightLocation : Located rightHeader (.ref rightDomain))
  (rightLineage : rightLocation.contextDerivation .nil = rightContext)
  (leftBody : EndpointState leftEnv U (A :: leftSource) B (.sort v))
  (rightBody : EndpointState rightEnv U (C :: rightSource) D (.sort v'))
  (lu : u.WF U) (lv : v.WF U) (ru : u'.WF U) (rv : v'.WF U)
  (leftRoute : PrefixRoute leftEnv U leftSource (.forallE A B) leftNode (.pi lu lv (.ref leftDomain) leftBody))
  (rightRoute : PrefixRoute rightEnv U rightSource (.forallE C D) rightNode (.pi ru rv (.ref rightDomain) rightBody))
  (equal : (VExpr.forallE A B).subst σ = (VExpr.forallE C D).subst τ)
  (domainR :
    richSchedule .expressionReindex
      ((Closure.close (leftDomain.dependencyOrigin lf) (leftFrame.dependencyEnvironment lf lo leftInitial)).cost +
       (Closure.close (rightDomain.dependencyOrigin rf) (rightFrame.dependencyEnvironment rf ro rightInitial)).cost) <
    richSchedule .expressionReindex
      ((Closure.close (leftNode.dependencyOrigin lf) (leftFrame.dependencyEnvironment lf lo leftInitial)).cost +
       (Closure.close (rightNode.dependencyOrigin rf) (rightFrame.dependencyEnvironment rf ro rightInitial)).cost) →
    A.subst σ = C.subst τ →
    RichCodeTransfer env U registry target (.ref leftDomain) (.ref rightDomain)
      leftLocals rightLocals σ τ leftAvailable rightAvailable)
  (bodyR : ∀ {n} {ambient : Profile n} {relevant : Bool} {domainFootprint : Footprint}
    (leftCode : RichCert leftEnv env U registry target (.ref leftDomain) leftLocals σ true ambient domainFootprint)
    (leftResources : domainFootprint.Available leftAvailable)
    (answer : RichCodeTransferResult env U registry target (.ref leftDomain) (.ref rightDomain)
      rightLocals σ τ rightAvailable true ambient),
    HeaderPiBodyReindex henv lf lo rf ro leftInitial rightInitial
      ⟨leftFrame, leftLocation, leftLineage, domainFootprint, leftCode, leftResources⟩
      ⟨rightFrame, rightLocation, rightLineage, answer.footprint, answer.certificate, answer.resources⟩
      leftBody rightBody relevant)

include henv hscoped formed lf lo rf ro leftInitial rightInitial leftFrame leftLocation leftLineage
  rightFrame rightLocation rightLineage leftBody rightBody lu lv ru rv leftRoute rightRoute equal domainR bodyR

/-- Complete computational Pi R, including original conversion prefixes and
all incoming code/observation wrappers. No assigned-type or semantic oracle
is required to reconstruct the destination observation. -/
theorem HeaderBinderFrame.piObservationReindexStep
    (query : RichObs leftEnv env U registry target leftNode leftLocals σ profile footprint)
    (resources : footprint.Available leftAvailable) :
    Nonempty (RichGradedResult rightEnv env U registry target rightNode rightLocals τ rightAvailable profile) := by
  apply query.replayOriginalPi henv hscoped formed (domain := .ref leftDomain) (body := leftBody) ?_
    lu lv leftRoute resources
  intro n ambient relevant prototypeDomain prototypeBody table domainFootprint rowFootprint leftCode guard rows leftResources rowResources
  have domains := (VExpr.forallE.inj equal).1
  have bodies := (VExpr.forallE.inj equal).2
  have leftBound := Nat.lt_of_lt_of_le
    (binder_domain_cost (leftDomain.dependencyOrigin lf) [leftBody.dependencyOrigin lf] []
      (leftFrame.dependencyEnvironment lf lo leftInitial))
    (leftRoute.dependency_cost_le lf (leftFrame.dependencyEnvironment lf lo leftInitial))
  have rightBound := Nat.lt_of_lt_of_le
    (binder_domain_cost (rightDomain.dependencyOrigin rf) [rightBody.dependencyOrigin rf] []
      (rightFrame.dependencyEnvironment rf ro rightInitial))
    (rightRoute.dependency_cost_le rf (rightFrame.dependencyEnvironment rf ro rightInitial))
  obtain ⟨domainAnswer⟩ := domainR (richSchedule_strict (Nat.add_lt_add leftBound rightBound) _ _)
    domains leftCode leftResources
  let left : HeaderPiSide leftHeader leftField leftMajor env registry target leftContext leftDomain
      leftLocals σ leftAvailable ambient :=
    ⟨leftFrame, leftLocation, leftLineage, domainFootprint, leftCode, leftResources⟩
  let right : HeaderPiSide rightHeader rightField rightMajor env registry target rightContext rightDomain
      rightLocals τ rightAvailable ambient :=
    ⟨rightFrame, rightLocation, rightLineage, domainAnswer.footprint, domainAnswer.certificate, domainAnswer.resources⟩
  obtain ⟨rowFootprint, ⟨rowCode⟩, available⟩ := rows.reindexPiRows henv lf lo rf ro leftInitial rightInitial
    left right leftBody rightBody equal (bodyR leftCode leftResources domainAnswer) rowResources
  have rightGuard : PiGuard env U target τ C D prototypeDomain prototypeBody := {
    domainPath := by simpa only [domains] using guard.domainPath
    bodyPath := by simpa only [domains, bodies] using guard.bodyPath }
  exact ⟨(RichCert.route rightRoute (.pi ru rv domainAnswer.certificate rightGuard rowCode)).graded
    (fun i need member => (List.mem_append.mp member).elim (domainAnswer.resources i need) (available i need))⟩

end
section
variable
  {leftHeader : EndpointRef leftEnv U [] lhe lht}
  {leftField : EndpointRef leftOriginEnv U leftOriginSource lfe lft}
  {leftMajor : EndpointRef leftOriginEnv U leftOriginSource lme lmt}
  {rightHeader : EndpointRef rightEnv U [] rhe rht}
  {rightField : EndpointRef rightOriginEnv U rightOriginSource rfe rft}
  {rightMajor : EndpointRef rightOriginEnv U rightOriginSource rme rmt}
  {leftContext : ContextDerivation leftEnv U leftSource}
  {rightContext : ContextDerivation rightEnv U rightSource}
  {leftDomain : EndpointRef leftEnv U leftSource A (.sort u)}
  {rightDomain : EndpointRef rightEnv U rightSource C (.sort u')}
  {leftNode : EndpointState leftEnv U leftSource (.forallE A B) (.sort leftLevel)}
  {rightNode : EndpointState rightEnv U rightSource (.forallE C D) (.sort rightLevel)}
  (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
  (lf : leftEnv.Ordered) (lo : leftOriginEnv.Ordered)
  (rf : rightEnv.Ordered) (ro : rightOriginEnv.Ordered) (leftInitial rightInitial : List Closure)
  (leftFrame : HeaderBinderFrame leftHeader leftField leftMajor env registry target leftContext leftLocals σ σ leftAvailable)
  (leftLocation : Located leftHeader (.ref leftDomain))
  (leftLineage : leftLocation.contextDerivation .nil = leftContext)
  (rightFrame : HeaderBinderFrame rightHeader rightField rightMajor env registry target rightContext rightLocals τ τ rightAvailable)
  (rightLocation : Located rightHeader (.ref rightDomain))
  (rightLineage : rightLocation.contextDerivation .nil = rightContext)
  (leftBody : EndpointState leftEnv U (A :: leftSource) B (.sort v))
  (rightBody : EndpointState rightEnv U (C :: rightSource) D (.sort v'))
  (lu : u.WF U) (lv : v.WF U) (ru : u'.WF U) (rv : v'.WF U)
  (leftRoute : PrefixRoute leftEnv U leftSource (.forallE A B) leftNode (.pi lu lv (.ref leftDomain) leftBody))
  (rightRoute : PrefixRoute rightEnv U rightSource (.forallE C D) rightNode (.pi ru rv (.ref rightDomain) rightBody))
  (equal : (VExpr.forallE A B).subst σ = (VExpr.forallE C D).subst τ)
  (domainR :
    richSchedule .expressionReindex
      ((Closure.close (leftDomain.dependencyOrigin lf) (leftFrame.dependencyEnvironment lf lo leftInitial)).cost +
       (Closure.close (rightDomain.dependencyOrigin rf) (rightFrame.dependencyEnvironment rf ro rightInitial)).cost) <
    richSchedule .expressionReindex
      ((Closure.close (leftNode.dependencyOrigin lf) (leftFrame.dependencyEnvironment lf lo leftInitial)).cost +
       (Closure.close (rightNode.dependencyOrigin rf) (rightFrame.dependencyEnvironment rf ro rightInitial)).cost) →
    A.subst σ = C.subst τ →
    RichCodeTransfer env U registry target (.ref leftDomain) (.ref rightDomain)
      leftLocals rightLocals σ τ leftAvailable rightAvailable)
  (bodyR : ∀ {n} {ambient : Profile n} {relevant : Bool} {domainFootprint : Footprint}
    (leftCode : RichCert leftEnv env U registry target (.ref leftDomain) leftLocals σ true ambient domainFootprint)
    (leftResources : domainFootprint.Available leftAvailable)
    (answer : RichCodeTransferResult env U registry target (.ref leftDomain) (.ref rightDomain)
      rightLocals σ τ rightAvailable true ambient),
    HeaderPiBodyReindex henv lf lo rf ro leftInitial rightInitial
      ⟨leftFrame, leftLocation, leftLineage, domainFootprint, leftCode, leftResources⟩
      ⟨rightFrame, rightLocation, rightLineage, answer.footprint, answer.certificate, answer.resources⟩
      leftBody rightBody relevant)

include henv hscoped formed lf lo rf ro leftInitial rightInitial leftFrame leftLocation leftLineage
  rightFrame rightLocation rightLineage leftBody rightBody lu lv ru rv leftRoute rightRoute equal domainR bodyR

/-- The formation-code channel uses the same complete source reconstruction
and one unary F call at the actual source formation, strictly below the pair. -/
theorem HeaderBinderFrame.piReindexStep
    (leftClosed : leftAvailable.AtomClosed)
    (leftSubstitutions : Ctx.SubstEq env U target σ σ leftSource)
    (sourceF : HeaderCodeInductionAt leftHeader leftField leftMajor env registry lf lo leftInitial
      leftContext leftNode
      ((Closure.close (leftNode.dependencyOrigin lf) (leftFrame.dependencyEnvironment lf lo leftInitial)).cost +
       (Closure.close (rightNode.dependencyOrigin rf) (rightFrame.dependencyEnvironment rf ro rightInitial)).cost))
    (query : RichCert leftEnv env U registry target leftNode leftLocals σ relevant profile footprint)
    (resources : footprint.Available leftAvailable) :
    Nonempty (RichCodeTransferResult env U registry target leftNode rightNode rightLocals σ τ
      rightAvailable relevant profile) := by
  obtain ⟨destinationQuery⟩ := HeaderBinderFrame.piObservationReindexStep henv hscoped formed lf lo rf ro
    leftInitial rightInitial leftFrame leftLocation leftLineage rightFrame rightLocation rightLineage
    leftBody rightBody lu lv ru rv leftRoute rightRoute equal domainR bodyR (.code query) resources
  obtain ⟨required, ⟨certificate⟩, outputResources⟩ := destinationQuery.code henv query.formed
  have positive := (Closure.close (rightNode.dependencyOrigin rf)
    (rightFrame.dependencyEnvironment rf ro rightInitial)).cost_pos
  obtain ⟨semantics⟩ := sourceF target leftLocals σ σ leftAvailable leftFrame
    (Nat.lt_add_of_pos_right positive) leftClosed formed leftSubstitutions query resources
  exact ⟨⟨required, certificate, outputResources, by simpa only [← equal] using semantics.related⟩⟩

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
