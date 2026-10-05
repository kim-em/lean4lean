import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedPiRows
import Lean4Lean.Theory.Typing.AnchoredOriginalBoundedGeneratedReply
import Lean4Lean.Theory.Typing.AnchoredOriginalCappedPiQueryReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiObservationReindex

/-! Native Pi query reindexing computes its finite destination row replies
from the actual original domain/body children. Recursive calls retain the
common source display graph and fixed common binder caps. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private LambdaGuard.anchorRelated from Lean4Lean.Theory.Typing.AnchoredOriginalGenericPiReindex
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- A fixed pair of original expression children, restricted to actual
capped generated frames and the caller's strict original recursion budget. -/
def GeneratedObservationCall
    (base : OriginalCaptureBase env U registry target) (commonCaps : CaptureCaps)
    (left : OriginalNestedDisplay U common expression leftAssigned)
    (right : OriginalNestedDisplay U common expression rightAssigned)
    (commonLeft commonRight : Subst) (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered)
    (limit : Nat) : Prop :=
  ∀ {leftLocals leftAvailable}
    (leftFrame : OriginalCaptureRealization left.graph env registry target leftLocals commonLeft commonRight leftAvailable),
    CappedCaptureGenerated base commonCaps commonLeft commonRight left.graph leftFrame.frame.raw →
    leftAvailable.AtomClosed →
    ∀ {rightLocals rightAvailable}
    (rightFrame : OriginalCaptureRealization right.graph env registry target rightLocals commonLeft commonRight rightAvailable),
    CappedCaptureGenerated base commonCaps commonLeft commonRight right.graph rightFrame.frame.raw →
    rightAvailable.AtomClosed →
    richSchedule .expressionReindex
      ((Closure.close (left.node.dependencyOrigin lf) (leftFrame.frame.dependencyEnvironment lf)).cost +
       (Closure.close (right.node.dependencyOrigin rf) (rightFrame.frame.dependencyEnvironment rf)).cost) < limit →
    ∀ {n : Nat} {profile : Profile n} {footprint : Footprint},
    RichObs left.sourceEnv env U registry target left.node leftLocals (left.raw.comp commonLeft) profile footprint →
    footprint.Available leftAvailable →
    Nonempty (BoundedGeneratedQueryReply base commonCaps right commonLeft commonRight profile
      (environmentCost (rightFrame.frame.dependencyEnvironment rf)))

private theorem lift_comp (raw commonLeft : Subst) (anchor : VExpr) :
    raw.lift.comp (commonLeft.cons anchor) = (raw.comp commonLeft).cons anchor := by
  funext index
  cases index <;> simp [Subst.comp, Subst.lift, Subst.cons]

section
variable
  {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
  {leftRoot : EndpointRef leftEnv U leftRootSource leftRootExpression leftRootType}
  {rightRoot : EndpointRef rightEnv U rightRootSource rightRootExpression rightRootType}
  {leftDomain : EndpointRef leftEnv U leftSource A (.sort u)}
  {rightDomain : EndpointRef rightEnv U rightSource C (.sort u')}
  {leftBody : EndpointState leftEnv U (A :: leftSource) B (.sort v)}
  {rightBody : EndpointState rightEnv U (C :: rightSource) D (.sort v')}
  {lu : u.WF U} {lv : v.WF U} {ru : u'.WF U} {rv : v'.WF U}
  (leftLocation : Located leftRoot (.pi lu lv (.ref leftDomain) leftBody))
  (rightLocation : Located rightRoot (.pi ru rv (.ref rightDomain) rightBody))
  (leftInitial : ContextDerivation leftEnv U leftRootSource)
  (rightInitial : ContextDerivation rightEnv U rightRootSource)
  (leftGraph : OriginalCaptureMap (common := common) (leftLocation.contextDerivation leftInitial) leftRaw)
  (rightGraph : OriginalCaptureMap (common := common) (rightLocation.contextDerivation rightInitial) rightRaw)
  (leftAnnotation : annotation = A.subst leftRaw)
  (rightAnnotation : annotation = C.subst rightRaw)
  (leftExpression : displayedBody = B.subst leftRaw.lift)
  (rightExpression : displayedBody = D.subst rightRaw.lift)
  (henv : env.Ordered) (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
  (lf : leftEnv.Ordered) (rf : rightEnv.Ordered)
  (leftFrame : OriginalCaptureRealization leftGraph env registry target leftLocals commonLeft commonRight leftAvailable)
  (leftCapped : CappedCaptureGenerated base commonCaps commonLeft commonRight leftGraph leftFrame.frame.raw)
  (leftClosed : leftAvailable.AtomClosed)

include henv leftBelow rightBelow leftCapped leftClosed in
private theorem RichRows.originalCappedReplies
    (rightFrame : OriginalCaptureRealization rightGraph env registry target
      (rightGraph.locals base.locals) commonLeft commonRight rightAvailable)
    (rightCapped : CappedCaptureGenerated base commonCaps commonLeft commonRight rightGraph rightFrame.frame.raw)
    (rightClosed : rightAvailable.AtomClosed)
    (leftCode : RichCert leftEnv env U registry target (.ref leftDomain) leftLocals (leftRaw.comp commonLeft)
      true (ambient : Profile n) leftFootprint)
    (leftResources : leftFootprint.Available leftAvailable)
    (rightCode : RichCert rightEnv env U registry target (.ref rightDomain) (rightGraph.locals base.locals)
      (rightRaw.comp commonLeft) true ambient rightFootprint)
    (rightResources : rightFootprint.Available rightAvailable)
    (parentLimit : Nat)
    (parentBound : richSchedule .expressionReindex
      ((Closure.close ((EndpointState.pi lu lv (.ref leftDomain) leftBody).dependencyOrigin lf)
        (leftFrame.frame.dependencyEnvironment lf)).cost +
       (Closure.close ((EndpointState.pi ru rv (.ref rightDomain) rightBody).dependencyOrigin rf)
        (rightFrame.frame.dependencyEnvironment rf)).cost) ≤ parentLimit)
    (bodyR : ∀ (key : Key n), GeneratedObservationCall base (commonCaps.push (Need.Fits key.input))
      (OriginalNestedDisplay.piBody leftLocation leftInitial leftGraph leftAnnotation leftExpression)
      (OriginalNestedDisplay.piBody rightLocation rightInitial rightGraph rightAnnotation rightExpression)
      (commonLeft.cons key.anchor) (commonRight.cons key.anchor) lf rf parentLimit)
    (rows : RichRows leftEnv env U registry target (.ref leftDomain) leftBody leftLocals
      (leftRaw.comp commonLeft) relevant ambient values footprint)
    (resources : footprint.Available leftAvailable) :
    ∃ answers : CappedPiRowAnswers (base := base) (commonCaps := commonCaps)
      rightLocation rightInitial rightGraph rightAnnotation rightExpression commonLeft commonRight ambient relevant values,
      answers.Bounded rightFrame := by
  match rows with
  | .nil => exact ⟨.nil, True.intro⟩
  | .cons (key := key) (support := output) (bodyFootprint := bodyFootprint) guard certificate pack covered rest =>
    have domains : A.subst (leftRaw.comp commonLeft) = C.subst (rightRaw.comp commonLeft) := by
      rw [← subst_subst, ← subst_subst, ← leftAnnotation, ← rightAnnotation]
    have rightGuard : LambdaGuard env U registry target (rightRaw.comp commonLeft) C key ambient := {
      inputTyped := guard.inputTyped, formed := guard.formed, anchor := guard.anchor
      path := by simpa only [domains] using guard.path
      domains := by simpa only [domains] using guard.domains }
    have bounded := fun need member => (pack.atomized_localNeeds need member).1
    have cover := fun need member atom present => covered atom ((pack.atomized_localNeeds need member).2 atom present)
    obtain ⟨leftChild, leftGenerated, leftEnvironment⟩ := leftFrame.bindCapped leftCapped leftDomain
      annotation leftAnnotation.symm leftBelow leftCode leftResources guard.inputTyped
      (LambdaGuard.anchorRelated henv guard) (guard.path.cast guard.anchor.1) _ bounded cover
    obtain ⟨rightChild, rightGenerated, rightEnvironment⟩ := rightFrame.bindCapped rightCapped rightDomain
      annotation rightAnnotation.symm rightBelow rightCode rightResources rightGuard.inputTyped
      (LambdaGuard.anchorRelated henv rightGuard) (rightGuard.path.cast rightGuard.anchor.1) _ bounded cover
    have bodyResources := pack.available_atomized_localNeeds
      (fun index need member => resources index need (List.mem_append_left _ member))
    have callBound : richSchedule .expressionReindex
        ((Closure.close (leftBody.dependencyOrigin lf) (leftChild.frame.dependencyEnvironment lf)).cost +
         (Closure.close (rightBody.dependencyOrigin rf) (rightChild.frame.dependencyEnvironment rf)).cost) < parentLimit := by
      rw [leftEnvironment lf, rightEnvironment rf]
      apply Nat.lt_of_lt_of_le _ parentBound
      exact richSchedule_strict (Nat.add_lt_add
        (binder_body_cost (by simp) _) (binder_body_cost (by simp) _)) _ _
    have observation : RichObs leftEnv env U registry target leftBody (Locals.push leftLocals)
        (leftRaw.lift.comp (commonLeft.cons key.anchor)) output bodyFootprint := by
      simpa only [lift_comp] using RichObs.code certificate
    obtain ⟨reply⟩ := bodyR key leftChild leftGenerated (Valuation.push_atomized_closed leftClosed _)
      rightChild rightGenerated (Valuation.push_atomized_closed rightClosed _) callBound observation bodyResources
    obtain ⟨tailAnswers, tailBound⟩ := originalCappedReplies rightFrame rightCapped rightClosed leftCode leftResources rightCode rightResources
      parentLimit parentBound bodyR rest (fun index need member => resources index need (List.mem_append_right _ member))
    refine ⟨.cons key output rightGuard certificate.formed reply.answer tailAnswers, ?_, tailBound⟩
    intro ordered
    simpa only [rightEnvironment rf, generatedBinder_environmentCost] using reply.bounded ordered
termination_by sizeOf rows


include henv leftBelow rightBelow leftCapped leftClosed in
/-- The native Pi step computes all destination queries from the actual
source domain and row table. Only strict original-child calls are supplied;
returned captured resources stay below the original destination capacity. -/
theorem nativePiGeneratedQueryStep
    (rightFrame : OriginalCaptureRealization rightGraph env registry target
      rightLocals commonLeft commonRight rightAvailable)
    (rightCapped : CappedCaptureGenerated base commonCaps commonLeft commonRight rightGraph rightFrame.frame.raw)
    (rightClosed : rightAvailable.AtomClosed)
    (domainR : GeneratedObservationCall base commonCaps
      (OriginalNestedDisplay.piDomain leftLocation leftInitial leftGraph leftAnnotation)
      (OriginalNestedDisplay.piDomain rightLocation rightInitial rightGraph rightAnnotation)
      commonLeft commonRight lf rf
      (richSchedule .expressionReindex
        ((Closure.close ((EndpointState.pi lu lv (.ref leftDomain) leftBody).dependencyOrigin lf)
          (leftFrame.frame.dependencyEnvironment lf)).cost +
         (Closure.close ((EndpointState.pi ru rv (.ref rightDomain) rightBody).dependencyOrigin rf)
          (rightFrame.frame.dependencyEnvironment rf)).cost)))
    (bodyR : ∀ {n : Nat} (key : Key n), GeneratedObservationCall base (commonCaps.push (Need.Fits key.input))
      (OriginalNestedDisplay.piBody leftLocation leftInitial leftGraph leftAnnotation leftExpression)
      (OriginalNestedDisplay.piBody rightLocation rightInitial rightGraph rightAnnotation rightExpression)
      (commonLeft.cons key.anchor) (commonRight.cons key.anchor) lf rf
      (richSchedule .expressionReindex
        ((Closure.close ((EndpointState.pi lu lv (.ref leftDomain) leftBody).dependencyOrigin lf)
          (leftFrame.frame.dependencyEnvironment lf)).cost +
         (Closure.close ((EndpointState.pi ru rv (.ref rightDomain) rightBody).dependencyOrigin rf)
          (rightFrame.frame.dependencyEnvironment rf)).cost)))
    (leftCode : RichCert leftEnv env U registry target (.ref leftDomain) leftLocals (leftRaw.comp commonLeft)
      true (ambient : Profile n) leftFootprint)
    (guard : PiGuard env U target (leftRaw.comp commonLeft) A B prototypeDomain prototypeBody)
    (rows : RichRows leftEnv env U registry target (.ref leftDomain) leftBody leftLocals
      (leftRaw.comp commonLeft) relevant ambient values footprint)
    (leftResources : leftFootprint.Available leftAvailable)
    (rowResources : footprint.Available leftAvailable) :
    Nonempty (BoundedGeneratedQueryReply base commonCaps
      (OriginalNestedDisplay.pi rightLocation rightInitial rightGraph rightAnnotation rightExpression)
      commonLeft commonRight (Profile.pi prototypeDomain prototypeBody ambient values)
      (environmentCost (rightFrame.frame.dependencyEnvironment rf))) := by
  have domainBound := richSchedule_strict (Nat.add_lt_add
    (binder_domain_cost (leftDomain.dependencyOrigin lf) [leftBody.dependencyOrigin lf] []
      (leftFrame.frame.dependencyEnvironment lf))
    (binder_domain_cost (rightDomain.dependencyOrigin rf) [rightBody.dependencyOrigin rf] []
      (rightFrame.frame.dependencyEnvironment rf))) RichPhase.expressionReindex RichPhase.expressionReindex
  obtain ⟨⟨⟨⟨domainLocals, domainAvailable, next, _nextGenerated, query, nextClosed⟩, nextCapped⟩, nextBound⟩⟩ :=
    domainR leftFrame leftCapped leftClosed rightFrame rightCapped rightClosed domainBound
      (.code leftCode) leftResources
  have sameLocals : domainLocals = rightGraph.locals base.locals := nextCapped.generated.locals_eq
  subst domainLocals
  obtain ⟨domainFootprint, ⟨domainCode⟩, domainResources⟩ := query.code henv leftCode.formed
  have parentBound : richSchedule .expressionReindex
      ((Closure.close ((EndpointState.pi lu lv (.ref leftDomain) leftBody).dependencyOrigin lf)
        (leftFrame.frame.dependencyEnvironment lf)).cost +
       (Closure.close ((EndpointState.pi ru rv (.ref rightDomain) rightBody).dependencyOrigin rf)
        (next.frame.dependencyEnvironment rf)).cost) ≤
      richSchedule .expressionReindex
      ((Closure.close ((EndpointState.pi lu lv (.ref leftDomain) leftBody).dependencyOrigin lf)
        (leftFrame.frame.dependencyEnvironment lf)).cost +
       (Closure.close ((EndpointState.pi ru rv (.ref rightDomain) rightBody).dependencyOrigin rf)
        (rightFrame.frame.dependencyEnvironment rf)).cost) := by
    have bound := nextBound rf
    simp only [richSchedule, Closure.cost]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_left
      (Nat.mul_le_mul_left _ (Nat.add_le_add_left bound 1)) _)) _
  obtain ⟨answers, answersBound⟩ := rows.originalCappedReplies
    leftLocation rightLocation leftInitial rightInitial leftGraph rightGraph
    leftAnnotation rightAnnotation leftExpression rightExpression henv leftBelow rightBelow lf rf
    leftFrame leftCapped leftClosed next nextCapped nextClosed leftCode leftResources domainCode domainResources
    _ parentBound (fun key => bodyR key) rowResources
  have domains : A.subst (leftRaw.comp commonLeft) = C.subst (rightRaw.comp commonLeft) := by
    rw [← subst_subst, ← subst_subst, ← leftAnnotation, ← rightAnnotation]
  have bodies : B.subst (leftRaw.comp commonLeft).lift = D.subst (rightRaw.comp commonLeft).lift := by
    rw [Subst.comp_lift, Subst.comp_lift, ← subst_subst, ← subst_subst,
      ← leftExpression, ← rightExpression]
  have rightGuard : PiGuard env U target (rightRaw.comp commonLeft) C D prototypeDomain prototypeBody := {
    domainPath := by simpa only [domains] using guard.domainPath
    bodyPath := by simpa only [domains, bodies] using guard.bodyPath }
  obtain ⟨finalAvailable, finalFrame, finalCapped, finalClosed, _included, finalBound,
    finalFootprint, ⟨finalCode⟩, finalResources⟩ :=
    answers.piCode henv next nextCapped nextClosed answersBound domainCode domainResources rightGuard
  exact ⟨⟨⟨⟨_, finalAvailable, finalFrame, finalCapped.generated,
    finalCode.graded finalResources, finalClosed⟩, finalCapped⟩,
    fun ordered => Nat.le_trans (finalBound ordered) (nextBound ordered)⟩⟩


include henv leftBelow rightBelow leftCapped leftClosed in
/-- Every legacy/rich Pi wrapper is replayed using actual domain/body
recursion. Prefixes retain their original endpoint route; all output frames
remain under the same pre-answer destination capacity. -/
theorem piGeneratedQueryStep
    (rightFrame : OriginalCaptureRealization rightGraph env registry target
      rightLocals commonLeft commonRight rightAvailable)
    (rightCapped : CappedCaptureGenerated base commonCaps commonLeft commonRight rightGraph rightFrame.frame.raw)
    (rightClosed : rightAvailable.AtomClosed)
    (domainR : GeneratedObservationCall base commonCaps
      (OriginalNestedDisplay.piDomain leftLocation leftInitial leftGraph leftAnnotation)
      (OriginalNestedDisplay.piDomain rightLocation rightInitial rightGraph rightAnnotation)
      commonLeft commonRight lf rf
      (richSchedule .expressionReindex
        ((Closure.close ((EndpointState.pi lu lv (.ref leftDomain) leftBody).dependencyOrigin lf)
          (leftFrame.frame.dependencyEnvironment lf)).cost +
         (Closure.close ((EndpointState.pi ru rv (.ref rightDomain) rightBody).dependencyOrigin rf)
          (rightFrame.frame.dependencyEnvironment rf)).cost)))
    (bodyR : ∀ {n : Nat} (key : Key n), GeneratedObservationCall base (commonCaps.push (Need.Fits key.input))
      (OriginalNestedDisplay.piBody leftLocation leftInitial leftGraph leftAnnotation leftExpression)
      (OriginalNestedDisplay.piBody rightLocation rightInitial rightGraph rightAnnotation rightExpression)
      (commonLeft.cons key.anchor) (commonRight.cons key.anchor) lf rf
      (richSchedule .expressionReindex
        ((Closure.close ((EndpointState.pi lu lv (.ref leftDomain) leftBody).dependencyOrigin lf)
          (leftFrame.frame.dependencyEnvironment lf)).cost +
         (Closure.close ((EndpointState.pi ru rv (.ref rightDomain) rightBody).dependencyOrigin rf)
          (rightFrame.frame.dependencyEnvironment rf)).cost)))
    (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {node : EndpointState leftEnv U leftSource (.forallE A B) assigned}
    (route : PrefixRoute leftEnv U leftSource (.forallE A B) node
      (.pi lu lv (.ref leftDomain) leftBody))
    (query : RichObs leftEnv env U registry target node leftLocals
      (leftRaw.comp commonLeft) (profile : Profile n) footprint)
    (resources : footprint.Available leftAvailable) :
    Nonempty (BoundedGeneratedQueryReply base commonCaps
      (OriginalNestedDisplay.pi rightLocation rightInitial rightGraph rightAnnotation rightExpression)
      commonLeft commonRight profile (environmentCost (rightFrame.frame.dependencyEnvironment rf))) := by
  apply query.replayCappedPi henv hscoped formed
    (fun {n} => .empty _ rightFrame rightCapped rightClosed (fun _ => Nat.le_refl _))
    ?_ lu lv route resources
  intro n ambient relevant prototypeDomain prototypeBody table domainFootprint rowFootprint
    domainCode guard rows domainResources rowResources
  exact nativePiGeneratedQueryStep leftLocation rightLocation leftInitial rightInitial leftGraph rightGraph
    leftAnnotation rightAnnotation leftExpression rightExpression henv leftBelow rightBelow lf rf
    leftFrame leftCapped leftClosed rightFrame rightCapped rightClosed domainR bodyR
    domainCode guard rows domainResources rowResources

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
