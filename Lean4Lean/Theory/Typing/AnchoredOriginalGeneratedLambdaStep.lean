import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedNativePiReindex
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedLambdaReply
import Lean4Lean.Theory.Typing.AnchoredOriginalCappedLambdaQueryReplay

/-! Actual lambda expression reindexing at generated source graphs.
The source domain and body queries generate independent capped destination
frames through strict original-child calls. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private LambdaGuard.anchorRelated from Lean4Lean.Theory.Typing.AnchoredOriginalGenericPiReindex
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

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
  {leftCodomain : EndpointState leftEnv U (A :: leftSource) B (.sort v)}
  {leftBody : EndpointState leftEnv U (A :: leftSource) b B}
  {rightCodomain : EndpointState rightEnv U (C :: rightSource) D (.sort v')}
  {rightBody : EndpointState rightEnv U (C :: rightSource) d D}
  {lu : u.WF U} {lv : v.WF U} {ru : u'.WF U} {rv : v'.WF U}
  (leftLocation : Located leftRoot (.lam lu lv (.ref leftDomain) leftCodomain leftBody))
  (rightLocation : Located rightRoot (.lam ru rv (.ref rightDomain) rightCodomain rightBody))
  (leftInitial : ContextDerivation leftEnv U leftRootSource)
  (rightInitial : ContextDerivation rightEnv U rightRootSource)
  (leftGraph : OriginalCaptureMap (common := common) (leftLocation.contextDerivation leftInitial) leftRaw)
  (rightGraph : OriginalCaptureMap (common := common) (rightLocation.contextDerivation rightInitial) rightRaw)
  (leftAnnotation : annotation = A.subst leftRaw)
  (rightAnnotation : annotation = C.subst rightRaw)
  (leftExpression : displayedBody = b.subst leftRaw.lift)
  (rightExpression : displayedBody = d.subst rightRaw.lift)
  (henv : env.Ordered) (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
  (lf : leftEnv.Ordered) (rf : rightEnv.Ordered)
  (leftFrame : OriginalCaptureRealization leftGraph env registry target leftLocals commonLeft commonRight leftAvailable)
  (leftCapped : CappedCaptureGenerated base commonCaps commonLeft commonRight leftGraph leftFrame.frame.raw)
  (leftClosed : leftAvailable.AtomClosed)

include henv leftBelow rightBelow leftCapped leftClosed in
/-- Native lambda query reconstruction from its actual original domain and
body, with unchanged common binder caps and output environment non-growth. -/
theorem nativeLambdaGeneratedQueryStep
    (rightFrame : OriginalCaptureRealization rightGraph env registry target
      rightLocals commonLeft commonRight rightAvailable)
    (rightCapped : CappedCaptureGenerated base commonCaps commonLeft commonRight rightGraph rightFrame.frame.raw)
    (rightClosed : rightAvailable.AtomClosed)
    (domainR : GeneratedObservationCall base commonCaps
      (OriginalNestedDisplay.lambdaDomain leftLocation leftInitial leftGraph leftAnnotation)
      (OriginalNestedDisplay.lambdaDomain rightLocation rightInitial rightGraph rightAnnotation)
      commonLeft commonRight lf rf
      (richSchedule .expressionReindex
        ((Closure.close ((EndpointState.lam lu lv (.ref leftDomain) leftCodomain leftBody).dependencyOrigin lf)
          (leftFrame.frame.dependencyEnvironment lf)).cost +
         (Closure.close ((EndpointState.lam ru rv (.ref rightDomain) rightCodomain rightBody).dependencyOrigin rf)
          (rightFrame.frame.dependencyEnvironment rf)).cost)))
    (bodyR : ∀ {n : Nat} (key : Key n), GeneratedObservationCall base (commonCaps.push (Need.Fits key.input))
      (OriginalNestedDisplay.lambdaBody leftLocation leftInitial leftGraph leftAnnotation leftExpression)
      (OriginalNestedDisplay.lambdaBody rightLocation rightInitial rightGraph rightAnnotation rightExpression)
      (commonLeft.cons key.anchor) (commonRight.cons key.anchor) lf rf
      (richSchedule .expressionReindex
        ((Closure.close ((EndpointState.lam lu lv (.ref leftDomain) leftCodomain leftBody).dependencyOrigin lf)
          (leftFrame.frame.dependencyEnvironment lf)).cost +
         (Closure.close ((EndpointState.lam ru rv (.ref rightDomain) rightCodomain rightBody).dependencyOrigin rf)
          (rightFrame.frame.dependencyEnvironment rf)).cost)))
    (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (leftCode : RichCert leftEnv env U registry target (.ref leftDomain) leftLocals (leftRaw.comp commonLeft)
      true (ambient : Profile n) leftFootprint)
    (guard : LambdaGuard env U registry target (leftRaw.comp commonLeft) A (key : Key n) ambient)
    (query : RichObs leftEnv env U registry target leftBody (Locals.push leftLocals)
      ((leftRaw.comp commonLeft).cons key.anchor) (.singleton output) bodyFootprint)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (leftResources : leftFootprint.Available leftAvailable)
    (resources : outside.Available leftAvailable) :
    Nonempty (BoundedGeneratedQueryReply base commonCaps
      (OriginalNestedDisplay.lambda rightLocation rightInitial rightGraph rightAnnotation rightExpression)
      commonLeft commonRight (Profile.fn key output)
      (environmentCost (rightFrame.frame.dependencyEnvironment rf))) := by
  have domainBound := richSchedule_strict (Nat.add_lt_add
    (binder_domain_cost (leftDomain.dependencyOrigin lf)
      [leftCodomain.dependencyOrigin lf, leftBody.dependencyOrigin lf] []
      (leftFrame.frame.dependencyEnvironment lf))
    (binder_domain_cost (rightDomain.dependencyOrigin rf)
      [rightCodomain.dependencyOrigin rf, rightBody.dependencyOrigin rf] []
      (rightFrame.frame.dependencyEnvironment rf))) RichPhase.expressionReindex RichPhase.expressionReindex
  obtain ⟨⟨⟨⟨domainLocals, domainAvailable, next, _nextGenerated, domainQuery, nextClosed⟩, nextCapped⟩, nextBound⟩⟩ :=
    domainR leftFrame leftCapped leftClosed rightFrame rightCapped rightClosed domainBound
      (.code leftCode) leftResources
  have sameLocals : domainLocals = rightGraph.locals base.locals := nextCapped.generated.locals_eq
  subst domainLocals
  obtain ⟨domainFootprint, ⟨domainCode⟩, domainResources⟩ := domainQuery.code henv leftCode.formed
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
  obtain ⟨rightChild, rightGenerated, rightEnvironment⟩ := next.bindCapped nextCapped rightDomain
    annotation rightAnnotation.symm rightBelow domainCode domainResources rightGuard.inputTyped
    (LambdaGuard.anchorRelated henv rightGuard) (rightGuard.path.cast rightGuard.anchor.1) _ bounded cover
  have parentBound : (Closure.close
      ((EndpointState.lam ru rv (.ref rightDomain) rightCodomain rightBody).dependencyOrigin rf)
      (next.frame.dependencyEnvironment rf)).cost ≤
      (Closure.close ((EndpointState.lam ru rv (.ref rightDomain) rightCodomain rightBody).dependencyOrigin rf)
      (rightFrame.frame.dependencyEnvironment rf)).cost :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_left (nextBound rf) 1)
  have callBound : richSchedule .expressionReindex
      ((Closure.close (leftBody.dependencyOrigin lf) (leftChild.frame.dependencyEnvironment lf)).cost +
       (Closure.close (rightBody.dependencyOrigin rf) (rightChild.frame.dependencyEnvironment rf)).cost) <
      richSchedule .expressionReindex
      ((Closure.close ((EndpointState.lam lu lv (.ref leftDomain) leftCodomain leftBody).dependencyOrigin lf)
        (leftFrame.frame.dependencyEnvironment lf)).cost +
       (Closure.close ((EndpointState.lam ru rv (.ref rightDomain) rightCodomain rightBody).dependencyOrigin rf)
        (rightFrame.frame.dependencyEnvironment rf)).cost) := by
    rw [leftEnvironment lf, rightEnvironment rf]
    apply richSchedule_strict
    exact Nat.add_lt_add (binder_body_cost (by simp) _)
      (Nat.lt_of_lt_of_le (binder_body_cost (by simp) _) parentBound)
  have observation : RichObs leftEnv env U registry target leftBody (Locals.push leftLocals)
      (leftRaw.lift.comp (commonLeft.cons key.anchor)) (.singleton output) bodyFootprint := by
    simpa only [lift_comp] using query
  obtain ⟨reply⟩ := bodyR key leftChild leftGenerated (Valuation.push_atomized_closed leftClosed _)
    rightChild rightGenerated (Valuation.push_atomized_closed nextClosed _) callBound observation
    (pack.available_atomized_localNeeds resources)
  have bodyReply : BoundedGeneratedQueryReply base (commonCaps.push (Need.Fits key.input))
      (OriginalNestedDisplay.lambdaBody rightLocation rightInitial rightGraph rightAnnotation rightExpression)
      (commonLeft.cons key.anchor) (commonRight.cons key.anchor) (.singleton output)
      ((rightDomain.dependencyOrigin rf).weight * (1 + environmentCost (next.frame.dependencyEnvironment rf))) := by
    simpa only [rightEnvironment rf, generatedBinder_environmentCost] using reply
  obtain ⟨answer⟩ := boundedGeneratedLambdaReply rightLocation rightInitial rightGraph
    rightAnnotation rightExpression henv hscoped formed rf next nextCapped nextClosed
    domainCode domainResources key output rightGuard bodyReply
  exact ⟨⟨answer.answer, fun ordered => Nat.le_trans (answer.bounded ordered) (nextBound ordered)⟩⟩


include henv leftBelow rightBelow leftCapped leftClosed in
/-- Full lambda expression replay through all legacy/rich wrappers and its
retained original input prefix. Every native leaf uses the actual strictly
smaller domain/body pair; finite unions merge only after recursion. -/
theorem lambdaGeneratedQueryStep
    (rightFrame : OriginalCaptureRealization rightGraph env registry target
      rightLocals commonLeft commonRight rightAvailable)
    (rightCapped : CappedCaptureGenerated base commonCaps commonLeft commonRight rightGraph rightFrame.frame.raw)
    (rightClosed : rightAvailable.AtomClosed)
    (domainR : GeneratedObservationCall base commonCaps
      (OriginalNestedDisplay.lambdaDomain leftLocation leftInitial leftGraph leftAnnotation)
      (OriginalNestedDisplay.lambdaDomain rightLocation rightInitial rightGraph rightAnnotation)
      commonLeft commonRight lf rf
      (richSchedule .expressionReindex
        ((Closure.close ((EndpointState.lam lu lv (.ref leftDomain) leftCodomain leftBody).dependencyOrigin lf)
          (leftFrame.frame.dependencyEnvironment lf)).cost +
         (Closure.close ((EndpointState.lam ru rv (.ref rightDomain) rightCodomain rightBody).dependencyOrigin rf)
          (rightFrame.frame.dependencyEnvironment rf)).cost)))
    (bodyR : ∀ {n : Nat} (key : Key n), GeneratedObservationCall base (commonCaps.push (Need.Fits key.input))
      (OriginalNestedDisplay.lambdaBody leftLocation leftInitial leftGraph leftAnnotation leftExpression)
      (OriginalNestedDisplay.lambdaBody rightLocation rightInitial rightGraph rightAnnotation rightExpression)
      (commonLeft.cons key.anchor) (commonRight.cons key.anchor) lf rf
      (richSchedule .expressionReindex
        ((Closure.close ((EndpointState.lam lu lv (.ref leftDomain) leftCodomain leftBody).dependencyOrigin lf)
          (leftFrame.frame.dependencyEnvironment lf)).cost +
         (Closure.close ((EndpointState.lam ru rv (.ref rightDomain) rightCodomain rightBody).dependencyOrigin rf)
          (rightFrame.frame.dependencyEnvironment rf)).cost)))
    (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {node : EndpointState leftEnv U leftSource (.lam A b) assigned}
    (route : PrefixRoute leftEnv U leftSource (.lam A b) node
      (.lam lu lv (.ref leftDomain) leftCodomain leftBody))
    (query : RichObs leftEnv env U registry target node leftLocals
      (leftRaw.comp commonLeft) (profile : Profile n) footprint)
    (resources : footprint.Available leftAvailable) :
    Nonempty (BoundedGeneratedQueryReply base commonCaps
      (OriginalNestedDisplay.lambda rightLocation rightInitial rightGraph rightAnnotation rightExpression)
      commonLeft commonRight profile (environmentCost (rightFrame.frame.dependencyEnvironment rf))) := by
  apply query.replayCappedLambda henv hscoped formed
    (fun {n} => .empty _ rightFrame rightCapped rightClosed (fun _ => Nat.le_refl _))
    ?_ lu lv route resources
  intro n ambient key output domainFootprint bodyFootprint outside packed
    domainCode guard bodyQuery pack covered domainResources outsideResources
  exact nativeLambdaGeneratedQueryStep leftLocation rightLocation leftInitial rightInitial leftGraph rightGraph
    leftAnnotation rightAnnotation leftExpression rightExpression henv leftBelow rightBelow lf rf
    leftFrame leftCapped leftClosed rightFrame rightCapped rightClosed domainR bodyR hscoped formed
    domainCode guard bodyQuery pack covered domainResources outsideResources

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
