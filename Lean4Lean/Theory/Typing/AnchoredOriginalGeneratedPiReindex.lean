import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedPiDisplays
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericPiObservationReindex

/-! Pi R for recursively captured source displays. The recursive body
comparisons extend actual generated graphs with the same raw common binder. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

private theorem lift_comp (raw realization : Subst) (anchor : VExpr) :
    raw.lift.comp (realization.cons anchor) = (raw.comp realization).cons anchor := by
  funext index
  cases index <;> simp [Subst.comp, Subst.lift, Subst.cons, lift_subst_cons]

section
variable
  {base : OriginalCaptureBase env U registry target}
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
  (leftFrame : OriginalGeneratedDisplayFrame base
    (OriginalNestedDisplay.pi leftLocation leftInitial leftGraph leftAnnotation leftExpression)
    realization leftLocals leftAvailable)
  (rightFrame : OriginalGeneratedDisplayFrame base
    (OriginalNestedDisplay.pi rightLocation rightInitial rightGraph rightAnnotation rightExpression)
    realization rightLocals rightAvailable)

/-- The recursive obligations expose the actual graphs and generated frames
of both bodies, not merely equality after target substitution. -/
def OriginalGeneratedPiBodyCalls
    (leftCode : RichCert leftEnv env U registry target (.ref leftDomain) leftLocals
      (leftRaw.comp realization) true (ambient : Profile n) footprint)
    (resources : footprint.Available leftAvailable)
    (answer : RichCodeTransferResult env U registry target (.ref leftDomain) (.ref rightDomain)
      rightLocals (leftRaw.comp realization) (rightRaw.comp realization) rightAvailable true ambient)
    (limit : Nat) : Prop :=
  ∀ (key : Key n)
    (guard : LambdaGuard env U registry target (leftRaw.comp realization) A key ambient)
    (rightGuard : LambdaGuard env U registry target (rightRaw.comp realization) C key ambient)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms),
    let leftChild := leftFrame.piBody leftLocation leftInitial leftGraph leftAnnotation leftExpression
      henv leftBelow leftCode resources guard needs bounded covered
    let rightChild := rightFrame.piBody rightLocation rightInitial rightGraph rightAnnotation rightExpression
      henv rightBelow answer.certificate answer.resources rightGuard needs bounded covered
    richSchedule .expressionReindex (leftChild.cost lf + rightChild.cost rf) < limit →
    OriginalGeneratedDisplayReindex leftChild rightChild

theorem OriginalGeneratedPiBodyCalls.rows
    (leftCode : RichCert leftEnv env U registry target (.ref leftDomain) leftLocals
      (leftRaw.comp realization) true (ambient : Profile n) footprint)
    (resources : footprint.Available leftAvailable)
    (answer : RichCodeTransferResult env U registry target (.ref leftDomain) (.ref rightDomain)
      rightLocals (leftRaw.comp realization) (rightRaw.comp realization) rightAvailable true ambient)
    (calls : OriginalGeneratedPiBodyCalls leftLocation rightLocation leftInitial rightInitial
      leftGraph rightGraph leftAnnotation rightAnnotation leftExpression rightExpression
      henv leftBelow rightBelow lf rf leftFrame rightFrame leftCode resources answer
      (richSchedule .expressionReindex (leftFrame.cost lf + rightFrame.cost rf))) :
    OriginalPiBodyReindex henv lf rf
      ⟨leftFrame.capture.frame, .piDomain leftLocation, rfl, footprint, leftCode, resources⟩
      ⟨rightFrame.capture.frame, .piDomain rightLocation, rfl,
        answer.footprint, answer.certificate, answer.resources⟩
      leftBody rightBody relevant := by
  intro key output guard rightGuard needs bounded covered bound _same required certificate available
  have childBound : richSchedule .expressionReindex
      ((leftFrame.piBody leftLocation leftInitial leftGraph leftAnnotation leftExpression
        henv leftBelow leftCode resources guard needs bounded covered).cost lf +
       (rightFrame.piBody rightLocation rightInitial rightGraph rightAnnotation rightExpression
        henv rightBelow answer.certificate answer.resources rightGuard needs bounded covered).cost rf) <
      richSchedule .expressionReindex (leftFrame.cost lf + rightFrame.cost rf) := by
    simp only [OriginalGeneratedDisplayFrame.cost, OriginalGeneratedDisplayFrame.piBody_environment]
    exact bound
  have replay : RichCodeTransfer env U registry target leftBody rightBody (Locals.push leftLocals)
      (Locals.push rightLocals) (leftRaw.lift.comp (realization.cons key.anchor))
      (rightRaw.lift.comp (realization.cons key.anchor)) (leftAvailable.push needs)
      (rightAvailable.push needs) :=
    calls key guard rightGuard needs bounded covered childBound rfl rfl
  rw [lift_comp, lift_comp] at replay
  exact replay certificate available

/-- Full rich Pi R at recursively generated source displays, preserving all
query actions and rows. Domain/body calls use actual smaller generated
children; no typing of the raw common context is required. -/
theorem OriginalGeneratedDisplayFrame.nativePiReindex
    (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (leftClosed : leftAvailable.AtomClosed)
    (sourceF : OriginalCodeInductionAt env registry lf leftInitial leftLocation
      (leftFrame.cost lf + rightFrame.cost rf))
    (domainR :
      richSchedule .expressionReindex
        ((leftFrame.piDomain leftLocation leftInitial leftGraph leftAnnotation leftExpression).cost lf +
         (rightFrame.piDomain rightLocation rightInitial rightGraph rightAnnotation rightExpression).cost rf) <
      richSchedule .expressionReindex (leftFrame.cost lf + rightFrame.cost rf) →
      OriginalGeneratedDisplayReindex
        (leftFrame.piDomain leftLocation leftInitial leftGraph leftAnnotation leftExpression)
        (rightFrame.piDomain rightLocation rightInitial rightGraph rightAnnotation rightExpression))
    (bodyR : ∀ {n : Nat} {ambient : Profile n} {footprint : Footprint}
      (leftCode : RichCert leftEnv env U registry target (.ref leftDomain) leftLocals
        (leftRaw.comp realization) true ambient footprint)
      (resources : footprint.Available leftAvailable)
      (answer : RichCodeTransferResult env U registry target (.ref leftDomain) (.ref rightDomain)
        rightLocals (leftRaw.comp realization) (rightRaw.comp realization) rightAvailable true ambient),
      OriginalGeneratedPiBodyCalls leftLocation rightLocation leftInitial rightInitial
        leftGraph rightGraph leftAnnotation rightAnnotation leftExpression rightExpression
        henv leftBelow rightBelow lf rf leftFrame rightFrame leftCode resources answer
        (richSchedule .expressionReindex (leftFrame.cost lf + rightFrame.cost rf))) :
    OriginalGeneratedDisplayReindex leftFrame rightFrame := by
  intro leftLevel rightLevel leftSort rightSort
  change VExpr.sort (.imax u v) = .sort leftLevel at leftSort
  change VExpr.sort (.imax u' v') = .sort rightLevel at rightSort
  cases leftSort
  cases rightSort
  have sameSource : (VExpr.forallE A B).subst leftRaw = (VExpr.forallE C D).subst rightRaw := by
    simp only [subst, ← leftAnnotation, ← rightAnnotation, ← leftExpression, ← rightExpression]
  have equal := congrArg (fun expression => expression.subst realization) sameSource
  simp only [subst_subst] at equal
  intro relevant n profile footprint query resources
  apply OriginalRichFrame.piReindexStep henv hscoped formed lf rf leftFrame.capture.frame
    (.piDomain leftLocation) rfl rightFrame.capture.frame (.piDomain rightLocation) rfl
    leftBody rightBody lu lv ru rv (.done _) (.done _) equal ?_ ?_
    leftClosed leftFrame.capture.substitutions leftLocation rfl sourceF query resources
  · intro bound _equal
    exact domainR bound rfl rfl
  · intro m ambient outputRelevant domainFootprint leftCode leftResources answer
    exact OriginalGeneratedPiBodyCalls.rows leftLocation rightLocation leftInitial rightInitial
      leftGraph rightGraph leftAnnotation rightAnnotation leftExpression rightExpression
      henv leftBelow rightBelow lf rf leftFrame rightFrame leftCode leftResources answer
      (bodyR leftCode leftResources answer)
end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
