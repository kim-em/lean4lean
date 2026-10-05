import Lean4Lean.Theory.Typing.AnchoredOriginalGenericPiDisplays
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericPiObservationReindex

/-! Pi reindexing from actual common source displays. Each recursive R call
is a comparison of the two original child displays, with the real generic
frames and strictly smaller computed costs. Target equality is derived only
after retaining this source evidence. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

section
variable
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
  (leftInsertion : Ctx.Lift' leftMap leftSource displayed)
  (rightInsertion : Ctx.Lift' rightMap rightSource displayed)
  (leftAnnotation : annotation = A.lift' leftMap)
  (rightAnnotation : annotation = C.lift' rightMap)
  (leftExpression : displayedBody = B.lift' leftMap.cons)
  (rightExpression : displayedBody = D.lift' rightMap.cons)
  (henv : env.Ordered) (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
  (lf : leftEnv.Ordered) (rf : rightEnv.Ordered)

/-- The fixed body calls carry source-context insertions and actual original
locations on both sides. Arbitrary equality of realized bodies is not an
eligibility condition for the recursive theorem. -/
def OriginalPiDisplayBodyCalls
    (left : OriginalPiSide leftRoot leftInitial env registry target
      (leftLocation.contextDerivation leftInitial) leftDomain leftLocals
      (Subst.lift_l leftMap common) leftAvailable (ambient : Profile n))
    (right : OriginalPiSide rightRoot rightInitial env registry target
      (rightLocation.contextDerivation rightInitial) rightDomain rightLocals
      (Subst.lift_l rightMap common) rightAvailable ambient)
    (leftSubstitutions : Ctx.SubstEq env U target (Subst.lift_l leftMap common)
      (Subst.lift_l leftMap common) leftSource)
    (rightSubstitutions : Ctx.SubstEq env U target (Subst.lift_l rightMap common)
      (Subst.lift_l rightMap common) rightSource) (limit : Nat) : Prop :=
  ∀ (key : Key n)
    (guard : LambdaGuard env U registry target (Subst.lift_l leftMap common) A key ambient)
    (rightGuard : LambdaGuard env U registry target (Subst.lift_l rightMap common) C key ambient)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms),
    let leftChild := left.displayBodyFits henv leftBelow leftLocation leftInitial rfl
      leftInsertion leftAnnotation leftExpression leftSubstitutions guard needs bounded covered
    let rightChild := right.displayBodyFits henv rightBelow rightLocation rightInitial rfl
      rightInsertion rightAnnotation rightExpression rightSubstitutions rightGuard needs bounded covered
    richSchedule .expressionReindex (leftChild.cost lf + rightChild.cost rf) < limit →
    OriginalRichDisplayReindex leftChild rightChild

/-- Convert the syntactic child-display calls into the local row worker's
fixed-endpoint interface. The conversion preserves each computed closure. -/
theorem OriginalPiDisplayBodyCalls.rows
    (left : OriginalPiSide leftRoot leftInitial env registry target
      (leftLocation.contextDerivation leftInitial) leftDomain leftLocals
      (Subst.lift_l leftMap common) leftAvailable (ambient : Profile n))
    (right : OriginalPiSide rightRoot rightInitial env registry target
      (rightLocation.contextDerivation rightInitial) rightDomain rightLocals
      (Subst.lift_l rightMap common) rightAvailable ambient)
    (leftSubstitutions : Ctx.SubstEq env U target (Subst.lift_l leftMap common)
      (Subst.lift_l leftMap common) leftSource)
    (rightSubstitutions : Ctx.SubstEq env U target (Subst.lift_l rightMap common)
      (Subst.lift_l rightMap common) rightSource)
    (calls : OriginalPiDisplayBodyCalls leftLocation rightLocation leftInitial rightInitial
      leftInsertion rightInsertion leftAnnotation rightAnnotation leftExpression rightExpression
      henv leftBelow rightBelow lf rf left right leftSubstitutions rightSubstitutions
      (richSchedule .expressionReindex
        ((Closure.close (.binder (leftDomain.dependencyOrigin lf) [leftBody.dependencyOrigin lf] [])
          (left.frame.dependencyEnvironment lf)).cost +
         (Closure.close (.binder (rightDomain.dependencyOrigin rf) [rightBody.dependencyOrigin rf] [])
          (right.frame.dependencyEnvironment rf)).cost))) :
    OriginalPiBodyReindex henv lf rf left right leftBody rightBody relevant := by
  intro key output guard rightGuard needs bounded covered bound _same footprint certificate resources
  have displayBound : richSchedule .expressionReindex
      ((left.displayBodyFits henv leftBelow leftLocation leftInitial rfl leftInsertion leftAnnotation
        leftExpression leftSubstitutions guard needs bounded covered).cost lf +
       (right.displayBodyFits henv rightBelow rightLocation rightInitial rfl rightInsertion rightAnnotation
        rightExpression rightSubstitutions rightGuard needs bounded covered).cost rf) <
      richSchedule .expressionReindex
        ((Closure.close (.binder (leftDomain.dependencyOrigin lf) [leftBody.dependencyOrigin lf] [])
          (left.frame.dependencyEnvironment lf)).cost +
         (Closure.close (.binder (rightDomain.dependencyOrigin rf) [rightBody.dependencyOrigin rf] [])
          (right.frame.dependencyEnvironment rf)).cost) := by
    simpa only [OriginalRichDisplayFrame.cost, OriginalPiSide.displayBodyFits,
      Located.piBodyDisplayAs, OriginalPiSide.displayBodyFrame_environment] using bound
  have replay : RichCodeTransfer env U registry target leftBody rightBody (Locals.push leftLocals)
      (Locals.push rightLocals) (Subst.lift_l leftMap.cons (common.cons key.anchor))
      (Subst.lift_l rightMap.cons (common.cons key.anchor)) (leftAvailable.push needs)
      (rightAvailable.push needs) := calls key guard rightGuard needs bounded covered displayBound rfl rfl
  have leftRealization : Subst.lift_l leftMap.cons (common.cons key.anchor) =
      (Subst.lift_l leftMap common).cons key.anchor := by funext i; cases i <;> rfl
  have rightRealization : Subst.lift_l rightMap.cons (common.cons key.anchor) =
      (Subst.lift_l rightMap common).cons key.anchor := by funext i; cases i <;> rfl
  change RichCodeTransfer env U registry target leftBody rightBody (Locals.push leftLocals)
    (Locals.push rightLocals) (Subst.lift_l leftMap.cons (common.cons key.anchor))
    (Subst.lift_l rightMap.cons (common.cons key.anchor)) (leftAvailable.push needs)
    (rightAvailable.push needs) at replay
  rw [leftRealization, rightRealization] at replay
  exact replay certificate resources

/-- Full rich Pi R at ordinary source displays, including all incoming
query actions, supports and empty row tables. The only binary induction
hypotheses name the actual domain/body displays constructed above. -/
theorem OriginalRichDisplayFrame.nativePiReindex
    (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (leftFrame : OriginalRichDisplayFrame env registry target
      (leftLocation.piDisplayAs leftInitial leftInsertion leftAnnotation leftExpression)
      common leftLocals leftAvailable)
    (rightFrame : OriginalRichDisplayFrame env registry target
      (rightLocation.piDisplayAs rightInitial rightInsertion rightAnnotation rightExpression)
      common rightLocals rightAvailable)
    (leftClosed : leftAvailable.AtomClosed)
    (sourceF : OriginalCodeInductionAt env registry lf leftInitial leftLocation
      (leftFrame.cost lf + rightFrame.cost rf))
    (domainR :
      richSchedule .expressionReindex
        ((leftFrame.piDomain leftLocation leftInitial leftInsertion leftAnnotation leftExpression).cost lf +
         (rightFrame.piDomain rightLocation rightInitial rightInsertion rightAnnotation rightExpression).cost rf) <
      richSchedule .expressionReindex (leftFrame.cost lf + rightFrame.cost rf) →
      OriginalRichDisplayReindex
        (leftFrame.piDomain leftLocation leftInitial leftInsertion leftAnnotation leftExpression)
        (rightFrame.piDomain rightLocation rightInitial rightInsertion rightAnnotation rightExpression))
    (bodyR : ∀ {n : Nat} {ambient : Profile n} {footprint : Footprint}
      (leftCode : RichCert leftEnv env U registry target (.ref leftDomain) leftLocals
        (Subst.lift_l leftMap common) true ambient footprint)
      (resources : footprint.Available leftAvailable)
      (answer : RichCodeTransferResult env U registry target (.ref leftDomain) (.ref rightDomain)
        rightLocals (Subst.lift_l leftMap common) (Subst.lift_l rightMap common) rightAvailable true ambient),
      OriginalPiDisplayBodyCalls leftLocation rightLocation leftInitial rightInitial
        leftInsertion rightInsertion leftAnnotation rightAnnotation leftExpression rightExpression
        henv leftBelow rightBelow lf rf
        ⟨leftFrame.frame, .piDomain leftLocation, rfl, footprint, leftCode, resources⟩
        ⟨rightFrame.frame, .piDomain rightLocation, rfl, answer.footprint, answer.certificate, answer.resources⟩
        leftFrame.substitutions rightFrame.substitutions
        (richSchedule .expressionReindex (leftFrame.cost lf + rightFrame.cost rf))) :
    OriginalRichDisplayReindex leftFrame rightFrame := by
  intro leftLevel rightLevel leftSort rightSort
  change VExpr.sort (.imax u v) = .sort leftLevel at leftSort
  change VExpr.sort (.imax u' v') = .sort rightLevel at rightSort
  cases leftSort
  cases rightSort
  have equal := (pi_display_realizations leftInsertion rightInsertion leftAnnotation rightAnnotation
    leftExpression rightExpression common).1
  intro relevant n profile footprint query resources
  apply OriginalRichFrame.piReindexStep henv hscoped formed lf rf leftFrame.frame
    (.piDomain leftLocation) rfl rightFrame.frame (.piDomain rightLocation) rfl
    leftBody rightBody lu lv ru rv (.done _) (.done _) equal ?_ ?_
    leftClosed leftFrame.substitutions leftLocation rfl sourceF query resources
  · intro bound _equal
    exact domainR bound rfl rfl
  · intro m ambient outputRelevant domainFootprint leftCode leftResources answer
    exact OriginalPiDisplayBodyCalls.rows leftLocation rightLocation leftInitial rightInitial
      leftInsertion rightInsertion leftAnnotation rightAnnotation leftExpression rightExpression
      henv leftBelow rightBelow lf rf
      ⟨leftFrame.frame, .piDomain leftLocation, rfl, domainFootprint, leftCode, leftResources⟩
      ⟨rightFrame.frame, .piDomain rightLocation, rfl, answer.footprint, answer.certificate, answer.resources⟩
      leftFrame.substitutions rightFrame.substitutions (bodyR leftCode leftResources answer)

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
