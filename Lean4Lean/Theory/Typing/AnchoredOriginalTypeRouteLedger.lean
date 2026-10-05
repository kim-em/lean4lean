import Lean4Lean.Theory.Typing.AnchoredOriginalRawParameterTypeRoute
import Lean4Lean.Theory.Typing.AnchoredOriginalParameterRouteLedger

/-! Connect the retained original alignment history to the repeated-slot
ledger. Every charge is indexed by the exact endpoint closures and actual
frame environments appearing in that history, including assigned-C edges.
No bound for an unrelated environment can stand in for this evidence. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail OriginalEndpointFactor.Dependency
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target common : List VExpr}

/-- Increasing the prefix index retains the very same original occurrences
and environments. Only the already proved ledger index is widened. -/
def _root_.Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.Dependency.ParameterRouteCharge.widen
    (charge : ParameterRouteCharge sources initial count closure) (bound : count ≤ next) :
    ParameterRouteCharge sources initial next closure := by
  cases charge with
  | reindex left right leftFrame rightFrame =>
    exact .reindex left right (leftFrame.widen bound) (rightFrame.widen bound)
  | ownerPair left right leftEnvironment rightEnvironment leftBound rightBound =>
    exact .ownerPair left right leftEnvironment rightEnvironment leftBound rightBound
  | ownerReindex owner ownerEnvironment bounded right rightFrame =>
    exact .ownerReindex owner ownerEnvironment bounded right (rightFrame.widen bound)
  | equality equality frame => exact .equality equality (frame.widen bound)

def _root_.Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.Dependency.ParameterRouteCharges.widen
    (charges : ParameterRouteCharges sources initial count reserve) (bound : count ≤ next) :
    ParameterRouteCharges sources initial next reserve := by
  match charges with
  | .nil => exact .nil
  | .cons head tail => exact .cons (head.widen bound) (tail.widen bound)
termination_by sizeOf charges

noncomputable def RawGeneratedTypeRoute.Charged
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right first last)
    (sources : ParameterRouteSources ledgerEnv U) (initial : List Closure) (count : Nat) : Type :=
  match route with
  | .identity .. => PUnit
  | .same left right lf rf previous frame =>
      ParameterRouteCharge sources initial count
        (.bundle (.close (left.node.dependencyOrigin lf) previous)
          (.close (right.node.dependencyOrigin rf) (frame.realization.frame.dependencyEnvironment rf)))
  | .assigned left right lf rf previous frame =>
      ParameterRouteCharge sources initial count
        (.bundle (.close (left.node.dependencyOrigin lf) previous)
          (.close (right.node.dependencyOrigin rf) (frame.realization.frame.dependencyEnvironment rf)))
  | .equality _ original _ ordered _ previous =>
      ParameterRouteCharge sources initial count (.close (original.dependencyOrigin ordered) previous)
  | .typedEquality (original := original) (left := left) (leftOrdered := lf)
      (ordered := ordered) (environment := previous) (frame := frame) .. =>
      let equality := Closure.close (original.dependencyOrigin ordered)
        (frame.realization.frame.dependencyEnvironment ordered)
      ParameterRouteCharge sources initial count
        (.bundle (.close (left.node.dependencyOrigin lf) previous) equality) ×
      ParameterRouteCharge sources initial count equality
  | .trans first second => first.Charged sources initial count × second.Charged sources initial count
  | .piDomain _ _ _ route => route.Charged sources initial count
  | .applyPi (domain := domain) (body := body) (function := function) (argument := argument)
      (result := result) (hu := hu) (hv := hv) (headerDomain := headerDomain) (headerBody := headerBody)
      (hcu := hcu) (hdv := hdv) (sourceOrdered := sourceOrdered) (headerOrdered := headerOrdered)
      (sourceFrame := sourceFrame) (headerFrame := headerFrame) (whole := whole) .. =>
      let application := Closure.close
        ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin sourceOrdered)
        (sourceFrame.realization.frame.dependencyEnvironment sourceOrdered)
      let header := Closure.close
        ((EndpointState.pi hcu hdv (.ref headerDomain) headerBody).dependencyOrigin headerOrdered)
        (headerFrame.realization.frame.dependencyEnvironment headerOrdered)
      whole.Charged sources initial count ×
        ParameterRouteCharge sources initial count (.bundle application application) ×
        ParameterRouteCharge sources initial count (.bundle header header)
termination_by sizeOf route

/-- The reserve used by replay is exactly the finite ledger being bounded,
not merely a larger numerical budget supplied by a caller. -/
noncomputable def RawGeneratedTypeRoute.chargedReserve
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right first last)
    (charged : route.Charged sources initial count) :
    ParameterRouteCharges sources initial count route.reserve := by
  match route with
  | .identity .. => rw [reserve.eq_def]; exact .nil
  | .same .. =>
    rw [reserve.eq_def]
    exact .cons (by rw [Charged.eq_def] at charged; exact charged) .nil
  | .assigned .. =>
    rw [reserve.eq_def]
    exact .cons (by rw [Charged.eq_def] at charged; exact charged) .nil
  | .equality .. =>
    rw [reserve.eq_def]
    exact .cons (by rw [Charged.eq_def] at charged; exact charged) .nil
  | .typedEquality .. =>
    rw [Charged.eq_def] at charged
    rw [reserve.eq_def]
    exact .cons charged.1 (.cons charged.2 .nil)
  | .trans first second =>
    rw [Charged.eq_def] at charged
    rw [reserve.eq_def]
    exact (first.chargedReserve charged.1).append (second.chargedReserve charged.2)
  | .piDomain _ _ _ route =>
    rw [Charged.eq_def] at charged
    rw [reserve.eq_def]
    exact route.chargedReserve charged
  | .applyPi (whole := whole) .. =>
    rw [Charged.eq_def] at charged
    rw [reserve.eq_def]
    exact (whole.chargedReserve charged.1).append
      (.cons charged.2.1 (.cons charged.2.2 .nil))
termination_by sizeOf route

/-- A later prefix can reuse every earlier finite route charge. Original
endpoints, source environments and reserves are all retained unchanged. -/
noncomputable def RawGeneratedTypeRoute.widenCharged
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right first last)
    (charged : route.Charged sources initial count) (bound : count ≤ next) :
    route.Charged sources initial next := by
  match route with
  | .identity .. => rw [Charged.eq_def]; exact PUnit.unit
  | .same .. | .assigned .. | .equality .. =>
    rw [Charged.eq_def] at charged ⊢
    exact charged.widen bound
  | .typedEquality .. =>
    rw [Charged.eq_def] at charged ⊢
    exact ⟨charged.1.widen bound, charged.2.widen bound⟩
  | .trans first second =>
    rw [Charged.eq_def] at charged ⊢
    exact ⟨first.widenCharged charged.1 bound, second.widenCharged charged.2 bound⟩
  | .piDomain _ _ _ child =>
    rw [Charged.eq_def] at charged ⊢
    exact child.widenCharged charged bound
  | .applyPi (whole := whole) .. =>
    rw [Charged.eq_def] at charged ⊢
    exact ⟨whole.widenCharged charged.1 bound, charged.2.1.widen bound, charged.2.2.widen bound⟩
termination_by sizeOf route

theorem RawGeneratedTypeRoute.charged_schedule_bound
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right first last)
    (charged : route.Charged sources initial count) :
    route.schedule ≤ richSchedule .expressionReindex
      (2 * sources.weight * parameterRouteCapacity sources count initial) := by
  have bound := (route.chargedReserve charged).bound
  exact Nat.le_trans route.schedule_le (by
    change 3 * _ + 2 ≤ 3 * _ + 2
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 3 bound) 2)

/-- Query selection may change the closure list. Its proved non-growth
transports the existing ledger to that actual list; the baseline is never
identified with the selected frame by definitional equality. -/
noncomputable def BoundedGeneratedQueryReply.parameterLedger
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    (reply : BoundedGeneratedQueryReply base commonCaps display commonLeft commonRight requested
      (environmentCost baseline))
    (ledger : ParameterRouteLedger sources initial count baseline)
    (ordered : display.sourceEnv.Ordered) :
    ParameterRouteLedger sources initial count
      (reply.answer.reply.realization.frame.dependencyEnvironment ordered) :=
  .bounded ledger _ (reply.bounded ordered)

section
variable
    {env familyEnv baseEnv typesEnv ctorEnv : VEnv} {U : Nat}
    {registry : CanonicalHead.Registry} {target common : List VExpr}
    {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
    {familyContext : ContextDerivation familyEnv U familySource}
    {seedContext universeContext : ContextDerivation baseEnv U seedSource}
    {requestedContext : ContextDerivation typesEnv U requestedSource}
    {ctorContext : ContextDerivation ctorEnv U ctorSource}
    (familyGraph : OriginalCaptureMap (common := common) familyContext raw)
    (seedGraph : OriginalCaptureMap (common := common) seedContext raw)
    (universeGraph : OriginalCaptureMap (common := common) universeContext raw)
    (requestedGraph : OriginalCaptureMap (common := common) requestedContext raw)
    (ctorGraph : OriginalCaptureMap (common := common) ctorContext raw)
    (family : EndpointRef familyEnv U familySource familyDomain (.sort familyLevel))
    (familyProvenance : EndpointProvenance familyContext (.ref family))
    (familyCell : Derivation baseEnv U seedSource seedDomain familyDomain (.sort familySort))
    (universeCell : Derivation baseEnv U seedSource seedDomain requestedDomain (.sort universeSort))
    (ctorCell : Derivation typesEnv U requestedSource requestedDomain ctorDomain (.sort ctorSort))
    (constructor : EndpointRef ctorEnv U ctorSource ctorDomain (.sort ctorLevel))
    (ctorProvenance : EndpointProvenance ctorContext (.ref constructor))
    (familyOrdered : familyEnv.Ordered) (baseOrdered : baseEnv.Ordered)
    (typesOrdered : typesEnv.Ordered) (ctorOrdered : ctorEnv.Ordered)
    (baseBelow : baseEnv ≤ env) (typesBelow : typesEnv ≤ env)
    (initial : List Closure)
    (seedFrame : ParameterReplyFrame base commonCaps seedGraph commonLeft commonRight)
    (universeFrame : ParameterReplyFrame base commonCaps universeGraph commonLeft commonRight)
    (requestedFrame : ParameterReplyFrame base commonCaps requestedGraph commonLeft commonRight)
    (ctorFrame : ParameterReplyFrame base commonCaps ctorGraph commonLeft commonRight)


    (sources : ParameterRouteSources ledgerEnv U) (ownerInitial : List Closure) (count : Nat)
    (familyOccurrence : ParameterRouteOccurrence sources familyOrdered (.ref family))
    (familyLeft : ParameterRouteOccurrence sources baseOrdered (.ref (.left familyCell)))
    (familyRight : ParameterRouteOccurrence sources baseOrdered (.ref (.right familyCell)))
    (universeLeft : ParameterRouteOccurrence sources baseOrdered (.ref (.left universeCell)))
    (universeRight : ParameterRouteOccurrence sources baseOrdered (.ref (.right universeCell)))
    (ctorLeft : ParameterRouteOccurrence sources typesOrdered (.ref (.left ctorCell)))
    (ctorRight : ParameterRouteOccurrence sources typesOrdered (.ref (.right ctorCell)))
    (ctorOccurrence : ParameterRouteOccurrence sources ctorOrdered (.ref constructor))
    (incomingLedger : ParameterRouteLedger sources ownerInitial count initial)
    (seedLedger : ParameterRouteLedger sources ownerInitial count
      (seedFrame.realization.frame.dependencyEnvironment baseOrdered))
    (universeLedger : ParameterRouteLedger sources ownerInitial count
      (universeFrame.realization.frame.dependencyEnvironment baseOrdered))
    (requestedLedger : ParameterRouteLedger sources ownerInitial count
      (requestedFrame.realization.frame.dependencyEnvironment typesOrdered))
    (ctorLedger : ParameterRouteLedger sources ownerInitial count
      (ctorFrame.realization.frame.dependencyEnvironment ctorOrdered))

/-- The concrete seven-leg history is charged by its actual original
occurrences and five existing prefix ledgers. The three equality reserves
name the exact retained derivations, including when they are descendants
of a declaration equality root. -/
noncomputable def rawParameterCellsTypeRoute_charged :
    (rawParameterCellsTypeRoute familyGraph seedGraph universeGraph requestedGraph ctorGraph
      family familyProvenance familyCell universeCell ctorCell constructor ctorProvenance
      familyOrdered baseOrdered typesOrdered ctorOrdered baseBelow typesBelow initial
      seedFrame universeFrame requestedFrame ctorFrame).Charged sources ownerInitial count := by
  simp only [rawParameterCellsTypeRoute, RawGeneratedTypeRoute.Charged.eq_def]
  exact ⟨.reindex familyOccurrence familyRight incomingLedger seedLedger,
    .equality ⟨baseEnv, baseOrdered, seedSource, seedDomain, familyDomain, .sort familySort,
      familyCell, familyLeft⟩ seedLedger,
    .reindex familyLeft universeLeft seedLedger universeLedger,
    .equality ⟨baseEnv, baseOrdered, seedSource, seedDomain, requestedDomain, .sort universeSort,
      universeCell, universeLeft⟩ universeLedger,
    .reindex universeRight ctorLeft universeLedger requestedLedger,
    .equality ⟨typesEnv, typesOrdered, requestedSource, requestedDomain, ctorDomain, .sort ctorSort,
      ctorCell, ctorLeft⟩ requestedLedger,
    .reindex ctorRight ctorOccurrence requestedLedger ctorLedger⟩

end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
