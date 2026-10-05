import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiHistory
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionRouteSchedule

/-! A dependent prefixLedger successor adds one actual capture slot. The whole
previous history and both parent formation calls are paid by the existing
width-two parameter ledger; no new scalar reserve is assumed. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail OriginalEndpointFactor.Dependency
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

variable {U : Nat} {common : List VExpr}
  {left : OriginalApplicationTypeRouteSide U common}
  {right : OriginalPiTypeRouteSide U common}

noncomputable def _root_.Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.Dependency.ParameterRouteOccurrence.captureDomain
    (occurrence : ParameterRouteOccurrence sources ordered node) : ParameterRouteDomain sources :=
  match occurrence with
  | .seed selected => .seed selected.domain
  | .requested selected => .requested selected.domain

theorem _root_.Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.Dependency.ParameterRouteOccurrence.captureDomain_weight
    (occurrence : ParameterRouteOccurrence sources ordered node) :
    (node.dependencyOrigin ordered).weight ≤ occurrence.captureDomain.origin.weight := by
  cases occurrence with
  | seed selected => exact selected.weight_le
  | requested selected => exact selected.weight_le

/-- The live frame closes the selected domain itself, even when the ledger
bank retains the larger original equality root containing that domain. -/
noncomputable def actualParameterRouteStepEnvironment
    (sources : ParameterRouteSources ledgerEnv U) (domain : Origin)
    (owners : List sources.Owner) (previous reserve initial : List Closure) : List Closure :=
  let declared := Closure.close domain previous
  reserve ++ (declared :: (owners.map (fun owner => Closure.bundle (groupedOwnerClosure owner initial) declared) ++ previous))

private theorem environment_append (first second : List Closure) :
    environmentCost (first ++ second) = max (environmentCost first) (environmentCost second) := by
  induction first with
  | nil => simp [environmentCost]
  | cons head tail ih => simp only [List.cons_append, environmentCost, ih, Nat.max_assoc]

theorem _root_.Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.Dependency.ParameterRouteOccurrence.actualStep_bound
    (occurrence : ParameterRouteOccurrence sources ordered node)
    (owners : List sources.Owner) (previous reserve initial : List Closure) :
    environmentCost (actualParameterRouteStepEnvironment sources (node.dependencyOrigin ordered)
      owners previous reserve initial) ≤
    environmentCost (parameterRouteStepEnvironment sources occurrence.captureDomain
      owners previous reserve initial) := by
  have declared : (Closure.close (node.dependencyOrigin ordered) previous).cost ≤
      (Closure.close occurrence.captureDomain.origin previous).cost :=
    Nat.mul_le_mul_right _ occurrence.captureDomain_weight
  simp only [Closure.cost] at declared
  have mapped : environmentCost (owners.map (fun owner => Closure.bundle
      (groupedOwnerClosure owner initial) (.close (node.dependencyOrigin ordered) previous)) ++ previous) ≤
      environmentCost (owners.map (fun owner => Closure.bundle
        (groupedOwnerClosure owner initial) (.close occurrence.captureDomain.origin previous)) ++ previous) := by
    induction owners with
    | nil => exact Nat.le_refl _
    | cons owner owners ih =>
      simp only [List.map_cons, List.cons_append, environmentCost, Closure.cost]
      omega
  simp only [actualParameterRouteStepEnvironment, parameterRouteStepEnvironment,
    environment_append, environmentCost, Closure.cost]
  simp only [environment_append] at mapped
  omega

noncomputable def OriginalApplyPiHistory.reserveCharged
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight left right)
    (sources : ParameterRouteSources left.sourceEnv U) (initial : List Closure)
    (whole : history.whole.Charged sources initial count)
    (application : ParameterRouteOwnerOccurrence sources left.node)
    (sourceBound : environmentCost
        (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered) ≤
      environmentCost (application.environment initial))
    (header : ParameterRouteOccurrence sources history.rightOrdered right.display.node)
    (prefixLedger : ParameterRouteLedger sources initial count history.final) :
    ParameterRouteCharges sources initial count history.reserve := by
  apply (history.whole.chargedReserve whole).append
  exact .cons (.ownerPair application application _ _ sourceBound sourceBound)
    (.cons (.reindex header header prefixLedger prefixLedger) .nil)

noncomputable def OriginalApplicationTypeRouteSide.argumentFormationOccurrence
    (sources : ParameterRouteSources left.sourceEnv U)
    (application : ParameterRouteOwnerOccurrence sources left.node) :
    ParameterRouteOwnerOccurrence sources left.argumentDisplay.formationDisplay.node := by
  cases application with
  | field location => exact .field (.assignedFormation (.appArgument location))
  | major location => exact .major (.assignedFormation (.appArgument location))

noncomputable def OriginalApplicationTypeRouteSide.domainOccurrence
    (sources : ParameterRouteSources left.sourceEnv U)
    (application : ParameterRouteOwnerOccurrence sources left.node) :
    ParameterRouteOwnerOccurrence sources left.pi.domainDisplay.node := by
  cases application with
  | field location => exact .field (.appDomain location)
  | major location => exact .major (.appDomain location)

private noncomputable def chargeTrans
    {firstDisplay : OriginalNestedDisplay U common e A}
    {middleDisplay : OriginalNestedDisplay U common e' A'}
    {lastDisplay : OriginalNestedDisplay U common e'' A''}
    (first : RawGeneratedTypeRoute env registry target commonLeft commonRight firstDisplay middleDisplay firstEnv middleEnv)
    (second : RawGeneratedTypeRoute env registry target commonLeft commonRight middleDisplay lastDisplay middleEnv lastEnv)
    (firstCharge : first.Charged sources initial count)
    (secondCharge : second.Charged sources initial count) :
    (first.trans second).Charged sources initial count := by
  rw [RawGeneratedTypeRoute.Charged.eq_def]
  exact ⟨firstCharge, secondCharge⟩

private noncomputable def chargeSame
    (first : OriginalNestedDisplay U common e A)
    (last : OriginalNestedDisplay U common e A')
    (firstOrdered : first.sourceEnv.Ordered) (lastOrdered : last.sourceEnv.Ordered)
    (initialEnv : List Closure)
    (frame : OriginalTypeRouteFrame env registry target last.graph commonLeft commonRight)
    (paid : ParameterRouteCharge sources initial count
      (.bundle (.close (first.node.dependencyOrigin firstOrdered) initialEnv)
        (.close (last.node.dependencyOrigin lastOrdered) (frame.realization.frame.dependencyEnvironment lastOrdered)))) :
    (RawGeneratedTypeRoute.same first last firstOrdered lastOrdered initialEnv frame).Charged sources initial count := by
  rw [RawGeneratedTypeRoute.Charged.eq_def]
  exact paid

private noncomputable def chargeDomain
    (first last : OriginalPiTypeRouteSide U common) (below : first.sourceEnv ≤ env)
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight first.display last.display firstEnv lastEnv)
    (paid : route.Charged sources initial count) :
    (RawGeneratedTypeRoute.piDomain first last below route).Charged sources initial count := by
  rw [RawGeneratedTypeRoute.Charged.eq_def]
  exact paid

/-- The next seed's domain history uses only two original application
children and the domain projection of the previous whole-Pi history. -/
noncomputable def OriginalApplyPiHistory.argumentDomainRoute_charged
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight left right)
    (sources : ParameterRouteSources left.sourceEnv U) (initial : List Closure)
    (whole : history.whole.Charged sources initial count)
    (application : ParameterRouteOwnerOccurrence sources left.node)
    (sourceBound : environmentCost
        (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered) ≤
      environmentCost (application.environment initial)) :
    history.argumentDomainRoute.Charged sources initial count := by
  apply chargeTrans _ _
  · apply chargeSame
    refine .ownerPair (left.argumentFormationOccurrence sources application)
      (left.domainOccurrence sources application) _ _ ?_ ?_
    · cases application <;> exact sourceBound
    · cases application <;> exact sourceBound
  · exact chargeDomain left.pi right history.leftBelow history.whole whole

/-- Query-selected prior frames are admitted only through the actual
non-growth ledger. Capture itself then consumes exactly one prefixLedger slot. -/
noncomputable def OriginalApplyPiHistory.successorLedger
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight left right)
    (sources : ParameterRouteSources left.sourceEnv U) (initial : List Closure)
    (whole : history.whole.Charged sources initial count)
    (application : ParameterRouteOwnerOccurrence sources left.node)
    (sourceBound : environmentCost
        (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered) ≤
      environmentCost (application.environment initial))
    (prefixLedger : ParameterRouteLedger sources initial count history.final)
    (actual : List Closure) (actualBound : environmentCost actual ≤ environmentCost history.final)
    (domain : ParameterRouteDomain sources) (owners : List sources.Owner) :
    ParameterRouteLedger sources initial (count + 1)
      (parameterRouteStepEnvironment sources domain owners actual history.argumentDomainRoute.reserve initial) :=
  .capture domain owners (.bounded prefixLedger actual actualBound)
    (history.argumentDomainRoute.chargedReserve
      (history.argumentDomainRoute_charged sources initial whole application sourceBound))

/-- The actual chosen header domain, actual non-growing prior frame and
exact seed history produce the successor ledger. The only enlargement is
the checked retained-original domain reserve, never an assumed frame cost. -/
noncomputable def OriginalApplyPiHistory.actualSuccessorLedger
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight left right)
    (sources : ParameterRouteSources left.sourceEnv U) (initial : List Closure)
    (whole : history.whole.Charged sources initial count)
    (application : ParameterRouteOwnerOccurrence sources left.node)
    (sourceBound : environmentCost
        (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered) ≤
      environmentCost (application.environment initial))
    (prefixLedger : ParameterRouteLedger sources initial count history.final)
    (actual : List Closure) (actualBound : environmentCost actual ≤ environmentCost history.final)
    (domain : ParameterRouteOccurrence sources history.rightOrdered (.ref history.rightDomain))
    (owners : List sources.Owner) :
    ParameterRouteLedger sources initial (count + 1)
      (actualParameterRouteStepEnvironment sources (history.rightDomain.dependencyOrigin history.rightOrdered)
        owners actual history.argumentDomainRoute.reserve initial) :=
  .bounded
    (history.successorLedger sources initial whole application sourceBound prefixLedger actual actualBound domain.captureDomain owners)
    _ (domain.actualStep_bound owners actual history.argumentDomainRoute.reserve initial)

/-- The complete specialization, including both parent formation calls,
is below the same production projection reserve used by the actual route. -/
theorem OriginalApplyPiHistory.schedule_bound
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight left right)
    (sources : ParameterRouteSources left.sourceEnv U) (initial : List Closure)
    (whole : history.whole.Charged sources initial count)
    (application : ParameterRouteOwnerOccurrence sources left.node)
    (sourceBound : environmentCost
        (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered) ≤
      environmentCost (application.environment initial))
    (header : ParameterRouteOccurrence sources history.rightOrdered right.display.node)
    (prefixLedger : ParameterRouteLedger sources initial count history.final) :
    history.schedule ≤ richSchedule .expressionReindex
      (2 * sources.weight * parameterRouteCapacity sources count initial) := by
  have paid := (history.reserveCharged sources initial whole application sourceBound header prefixLedger).bound
  exact Nat.le_trans history.schedule_le (by
    change 3 * _ + 2 ≤ 3 * _ + 2
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 3 paid) 2)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
