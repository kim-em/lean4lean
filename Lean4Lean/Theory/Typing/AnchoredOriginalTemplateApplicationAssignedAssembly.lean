import Lean4Lean.Theory.Typing.AnchoredOriginalTemplateApplicationAssigned

/-! Productive assigned application assembly. The incoming result certificate
computes its singleton Pi request and its actual argument query. Only the
proper function/argument template children are compared. Their independently
selected right frames are merged before the original right-body replay. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

section Seed
variable
  {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
  (initial : ContextDerivation sourceEnv U rootSource)
  (domain : EndpointRef sourceEnv U source A (.sort u))
  (body : EndpointState sourceEnv U (A :: source) B (.sort v))
  (function : EndpointState sourceEnv U source f (.forallE A B))
  (argument : EndpointState sourceEnv U source a A)
  (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
  (hu : u.WF U) (hv : v.WF U)
  (location : Located root (.app hu hv (.ref domain) body function argument result))
  (frame : OriginalRichFrame sourceEnv env U registry target
    (location.contextDerivation initial) locals σ σ available)
  (substitutions : Ctx.SubstEq env U target σ σ source)
  (ordered : sourceEnv.Ordered)
local notation "limit" => applicationReplayLimit initial domain body function argument result hu hv location frame ordered
local notation "appCost" => (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin ordered)
  (frame.dependencyEnvironment ordered)).cost
local notation "base" => frame.captureBase substitutions

/-- The finite same-source calls for computing the left request. These
clauses recurse only at the stored original result/body/domain/argument and
function-formation occurrences. -/
structure TemplateApplicationSeedCalls (relevant : Bool) : Prop where
  bodyR : GeneratedObservationCall (base) (base).initialCaps
    (applicationResultDisplay initial domain body function argument result hu hv location (.identity _))
    (applicationBodyDisplay initial domain body function argument result hu hv location (.identity _))
    σ σ ordered ordered limit
  domainF : OriginalCodeInductionAt env registry ordered initial (.appDomain location) appCost
  argumentCalls : ∀ {n} {profile : Profile n},
    ∀ packet : ApplicationBackwardQueries initial domain body function argument result hu hv location frame substitutions ordered relevant profile,
    packet.queries.Calls
      (OriginalNestedDisplay.identity (base) argument (.ofLocation (.appArgument location) initial)) ordered limit
  formationR : GeneratedObservationCall (base) (base).initialCaps
    (applicationPiFormationDisplay (frame := frame) (substitutions := substitutions))
    (applicationFunctionFormationDisplay (frame := frame) (substitutions := substitutions))
    σ σ ordered ordered limit

/-- Both child requests are computed from the actual incoming result query.
The finite argument replay ledger consists only of original lower calls. -/
theorem templateApplicationSeed
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (bodyR : GeneratedObservationCall (base) (base).initialCaps
      (applicationResultDisplay initial domain body function argument result hu hv location (.identity _))
      (applicationBodyDisplay initial domain body function argument result hu hv location (.identity _))
      σ σ ordered ordered limit)
    (domainF : OriginalCodeInductionAt env registry ordered initial (.appDomain location) appCost)
    (argumentCalls : ∀ {n} {profile : Profile n},
      ∀ packet : ApplicationBackwardQueries initial domain body function argument result hu hv location frame substitutions ordered relevant profile,
      packet.queries.Calls
        (OriginalNestedDisplay.identity (base) argument (.ofLocation (.appArgument location) initial)) ordered limit)
    (formationR : GeneratedObservationCall (base) (base).initialCaps
      (applicationPiFormationDisplay (frame := frame) (substitutions := substitutions))
      (applicationFunctionFormationDisplay (frame := frame) (substitutions := substitutions))
      σ σ ordered ordered limit)
    (certificate : RichCert sourceEnv env U registry target result locals σ relevant (profile : Profile n) footprint)
    (resources : footprint.Available available) :
    ∃ packed : GeneratedApplicationPackedRequest domain body argument hu hv env registry target locals σ available relevant profile,
      ∃ functionFootprint, ∃ functionCertificate : RichCert sourceEnv env U registry target function.typeFormation.node locals σ relevant
        (.pi (A.subst σ) (B.subst σ.lift) packed.request.support
          [(packed.request.key, raiseProfile packed.request.rank packed.request.bound profile)]) functionFootprint,
        functionFootprint.Available available := by
  obtain ⟨packet, supply⟩ := generatedApplicationArguments initial domain body function argument result hu hv location frame substitutions ordered
    henv hscoped below formed closed bodyR certificate resources
  obtain ⟨supply⟩ := supply (argumentCalls packet)
  obtain ⟨packed⟩ := packet.piRequestWithArgument henv hscoped below formed closed domainF supply
  obtain ⟨required, ⟨query⟩, available⟩ := packed.request.atFunctionFormation
    (frame := frame) (substitutions := substitutions) henv closed formationR
  exact ⟨packed, required, query, available⟩

/-- Exact original calls needed after the two selected child frames have
been merged. No whole-application assigned comparison is a field. -/
structure TemplateApplicationReturnCalls : Prop where
  domainF : OriginalCodeInductionAt env registry ordered initial (.appDomain location) appCost
  bodyF : OriginalCodeInductionAt env registry ordered initial (.appCodomain location) appCost
  formationR : GeneratedObservationCall (base) (base).initialCaps
    (OriginalNestedDisplay.identity (base) function.typeFormation.node
      (.ofLocation (.assignedFormation (.appFunction location)) initial))
    (OriginalNestedDisplay.identity (base) (.pi hu hv (.ref domain) body)
      (.ofLocation (.appPiFormation location) initial)) σ σ ordered ordered limit
  resultR : GeneratedObservationCall (base) (base).initialCaps
    (templateApplicationBodyDisplay initial domain body function argument result hu hv location)
    (OriginalNestedDisplay.identity (base) result (.ofLocation (.appResult location) initial)) σ σ ordered ordered limit

end Seed

section Merge
variable
  {root : EndpointRef rightEnv U rootSource rootExpression rootType}
  (initial : ContextDerivation rightEnv U rootSource)
  (domain : EndpointRef rightEnv U source C (.sort u))
  (body : EndpointState rightEnv U (C :: source) E (.sort v))
  (function : EndpointState rightEnv U source g (.forallE C E))
  (argument : EndpointState rightEnv U source b C)
  (result : EndpointState rightEnv U source (E.inst b) (.sort v))
  (hu : u.WF U) (hv : v.WF U)
  (location : Located root (.app hu hv (.ref domain) body function argument result))
  (functionFrame : OriginalRichFrame rightEnv env U registry target
    (location.contextDerivation initial) locals τ τ functionAvailable)
  (argumentFrame : OriginalRichFrame rightEnv env U registry target
    (location.contextDerivation initial) locals τ τ argumentAvailable)
  (substitutions : Ctx.SubstEq env U target τ τ source)
  (ordered : rightEnv.Ordered)

/-- Independently returned child resources are kept verbatim in an actual
frame merge. Its measured environment is the maximum, not the sum. -/
theorem templateApplicationAssignedMerge
    {leftDomain : EndpointRef leftEnv U leftSource A (.sort lu)}
    {leftBody : EndpointState leftEnv U (A :: leftSource) B (.sort lv)}
    {leftFunction : EndpointState leftEnv U leftSource f (.forallE A B)}
    {leftArgument : EndpointState leftEnv U leftSource a A}
    (leftResult : EndpointState leftEnv U leftSource (B.inst a) (.sort lv))
    {lhu : lu.WF U} {lhv : lv.WF U}
    (packed : GeneratedApplicationPackedRequest leftDomain leftBody leftArgument lhu lhv
      env registry target leftLocals σ leftAvailable relevant (profile : Profile m))
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : rightEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (functionClosed : functionAvailable.AtomClosed) (argumentClosed : argumentAvailable.AtomClosed)
    (functionAnswer : TemplateAssignedResult env U registry target leftFunction function locals σ τ functionAvailable relevant
      (.pi (A.subst σ) (B.subst σ.lift) packed.request.support
        [(packed.request.key, raiseProfile packed.request.rank packed.request.bound profile)]))
    (argumentAnswer : TemplateComparisonResult env U registry target leftArgument argument
      leftLocals locals σ τ leftAvailable argumentAvailable packed.argumentQuery.raw)
    (calls : TemplateApplicationReturnCalls initial domain body function argument result hu hv location
      (functionFrame.merge argumentFrame) substitutions ordered) :
    Nonempty (TemplateAssignedResult env U registry target
      (.app lhu lhv (.ref leftDomain) leftBody leftFunction leftArgument leftResult)
      (.app hu hv (.ref domain) body function argument result) locals σ τ
      (functionAvailable.append argumentAvailable) relevant profile) := by
  let functionAnswer' : TemplateAssignedResult env U registry target leftFunction function locals σ τ
      (functionAvailable.append argumentAvailable) relevant
      (.pi (A.subst σ) (B.subst σ.lift) packed.request.support
        [(packed.request.key, raiseProfile packed.request.rank packed.request.bound profile)]) :=
    { functionAnswer with resources := fun i need member =>
        List.mem_append_left _ (functionAnswer.resources i need member) }
  let argumentAnswer' : TemplateComparisonResult env U registry target leftArgument argument
      leftLocals locals σ τ leftAvailable (functionAvailable.append argumentAvailable) packed.argumentQuery.raw :=
    { argumentAnswer with rightQuery := (argumentAnswer.rightQuery.availableMono
        (fun i need member => List.mem_append_right _ member)) }
  have closed : (functionAvailable.append argumentAvailable).AtomClosed := by
    intro i need member atom present
    rcases List.mem_append.mp member with member | member
    · exact List.mem_append_left _ (functionClosed i need member atom present)
    · exact List.mem_append_right _ (argumentClosed i need member atom present)
  exact templateApplicationAssignedOfSeed initial domain body function argument result hu hv location
    (functionFrame.merge argumentFrame) substitutions ordered leftResult packed henv hscoped below formed closed
    functionAnswer' argumentAnswer' calls.domainF calls.bodyF calls.formationR calls.resultR

end Merge
section Step
variable
  (left : OriginalApplicationTypeRouteSide U leftCommon)
  (right : OriginalApplicationTypeRouteSide U rightCommon)
  (leftFrame : OriginalRichFrame left.sourceEnv env U registry target
    (left.location.contextDerivation left.initial) leftLocals σ σ leftAvailable)
  (rightFrame : OriginalRichFrame right.sourceEnv env U registry target
    (right.location.contextDerivation right.initial) rightLocals τ τ rightAvailable)
  (leftSubstitutions : Ctx.SubstEq env U target σ σ left.source)
  (rightSubstitutions : Ctx.SubstEq env U target τ τ right.source)
  (leftOrdered : left.sourceEnv.Ordered) (rightOrdered : right.sourceEnv.Ordered)
local notation "leftCost" => (Closure.close (left.node.dependencyOrigin leftOrdered)
  (leftFrame.dependencyEnvironment leftOrdered)).cost
local notation "rightCost" => (Closure.close (right.node.dependencyOrigin rightOrdered)
  (rightFrame.dependencyEnvironment rightOrdered)).cost
local notation "parentLimit" => richSchedule .assignedComparison (leftCost + rightCost)
local notation "rightCapacity" => environmentCost (rightFrame.dependencyEnvironment rightOrdered)

/-- The productive application case for mutual local term/assigned template
comparison. The two local induction clauses concern ONLY the proper function
and argument original pairs. Their returned frames are selected independently,
then merged with a checked capacity bound before exact right-body replay.
There is no assigned comparison assumption for the applications themselves. -/
theorem templateApplicationAssignedStep
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftBelow : left.sourceEnv ≤ env) (rightBelow : right.sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (leftClosed : leftAvailable.AtomClosed)
    (seedCalls : TemplateApplicationSeedCalls left.initial left.domain left.body left.function left.argument left.result
      left.hu left.hv left.location leftFrame leftSubstitutions leftOrdered relevant)
    (functionC :
      richSchedule .assignedComparison
        ((Closure.close (left.function.dependencyOrigin leftOrdered) (leftFrame.dependencyEnvironment leftOrdered)).cost +
         (Closure.close (right.function.dependencyOrigin rightOrdered) (rightFrame.dependencyEnvironment rightOrdered)).cost) < parentLimit →
      ∀ {n : Nat} {query : Profile n} {footprint : Footprint},
      RichCert left.sourceEnv env U registry target left.function.typeFormation.node leftLocals σ relevant query footprint →
      footprint.Available leftAvailable →
      ∃ available, ∃ selected : OriginalRichFrame right.sourceEnv env U registry target
        (right.location.contextDerivation right.initial) rightLocals τ τ available,
        available.AtomClosed ∧ environmentCost (selected.dependencyEnvironment rightOrdered) ≤ rightCapacity ∧
        Nonempty (TemplateAssignedResult env U registry target left.function right.function rightLocals σ τ available relevant query))
    (argumentF :
      richSchedule .fundamental
        ((Closure.close (left.argument.dependencyOrigin leftOrdered) (leftFrame.dependencyEnvironment leftOrdered)).cost +
         (Closure.close (right.argument.dependencyOrigin rightOrdered) (rightFrame.dependencyEnvironment rightOrdered)).cost) < parentLimit →
      ∀ {n : Nat} {query : Profile n} {footprint : Footprint},
      RichObs left.sourceEnv env U registry target left.argument leftLocals σ query footprint →
      footprint.Available leftAvailable →
      ∃ available, ∃ selected : OriginalRichFrame right.sourceEnv env U registry target
        (right.location.contextDerivation right.initial) rightLocals τ τ available,
        available.AtomClosed ∧ environmentCost (selected.dependencyEnvironment rightOrdered) ≤ rightCapacity ∧
        Nonempty (TemplateComparisonResult env U registry target left.argument right.argument leftLocals rightLocals
          σ τ leftAvailable available query))
    (returnCalls : ∀ {available},
      ∀ selected : OriginalRichFrame right.sourceEnv env U registry target
        (right.location.contextDerivation right.initial) rightLocals τ τ available,
      environmentCost (selected.dependencyEnvironment rightOrdered) ≤ rightCapacity →
      TemplateApplicationReturnCalls right.initial right.domain right.body right.function right.argument right.result
        right.hu right.hv right.location selected rightSubstitutions rightOrdered)
    (certificate : RichCert left.sourceEnv env U registry target left.result leftLocals σ relevant
      (profile : Profile n) footprint)
    (resources : footprint.Available leftAvailable) :
    ∃ available, ∃ selected : OriginalRichFrame right.sourceEnv env U registry target
        (right.location.contextDerivation right.initial) rightLocals τ τ available,
      available.AtomClosed ∧ environmentCost (selected.dependencyEnvironment rightOrdered) ≤ rightCapacity ∧
      Nonempty (TemplateAssignedResult env U registry target left.node right.node rightLocals σ τ available relevant profile) := by
  have leftReserve := application_cost_le_captured (left.domain.dependencyOrigin leftOrdered)
    (left.body.dependencyOrigin leftOrdered) (left.function.dependencyOrigin leftOrdered)
    (left.argument.dependencyOrigin leftOrdered) (left.result.dependencyOrigin leftOrdered)
    (leftFrame.dependencyEnvironment leftOrdered)
  have rightReserve := application_cost_le_captured (right.domain.dependencyOrigin rightOrdered)
    (right.body.dependencyOrigin rightOrdered) (right.function.dependencyOrigin rightOrdered)
    (right.argument.dependencyOrigin rightOrdered) (right.result.dependencyOrigin rightOrdered)
    (rightFrame.dependencyEnvironment rightOrdered)
  have leftFn : (Closure.close (left.function.dependencyOrigin leftOrdered)
      (leftFrame.dependencyEnvironment leftOrdered)).cost < leftCost :=
    Nat.lt_of_lt_of_le (binder_other_cost (by simp) _) leftReserve
  have rightFn : (Closure.close (right.function.dependencyOrigin rightOrdered)
      (rightFrame.dependencyEnvironment rightOrdered)).cost < rightCost :=
    Nat.lt_of_lt_of_le (binder_other_cost (by simp) _) rightReserve
  have leftArg : (Closure.close (left.argument.dependencyOrigin leftOrdered)
      (leftFrame.dependencyEnvironment leftOrdered)).cost < leftCost :=
    Nat.lt_of_lt_of_le (binder_other_cost (by simp) _) leftReserve
  have rightArg : (Closure.close (right.argument.dependencyOrigin rightOrdered)
      (rightFrame.dependencyEnvironment rightOrdered)).cost < rightCost :=
    Nat.lt_of_lt_of_le (binder_other_cost (by simp) _) rightReserve
  obtain ⟨packed, functionFootprint, functionCertificate, functionResources⟩ :=
    templateApplicationSeed left.initial left.domain left.body left.function left.argument left.result
      left.hu left.hv left.location leftFrame leftSubstitutions leftOrdered henv hscoped leftBelow formed leftClosed
      seedCalls.bodyR seedCalls.domainF seedCalls.argumentCalls seedCalls.formationR certificate resources
  obtain ⟨functionAvailable, functionFrame, functionClosed, functionBound, ⟨functionAnswer⟩⟩ :=
    functionC (richSchedule_strict (Nat.add_lt_add leftFn rightFn) _ _) functionCertificate functionResources
  obtain ⟨argumentAvailable, argumentFrame, argumentClosed, argumentBound, ⟨argumentAnswer⟩⟩ :=
    argumentF (richSchedule_strict (Nat.add_lt_add leftArg rightArg) _ _)
      packed.argumentQuery.observation packed.argumentQuery.resources
  let merged := functionFrame.merge argumentFrame
  have mergedBound : environmentCost (merged.dependencyEnvironment rightOrdered) ≤ rightCapacity := by
    rw [OriginalRichFrame.merge_environmentCost]
    exact Nat.max_le.mpr ⟨functionBound, argumentBound⟩
  have mergedClosed : (functionAvailable.append argumentAvailable).AtomClosed := by
    intro i need member atom present
    rcases List.mem_append.mp member with member | member
    · exact List.mem_append_left _ (functionClosed i need member atom present)
    · exact List.mem_append_right _ (argumentClosed i need member atom present)
  have completed := templateApplicationAssignedMerge right.initial right.domain right.body right.function right.argument right.result
    right.hu right.hv right.location functionFrame argumentFrame rightSubstitutions rightOrdered left.result packed
    henv hscoped rightBelow formed functionClosed argumentClosed functionAnswer argumentAnswer (returnCalls merged mergedBound)
  exact ⟨_, merged, mergedClosed, mergedBound, completed⟩

end Step

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
