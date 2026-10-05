import Lean4Lean.Theory.Typing.AnchoredOriginalParameterGeneratedSchedules
import Lean4Lean.Theory.Typing.AnchoredOriginalParameterRouteReserve

/-! A declaration capture ledger that retains the original comparison routes
at every slot.  Both universe packets share the recurrence: a route may refer
to either actual header, at two independently produced prior ledgers. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.Dependency
open VExpr VEnv OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

structure ParameterRouteHeader (env : VEnv) (U : Nat) where
  sourceEnv : VEnv
  ordered : sourceEnv.Ordered
  source : List VExpr
  expression : VExpr
  assigned : VExpr
  header : EndpointRef sourceEnv U source expression assigned
  roots : List (SelectedParameterDependency env U)

noncomputable def ParameterRouteHeader.weight (header : ParameterRouteHeader env U) : Nat :=
  (header.header.dependencyOrigin header.ordered).weight + parameterWeights header.roots

structure ParameterRouteSources (env : VEnv) (U : Nat) where
  ordered : env.Ordered
  source : List VExpr
  fieldExpression : VExpr
  fieldType : VExpr
  majorExpression : VExpr
  majorType : VExpr
  field : EndpointRef env U source fieldExpression fieldType
  major : EndpointRef env U source majorExpression majorType
  seed : ParameterRouteHeader env U
  requested : ParameterRouteHeader env U

noncomputable def ParameterRouteSources.weight (sources : ParameterRouteSources env U) : Nat :=
  sources.seed.weight + sources.requested.weight

abbrev ParameterRouteSources.Owner (sources : ParameterRouteSources env U) :=
  Sum (LocatedOrigin sources.ordered sources.field) (LocatedOrigin sources.ordered sources.major)

inductive ParameterRouteDomain (sources : ParameterRouteSources env U) where
  | seed (domain : ParameterDomain sources.seed.ordered sources.seed.header sources.seed.roots)
  | requested (domain : ParameterDomain sources.requested.ordered sources.requested.header sources.requested.roots)

noncomputable def ParameterRouteDomain.origin (domain : ParameterRouteDomain sources) : Origin :=
  match domain with
  | .seed domain => domain.origin
  | .requested domain => domain.origin

theorem ParameterRouteDomain.weight_le (domain : ParameterRouteDomain sources) :
    domain.origin.weight ≤ sources.weight := by
  cases domain with
  | seed domain => exact Nat.le_trans domain.weight_le (Nat.le_add_right _ _)
  | requested domain => exact Nat.le_trans domain.weight_le (Nat.le_add_left _ _)

inductive ParameterRouteOccurrence (sources : ParameterRouteSources env U) :
    {sourceEnv : VEnv} → {source : List VExpr} → {expression assigned : VExpr} →
    (ordered : sourceEnv.Ordered) → EndpointState sourceEnv U source expression assigned → Type where
  | seed (occurrence : ParameterOccurrence sources.seed.ordered sources.seed.header sources.seed.roots ordered node) :
      ParameterRouteOccurrence sources ordered node
  | requested (occurrence : ParameterOccurrence sources.requested.ordered sources.requested.header sources.requested.roots ordered node) :
      ParameterRouteOccurrence sources ordered node

theorem ParameterRouteOccurrence.weight_le
    (occurrence : ParameterRouteOccurrence sources ordered node) :
    (node.dependencyOrigin ordered).weight ≤ sources.weight := by
  cases occurrence with
  | seed occurrence =>
      exact Nat.le_trans occurrence.weight_le (ParameterRouteDomain.weight_le (.seed occurrence.domain))
  | requested occurrence =>
      exact Nat.le_trans occurrence.weight_le (ParameterRouteDomain.weight_le (.requested occurrence.domain))

structure ParameterRouteEquality (sources : ParameterRouteSources env U) where
  sourceEnv : VEnv
  ordered : sourceEnv.Ordered
  source : List VExpr
  left : VExpr
  right : VExpr
  assigned : VExpr
  original : Derivation sourceEnv U source left right assigned
  occurrence : ParameterRouteOccurrence sources ordered (.ref (.left original))

noncomputable def ParameterRouteEquality.origin (equality : ParameterRouteEquality sources) : Origin :=
  equality.original.dependencyOrigin equality.ordered

theorem ParameterRouteEquality.weight_le (equality : ParameterRouteEquality sources) :
    equality.origin.weight ≤ sources.weight := equality.occurrence.weight_le

inductive ParameterRouteOwnerOccurrence (sources : ParameterRouteSources env U) :
    {source : List VExpr} → {expression assigned : VExpr} →
      EndpointState env U source expression assigned → Type where
  | field (location : Located sources.field node) : ParameterRouteOwnerOccurrence sources node
  | major (location : Located sources.major node) : ParameterRouteOwnerOccurrence sources node

noncomputable def ParameterRouteOwnerOccurrence.environment
    (owner : ParameterRouteOwnerOccurrence sources node) (initial : List Closure) : List Closure :=
  match owner with
  | .field location | .major location => location.dependencyEnvironment sources.ordered initial

theorem ParameterRouteOwnerOccurrence.cost_le
    (owner : ParameterRouteOwnerOccurrence sources node) (initial : List Closure)
    (bounded : environmentCost actual ≤ environmentCost (owner.environment initial)) :
    (Closure.close (node.dependencyOrigin sources.ordered) actual).cost ≤
      ((sources.field.dependencyOrigin sources.ordered).weight +
        (sources.major.dependencyOrigin sources.ordered).weight) * (1 + environmentCost initial) := by
  have first := Nat.mul_le_mul_left (node.dependencyOrigin sources.ordered).weight
    (Nat.add_le_add_left bounded 1)
  cases owner with
  | field location =>
    exact Nat.le_trans first (Nat.le_trans (location.dependency_cost_le sources.ordered initial)
      (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))
  | major location =>
    exact Nat.le_trans first (Nat.le_trans (location.dependency_cost_le sources.ordered initial)
      (Nat.mul_le_mul_right _ (Nat.le_add_left _ _)))

noncomputable def parameterRouteStepEnvironment (sources : ParameterRouteSources env U)
    (domain : ParameterRouteDomain sources) (owners : List sources.Owner)
    (previous reserve initial : List Closure) : List Closure :=
  let declared := Closure.close domain.origin previous
  reserve ++ (declared :: (owners.map (fun owner => Closure.bundle (groupedOwnerClosure owner initial) declared) ++ previous))

mutual
  /-- The index bounds actual prefix depth. Merging query-specific replies
  retains both original ledgers without charging another source slot. -/
  inductive ParameterRouteLedger (sources : ParameterRouteSources env U) (initial : List Closure) :
      Nat → List Closure → Type where
    | empty : ParameterRouteLedger sources initial 0 []
    | advance (previous : ParameterRouteLedger sources initial count environment) :
        ParameterRouteLedger sources initial (count + 1) environment
    | bounded (previous : ParameterRouteLedger sources initial count baseline)
        (actual : List Closure) (bound : environmentCost actual ≤ environmentCost baseline) :
        ParameterRouteLedger sources initial count actual
    | merge (left : ParameterRouteLedger sources initial count leftEnvironment)
        (right : ParameterRouteLedger sources initial count rightEnvironment) :
        ParameterRouteLedger sources initial count (leftEnvironment ++ rightEnvironment)
    | capture (domain : ParameterRouteDomain sources) (owners : List sources.Owner)
        (previous : ParameterRouteLedger sources initial count environment)
        (calls : ParameterRouteCharges sources initial count reserve) :
        ParameterRouteLedger sources initial (count + 1)
          (parameterRouteStepEnvironment sources domain owners environment reserve initial)

  /-- A call stores its original occurrence(s) and both actual prior
  environments. No independent numerical bound is accepted. -/
  inductive ParameterRouteCharge (sources : ParameterRouteSources env U) (initial : List Closure) :
      Nat → Closure → Type where
    | reindex (left : ParameterRouteOccurrence sources leftOrdered leftNode)
        (right : ParameterRouteOccurrence sources rightOrdered rightNode)
        (leftFrame : ParameterRouteLedger sources initial count leftEnvironment)
        (rightFrame : ParameterRouteLedger sources initial count rightEnvironment) :
        ParameterRouteCharge sources initial count
          (.bundle (.close (leftNode.dependencyOrigin leftOrdered) leftEnvironment)
            (.close (rightNode.dependencyOrigin rightOrdered) rightEnvironment))
    | ownerPair (left : ParameterRouteOwnerOccurrence sources leftNode)
        (right : ParameterRouteOwnerOccurrence sources rightNode)
        (leftEnvironment rightEnvironment : List Closure)
        (leftBound : environmentCost leftEnvironment ≤ environmentCost (left.environment initial))
        (rightBound : environmentCost rightEnvironment ≤ environmentCost (right.environment initial)) :
        ParameterRouteCharge sources initial count
          (.bundle (.close (leftNode.dependencyOrigin sources.ordered) leftEnvironment)
            (.close (rightNode.dependencyOrigin sources.ordered) rightEnvironment))
    | ownerReindex (owner : ParameterRouteOwnerOccurrence sources ownerNode)
        (ownerEnvironment : List Closure)
        (bounded : environmentCost ownerEnvironment ≤ environmentCost (owner.environment initial))
        (right : ParameterRouteOccurrence sources rightOrdered rightNode)
        (rightFrame : ParameterRouteLedger sources initial count rightEnvironment) :
        ParameterRouteCharge sources initial count
          (.bundle (.close (ownerNode.dependencyOrigin sources.ordered) ownerEnvironment)
            (.close (rightNode.dependencyOrigin rightOrdered) rightEnvironment))
    | equality (equality : ParameterRouteEquality sources)
        (frame : ParameterRouteLedger sources initial count environment) :
        ParameterRouteCharge sources initial count (.close equality.origin environment)

  inductive ParameterRouteCharges (sources : ParameterRouteSources env U) (initial : List Closure) :
      Nat → List Closure → Type where
    | nil : ParameterRouteCharges sources initial count []
    | cons (head : ParameterRouteCharge sources initial count closure)
        (tail : ParameterRouteCharges sources initial count rest) :
        ParameterRouteCharges sources initial count (closure :: rest)
end

noncomputable def parameterRouteCapacity (sources : ParameterRouteSources env U)
    (count : Nat) (initial : List Closure) : Nat :=
  (2 * sources.weight + 2) ^ count *
    (1 + (sources.field.dependencyOrigin sources.ordered).weight +
      (sources.major.dependencyOrigin sources.ordered).weight) * (1 + environmentCost initial)

private theorem sources_positive (sources : ParameterRouteSources env U) : 0 < sources.weight := by
  have first := (sources.seed.header.dependencyOrigin sources.seed.ordered).weight_pos
  dsimp [ParameterRouteSources.weight, ParameterRouteHeader.weight]
  omega

private theorem capacity_positive (sources : ParameterRouteSources env U) (count : Nat) (initial : List Closure) :
    0 < parameterRouteCapacity sources count initial := by
  apply Nat.mul_pos
  · apply Nat.mul_pos
    · exact Nat.pow_pos (by omega)
    · omega
  · omega

private theorem capacity_succ (sources : ParameterRouteSources env U) (count : Nat) (initial : List Closure) :
    parameterRouteCapacity sources (count + 1) initial =
      (2 * sources.weight + 2) * parameterRouteCapacity sources count initial := by
  simp only [parameterRouteCapacity, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

private theorem capacity_owner (sources : ParameterRouteSources env U) (owner : sources.Owner)
    (count : Nat) (initial : List Closure) :
    (groupedOwnerClosure owner initial).cost ≤ parameterRouteCapacity sources count initial := by
  have powerPositive : 0 < (2 * sources.weight + 2) ^ count := Nat.pow_pos (by omega)
  have base : (sources.field.dependencyOrigin sources.ordered).weight +
      (sources.major.dependencyOrigin sources.ordered).weight ≤
      1 + (sources.field.dependencyOrigin sources.ordered).weight +
        (sources.major.dependencyOrigin sources.ordered).weight := by omega
  exact Nat.le_trans (groupedOwner_bound owner initial)
    (Nat.mul_le_mul_right _ (Nat.le_trans base (Nat.le_mul_of_pos_left _ powerPositive)))

theorem ParameterRouteOwnerOccurrence.cost_le_capacity
    (owner : ParameterRouteOwnerOccurrence sources node) (initial : List Closure)
    (bounded : environmentCost actual ≤ environmentCost (owner.environment initial)) (count : Nat) :
    (Closure.close (node.dependencyOrigin sources.ordered) actual).cost ≤
      parameterRouteCapacity sources count initial := by
  have powerPositive : 0 < (2 * sources.weight + 2) ^ count := Nat.pow_pos (by omega)
  have base : (sources.field.dependencyOrigin sources.ordered).weight +
      (sources.major.dependencyOrigin sources.ordered).weight ≤
      1 + (sources.field.dependencyOrigin sources.ordered).weight +
        (sources.major.dependencyOrigin sources.ordered).weight := by omega
  exact Nat.le_trans (owner.cost_le initial bounded)
    (Nat.mul_le_mul_right _ (Nat.le_trans base (Nat.le_mul_of_pos_left _ powerPositive)))

private theorem environment_append (left right : List Closure) :
    environmentCost (left ++ right) = max (environmentCost left) (environmentCost right) := by
  induction left with
  | nil => simp [environmentCost]
  | cons head tail ih => simp only [List.cons_append, environmentCost, ih, Nat.max_assoc]

private theorem environment_bound_of_members {closures : List Closure}
    (bound : ∀ closure ∈ closures, closure.cost ≤ maximum) : environmentCost closures ≤ maximum := by
  induction closures with
  | nil => simp [environmentCost]
  | cons closure rest ih =>
    exact Nat.max_le.mpr ⟨bound closure List.mem_cons_self,
      ih (fun c hc => bound c (List.mem_cons_of_mem _ hc))⟩

mutual
  theorem ParameterRouteLedger.bound (ledger : ParameterRouteLedger sources initial count environment) :
      1 + environmentCost environment ≤ parameterRouteCapacity sources count initial := by
    match ledger with
    | .empty => have := capacity_positive sources 0 initial; simp only [environmentCost]; omega
    | .advance previous =>
      have bound := previous.bound
      rw [capacity_succ]
      exact Nat.le_trans bound (Nat.le_mul_of_pos_left _ (by omega))
    | .bounded previous actual bounded =>
      exact Nat.le_trans (Nat.add_le_add_left bounded 1) previous.bound
    | .merge left right =>
      have hl := left.bound
      have hr := right.bound
      rw [environment_append]
      omega
    | @ParameterRouteLedger.capture _ _ _ _ count environment reserve domain owners previous calls =>
      have priorBound := previous.bound
      have callBound := calls.bound
      have positive := capacity_positive sources count initial
      have domainBound : (Closure.close domain.origin _).cost ≤
          sources.weight * parameterRouteCapacity sources count initial :=
        Nat.mul_le_mul domain.weight_le priorBound
      have envBound : environmentCost (parameterRouteStepEnvironment sources domain owners environment reserve initial) ≤
          (2 * sources.weight + 1) * parameterRouteCapacity sources count initial := by
        apply environment_bound_of_members
        intro closure member
        simp only [parameterRouteStepEnvironment, List.mem_cons, List.mem_append, List.mem_map] at member
        rcases member with reserveMember | rfl | ⟨owner, _, rfl⟩ | previousMember
        · exact Nat.le_trans (environment_entry reserveMember)
            (Nat.le_trans callBound (Nat.mul_le_mul_right _ (by omega)))
        · apply Nat.le_trans domainBound
          exact Nat.mul_le_mul_right _ (by omega)
        · have ownerBound := capacity_owner sources owner count initial
          change _ + _ ≤ _
          rw [Nat.add_mul, Nat.one_mul]
          have twice : sources.weight * parameterRouteCapacity sources count initial ≤
              2 * sources.weight * parameterRouteCapacity sources count initial :=
            Nat.mul_le_mul_right _ (by omega)
          omega
        · have bound := environment_entry previousMember
          have grow : parameterRouteCapacity sources count initial ≤
              (2 * sources.weight + 1) * parameterRouteCapacity sources count initial :=
            Nat.le_mul_of_pos_left _ (by omega)
          omega
      rw [capacity_succ]
      rw [show 2 * sources.weight + 2 = (2 * sources.weight + 1) + 1 by omega, Nat.add_mul, Nat.one_mul]
      omega
  termination_by sizeOf ledger

  theorem ParameterRouteCharge.bound (charge : ParameterRouteCharge sources initial count closure) :
      closure.cost ≤ 2 * sources.weight * parameterRouteCapacity sources count initial := by
    match charge with
    | .reindex left right leftFrame rightFrame =>
      have first := Nat.mul_le_mul left.weight_le leftFrame.bound
      have second := Nat.mul_le_mul right.weight_le rightFrame.bound
      change _ + _ ≤ _
      simpa only [Closure.cost, Nat.two_mul, Nat.add_mul] using Nat.add_le_add first second
    | .ownerPair left right leftEnvironment rightEnvironment leftBound rightBound =>
      have first := left.cost_le_capacity initial leftBound count
      have second := right.cost_le_capacity initial rightBound count
      have enlarge : parameterRouteCapacity sources count initial ≤
          sources.weight * parameterRouteCapacity sources count initial :=
        Nat.le_mul_of_pos_left _ (sources_positive sources)
      change _ + _ ≤ _
      simpa only [Nat.two_mul, Nat.add_mul] using
        Nat.add_le_add (Nat.le_trans first enlarge) (Nat.le_trans second enlarge)
    | .ownerReindex owner ownerEnvironment bounded right rightFrame =>
      have ownerBound := owner.cost_le_capacity initial bounded count
      have second := Nat.mul_le_mul right.weight_le rightFrame.bound
      have enlarge : parameterRouteCapacity sources count initial ≤
          sources.weight * parameterRouteCapacity sources count initial :=
        Nat.le_mul_of_pos_left _ (sources_positive sources)
      change _ + _ ≤ _
      simpa only [Closure.cost, Nat.two_mul, Nat.add_mul] using
        Nat.add_le_add (Nat.le_trans ownerBound enlarge) second
    | .equality equality frame =>
      exact Nat.le_trans (Nat.mul_le_mul equality.weight_le frame.bound)
        (Nat.mul_le_mul_right _ (by omega))
  termination_by sizeOf charge

  theorem ParameterRouteCharges.bound (charges : ParameterRouteCharges sources initial count reserve) :
      environmentCost reserve ≤ 2 * sources.weight * parameterRouteCapacity sources count initial := by
    match charges with
    | .nil => simp [environmentCost]
    | .cons head tail => exact Nat.max_le.mpr ⟨head.bound, tail.bound⟩
  termination_by sizeOf charges
end

/-- Padding a shorter actual prefix changes only its stage index. -/
def ParameterRouteLedger.widen (ledger : ParameterRouteLedger sources initial count environment)
    (bound : count ≤ count') : ParameterRouteLedger sources initial count' environment := by
  match count' with
  | 0 =>
    have same : count = 0 := by omega
    subst count
    exact ledger
  | next + 1 =>
    by_cases same : count = next + 1
    · subst count; exact ledger
    · exact .advance (ledger.widen (count' := next) (by omega))
termination_by count'

def ParameterRouteCharges.append (left : ParameterRouteCharges sources initial count first)
    (right : ParameterRouteCharges sources initial count second) :
    ParameterRouteCharges sources initial count (first ++ second) := by
  match left with
  | .nil => exact right
  | .cons head tail => exact .cons head (tail.append right)
termination_by sizeOf left

/-- Existing declaration ledgers are concrete initial instances; no route
charge is retroactively assumed to be in their environments. -/
noncomputable def ParameterRouteLedger.seedPrefix
    (sources : ParameterRouteSources env U)
    (steps : List (GroupedParameterStep sources.seed.ordered sources.ordered
      sources.seed.header sources.field sources.major sources.seed.roots))
    (initial : List Closure) :
    ParameterRouteLedger sources initial steps.length (groupedParameterEnvironment steps initial) := by
  induction steps with
  | nil => exact .empty
  | cons step rest ih =>
    simpa only [List.length_cons, groupedParameterEnvironment, parameterRouteStepEnvironment,
      ParameterRouteDomain.origin, List.nil_append, List.append_nil, List.cons_append] using
      (ParameterRouteLedger.capture (.seed step.domain) step.owners ih .nil)

noncomputable def ParameterRouteLedger.requestedPrefix
    (sources : ParameterRouteSources env U)
    (steps : List (GroupedParameterStep sources.requested.ordered sources.ordered
      sources.requested.header sources.field sources.major sources.requested.roots))
    (initial : List Closure) :
    ParameterRouteLedger sources initial steps.length (groupedParameterEnvironment steps initial) := by
  induction steps with
  | nil => exact .empty
  | cons step rest ih =>
    simpa only [List.length_cons, groupedParameterEnvironment, parameterRouteStepEnvironment,
      ParameterRouteDomain.origin, List.nil_append, List.append_nil, List.cons_append] using
      (ParameterRouteLedger.capture (.requested step.domain) step.owners ih .nil)

/-- This coefficient depends only on the requested declaration and the
original major. Its selected seed header is bounded by that major's real
constant-prefix proof, including the selected universe equality roots. -/
theorem ParameterRouteCharge.projection_reserve_bound
    (charge : ParameterRouteCharge sources initial count closure)
    (seedBound : sources.seed.weight ≤ (sources.major.dependencyOrigin sources.ordered).weight)
    (countBound : count ≤ prefixCount) :
    closure.cost ≤ routedParameterDependencyReserve prefixCount
      (sources.requested.header.dependencyOrigin sources.requested.ordered).weight
      (parameterWeights sources.requested.roots)
      (sources.field.dependencyOrigin sources.ordered).weight
      (sources.major.dependencyOrigin sources.ordered).weight * (1 + environmentCost initial) := by
  apply Nat.le_trans charge.bound
  have weightBound : sources.weight ≤
      (sources.requested.header.dependencyOrigin sources.requested.ordered).weight +
        parameterWeights sources.requested.roots + (sources.major.dependencyOrigin sources.ordered).weight := by
    dsimp [ParameterRouteSources.weight, ParameterRouteHeader.weight] at *
    omega
  have powerBound := Nat.le_trans
    (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.mul_le_mul_left 2 weightBound) 2) count)
    (Nat.pow_le_pow_right (by omega) countBound)
  unfold parameterRouteCapacity routedParameterDependencyReserve
  simpa only [Nat.mul_assoc] using
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 weightBound)
      (Nat.mul_le_mul_right (1 + environmentCost initial)
        (Nat.mul_le_mul_right
          (1 + (sources.field.dependencyOrigin sources.ordered).weight +
            (sources.major.dependencyOrigin sources.ordered).weight) powerBound))

theorem ParameterRouteCharges.projection_reserve_bound
    (charges : ParameterRouteCharges sources initial count reserve)
    (seedBound : sources.seed.weight ≤ (sources.major.dependencyOrigin sources.ordered).weight)
    (countBound : count ≤ prefixCount) :
    environmentCost reserve ≤ routedParameterDependencyReserve prefixCount
      (sources.requested.header.dependencyOrigin sources.requested.ordered).weight
      (parameterWeights sources.requested.roots)
      (sources.field.dependencyOrigin sources.ordered).weight
      (sources.major.dependencyOrigin sources.ordered).weight * (1 + environmentCost initial) := by
  match charges with
  | .nil => simp [environmentCost]
  | .cons head tail =>
    exact Nat.max_le.mpr
      ⟨head.projection_reserve_bound seedBound countBound, tail.projection_reserve_bound seedBound countBound⟩
termination_by sizeOf charges

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.Dependency
