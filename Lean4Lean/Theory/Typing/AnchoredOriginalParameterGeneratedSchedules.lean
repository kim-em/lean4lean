import Lean4Lean.Theory.Typing.AnchoredOriginalGroupedParameterReserve
import Lean4Lean.Theory.Typing.AnchoredOriginalRichConstantBounds

/-! Query-selected parameter frames may have different exact prior
ledgers. Comparing their environment costs selects one of those two actual
ledgers; it neither concatenates captures nor increases the parent reserve. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.Dependency
open VExpr VEnv OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

/-- A queried domain is either an actual header descendant or an actual
left/right descendant of one retained parameter equality. In particular,
the normalized Pi domain is a descendant, not the normalization root. -/
inductive ParameterOccurrence
    {headerEnv : VEnv} (headerFormed : headerEnv.Ordered)
    (header : EndpointRef headerEnv U headerSource headerExpression headerType)
    (roots : List (SelectedParameterDependency env U)) :
    {sourceEnv : VEnv} → {source : List VExpr} → {expression assigned : VExpr} →
      (ordered : sourceEnv.Ordered) → EndpointState sourceEnv U source expression assigned → Type where
  | headerOrigin {node : EndpointState headerEnv U source expression assigned}
      (location : Located header node) : ParameterOccurrence headerFormed header roots headerFormed node
  | equalityLeft (selected : SelectedParameterDependency env U) (member : selected ∈ roots)
      {node : EndpointState selected.source U source expression assigned}
      (location : Located (.left selected.root.original) node) :
      ParameterOccurrence headerFormed header roots selected.ordered node
  | equalityRight (selected : SelectedParameterDependency env U) (member : selected ∈ roots)
      {node : EndpointState selected.source U source expression assigned}
      (location : Located (.right selected.root.original) node) :
      ParameterOccurrence headerFormed header roots selected.ordered node

noncomputable def ParameterOccurrence.domain
    (occurrence : ParameterOccurrence headerFormed header roots ordered node) :
    ParameterDomain headerFormed header roots :=
  match occurrence with
  | .headerOrigin location => .headerDomain ⟨_, _, _, _, location⟩
  | .equalityLeft selected member _ => .equality selected member
  | .equalityRight selected member _ => .equality selected member

theorem ParameterOccurrence.weight_le
    (occurrence : ParameterOccurrence headerFormed header roots ordered node) :
    (node.dependencyOrigin ordered).weight ≤ occurrence.domain.origin.weight := by
  cases occurrence with
  | headerOrigin location => exact Nat.le_refl _
  | equalityLeft selected member location => exact location.dependency_weight_le selected.ordered
  | equalityRight selected member location => exact location.dependency_weight_le selected.ordered

/-- Monotonicity uses a retained occurrence and the recursive answer's
computed capacity. It never accepts an independent bound on a proof root. -/
theorem ParameterOccurrence.cost_le
    (occurrence : ParameterOccurrence headerFormed header roots ordered node)
    (bounded : capacity ≤ environmentCost captured) :
    (node.dependencyOrigin ordered).weight * (1 + capacity) ≤
      (Closure.close occurrence.domain.origin captured).cost :=
  Nat.mul_le_mul occurrence.weight_le (Nat.add_le_add_left bounded 1)

theorem grouped_projection_parameter_two_prefixes_schedule
    (formed : env.Ordered)
    (registered : env.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (parameterCount : params.length = info.nparams)
    (indexCount : indices.length = info.nindices)
    (selected : info.fieldType name levels params index sourceMajor = some fieldType)
    (fieldWF : fieldLevel.WF U)
    (field : EndpointRef env U source fieldType (.sort fieldLevel))
    (major : Derivation env U source sourceMajor majorExpression
      (VExpr.mkApps (.const name levels) (params ++ indices)))
    (closed : info.ctorType.Closed)
    (allowed : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero)
    (steps : List (GroupedParameterStep
      (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).ordered formed
      (.left (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).original)
      field (.left major) (projectionParameterDependencies formed registered levelsWF)))
    (length_le : steps.length ≤
      (params ++ (List.range index).map (fun j => VExpr.proj name j sourceMajor)).length)
    (otherSteps : List (GroupedParameterStep
      (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).ordered formed
      (.left (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).original)
      field (.left major) (projectionParameterDependencies formed registered levelsWF)))
    (otherLength : otherSteps.length ≤ (params ++ (List.range index).map (fun j => VExpr.proj name j sourceMajor)).length)
    (left right : ParameterDomain
      (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).ordered
      (.left (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).original)
      (projectionParameterDependencies formed registered levelsWF)) (initial : List Closure) :
    richSchedule .expressionReindex
      ((Closure.close left.origin (groupedParameterEnvironment steps initial)).cost +
       (Closure.close right.origin (groupedParameterEnvironment otherSteps initial)).cost) <
    richSchedule .fundamental
      (Closure.close ((EndpointState.proj registered levelsWF levelCount parameterCount indexCount
        selected fieldWF (.ref field) major closed allowed).dependencyOrigin formed) initial).cost  := by
  by_cases order : environmentCost (groupedParameterEnvironment steps initial) ≤
      environmentCost (groupedParameterEnvironment otherSteps initial)
  · have schedule := grouped_projection_parameter_schedule formed registered levelsWF levelCount parameterCount indexCount selected fieldWF field major closed allowed otherSteps otherLength left right initial
    apply Nat.lt_of_le_of_lt _ schedule
    change 3 * (_ + _) + 2 ≤ 3 * (_ + _) + 2
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 3 (Nat.add_le_add_right
      (Nat.mul_le_mul_left left.origin.weight (Nat.add_le_add_left order 1)) _)) 2
  · have order' := Nat.le_of_lt (Nat.lt_of_not_ge order)
    have schedule := grouped_projection_parameter_schedule formed registered levelsWF levelCount parameterCount indexCount selected fieldWF field major closed allowed steps length_le left right initial
    apply Nat.lt_of_le_of_lt _ schedule
    change 3 * (_ + _) + 2 ≤ 3 * (_ + _) + 2
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 3 (Nat.add_le_add_left
      (Nat.mul_le_mul_left right.origin.weight (Nat.add_le_add_left order' 1)) _)) 2

theorem grouped_projection_seed_parameter_two_prefixes_schedule
    (formed : env.Ordered)
    (registered : env.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (parameterCount : params.length = info.nparams)
    (indexCount : indices.length = info.nindices)
    (selected : info.fieldType name levels params index sourceMajor = some fieldType)
    (fieldWF : fieldLevel.WF U)
    (field : EndpointRef env U source fieldType (.sort fieldLevel))
    (major : Derivation env U source sourceMajor majorExpression
      (VExpr.mkApps (.const name levels) (params ++ indices)))
    (closed : info.ctorType.Closed)
    (allowed : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero)
    (seedFormed : seedEnv.Ordered)
    (seedHeader : EndpointRef seedEnv U seedSource seedExpression seedType)
    (seedRoots : List (SelectedParameterDependency env U))
    (seedBound : (seedHeader.dependencyOrigin seedFormed).weight + 2 * parameterWeights seedRoots ≤
      (major.dependencyOrigin formed).weight)
    (seedSteps : List (GroupedParameterStep seedFormed formed seedHeader field (.left major) seedRoots))
    (seedLength : seedSteps.length ≤ (params ++ indices).length)
    (otherSteps : List (GroupedParameterStep seedFormed formed seedHeader field (.left major) seedRoots))
    (otherLength : otherSteps.length ≤ (params ++ indices).length)
    (left right : ParameterDomain seedFormed seedHeader seedRoots)
    (equalityEndpoint : left.isEquality ∨ right.isEquality) (initial : List Closure) :
    richSchedule .expressionReindex
      ((Closure.close left.origin (groupedParameterEnvironment seedSteps initial)).cost +
       (Closure.close right.origin (groupedParameterEnvironment otherSteps initial)).cost) <
    richSchedule .fundamental
      (Closure.close ((EndpointState.proj registered levelsWF levelCount parameterCount indexCount
        selected fieldWF (.ref field) major closed allowed).dependencyOrigin formed) initial).cost  := by
  by_cases order : environmentCost (groupedParameterEnvironment seedSteps initial) ≤
      environmentCost (groupedParameterEnvironment otherSteps initial)
  · have schedule := grouped_projection_seed_parameter_schedule formed registered levelsWF levelCount parameterCount indexCount selected fieldWF field major closed allowed seedFormed seedHeader seedRoots seedBound otherSteps otherLength left right equalityEndpoint initial
    apply Nat.lt_of_le_of_lt _ schedule
    change 3 * (_ + _) + 2 ≤ 3 * (_ + _) + 2
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 3 (Nat.add_le_add_right
      (Nat.mul_le_mul_left left.origin.weight (Nat.add_le_add_left order 1)) _)) 2
  · have order' := Nat.le_of_lt (Nat.lt_of_not_ge order)
    have schedule := grouped_projection_seed_parameter_schedule formed registered levelsWF levelCount parameterCount indexCount selected fieldWF field major closed allowed seedFormed seedHeader seedRoots seedBound seedSteps seedLength left right equalityEndpoint initial
    apply Nat.lt_of_le_of_lt _ schedule
    change 3 * (_ + _) + 2 ≤ 3 * (_ + _) + 2
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 3 (Nat.add_le_add_left
      (Nat.mul_le_mul_left right.origin.weight (Nat.add_le_add_left order' 1)) _)) 2

theorem grouped_projection_parameter_occurrences_schedule
    (formed : env.Ordered)
    (registered : env.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (parameterCount : params.length = info.nparams)
    (indexCount : indices.length = info.nindices)
    (selected : info.fieldType name levels params index sourceMajor = some fieldType)
    (fieldWF : fieldLevel.WF U)
    (field : EndpointRef env U source fieldType (.sort fieldLevel))
    (major : Derivation env U source sourceMajor majorExpression
      (VExpr.mkApps (.const name levels) (params ++ indices)))
    (closed : info.ctorType.Closed)
    (allowed : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero)
    (steps : List (GroupedParameterStep
      (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).ordered formed
      (.left (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).original)
      field (.left major) (projectionParameterDependencies formed registered levelsWF)))
    (length_le : steps.length ≤
      (params ++ (List.range index).map (fun j => VExpr.proj name j sourceMajor)).length)
    (otherSteps : List (GroupedParameterStep
      (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).ordered formed
      (.left (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).original)
      field (.left major) (projectionParameterDependencies formed registered levelsWF)))
    (otherLength : otherSteps.length ≤ (params ++ (List.range index).map (fun j => VExpr.proj name j sourceMajor)).length)
    {leftEnv rightEnv : VEnv} {leftSource rightSource : List VExpr}
    {leftExpression leftAssigned rightExpression rightAssigned : VExpr}
    {leftOrdered : leftEnv.Ordered} {rightOrdered : rightEnv.Ordered}
    {leftNode : EndpointState leftEnv U leftSource leftExpression leftAssigned}
    {rightNode : EndpointState rightEnv U rightSource rightExpression rightAssigned}
    (left : ParameterOccurrence (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).ordered
      (.left (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).original)
      (projectionParameterDependencies formed registered levelsWF) leftOrdered leftNode)
    (right : ParameterOccurrence (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).ordered
      (.left (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).original)
      (projectionParameterDependencies formed registered levelsWF) rightOrdered rightNode) (initial : List Closure)
    (leftCapacityBound : leftCapacity ≤ environmentCost (groupedParameterEnvironment steps initial))
    (rightCapacityBound : rightCapacity ≤ environmentCost (groupedParameterEnvironment otherSteps initial)) :
    richSchedule .expressionReindex
      ((leftNode.dependencyOrigin leftOrdered).weight * (1 + leftCapacity) +
       (rightNode.dependencyOrigin rightOrdered).weight * (1 + rightCapacity)) <
    richSchedule .fundamental
      (Closure.close ((EndpointState.proj registered levelsWF levelCount parameterCount indexCount
        selected fieldWF (.ref field) major closed allowed).dependencyOrigin formed) initial).cost  := by
  have schedule := grouped_projection_parameter_two_prefixes_schedule formed registered levelsWF levelCount parameterCount indexCount selected fieldWF field major closed allowed steps length_le otherSteps otherLength
    left.domain right.domain initial
  apply Nat.lt_of_le_of_lt _ schedule
  change 3 * (_ + _) + 2 ≤ 3 * (_ + _) + 2
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 3
    (Nat.add_le_add (left.cost_le leftCapacityBound) (right.cost_le rightCapacityBound))) 2

theorem grouped_projection_seed_parameter_occurrences_schedule
    (formed : env.Ordered)
    (registered : env.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (parameterCount : params.length = info.nparams)
    (indexCount : indices.length = info.nindices)
    (selected : info.fieldType name levels params index sourceMajor = some fieldType)
    (fieldWF : fieldLevel.WF U)
    (field : EndpointRef env U source fieldType (.sort fieldLevel))
    (major : Derivation env U source sourceMajor majorExpression
      (VExpr.mkApps (.const name levels) (params ++ indices)))
    (closed : info.ctorType.Closed)
    (allowed : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero)
    (seedFormed : seedEnv.Ordered)
    (seedHeader : EndpointRef seedEnv U seedSource seedExpression seedType)
    (seedRoots : List (SelectedParameterDependency env U))
    (seedBound : (seedHeader.dependencyOrigin seedFormed).weight + 2 * parameterWeights seedRoots ≤
      (major.dependencyOrigin formed).weight)
    (seedSteps : List (GroupedParameterStep seedFormed formed seedHeader field (.left major) seedRoots))
    (seedLength : seedSteps.length ≤ (params ++ indices).length)
    (otherSteps : List (GroupedParameterStep seedFormed formed seedHeader field (.left major) seedRoots))
    (otherLength : otherSteps.length ≤ (params ++ indices).length)
    {leftEnv rightEnv : VEnv} {leftSource rightSource : List VExpr}
    {leftExpression leftAssigned rightExpression rightAssigned : VExpr}
    {leftOrdered : leftEnv.Ordered} {rightOrdered : rightEnv.Ordered}
    {leftNode : EndpointState leftEnv U leftSource leftExpression leftAssigned}
    {rightNode : EndpointState rightEnv U rightSource rightExpression rightAssigned}
    (left : ParameterOccurrence seedFormed seedHeader seedRoots leftOrdered leftNode)
    (right : ParameterOccurrence seedFormed seedHeader seedRoots rightOrdered rightNode)
    (equalityEndpoint : left.domain.isEquality ∨ right.domain.isEquality) (initial : List Closure)
    (leftCapacityBound : leftCapacity ≤ environmentCost (groupedParameterEnvironment seedSteps initial))
    (rightCapacityBound : rightCapacity ≤ environmentCost (groupedParameterEnvironment otherSteps initial)) :
    richSchedule .expressionReindex
      ((leftNode.dependencyOrigin leftOrdered).weight * (1 + leftCapacity) +
       (rightNode.dependencyOrigin rightOrdered).weight * (1 + rightCapacity)) <
    richSchedule .fundamental
      (Closure.close ((EndpointState.proj registered levelsWF levelCount parameterCount indexCount
        selected fieldWF (.ref field) major closed allowed).dependencyOrigin formed) initial).cost  := by
  have schedule := grouped_projection_seed_parameter_two_prefixes_schedule formed registered levelsWF levelCount parameterCount indexCount selected fieldWF field major closed allowed seedFormed seedHeader seedRoots seedBound seedSteps seedLength otherSteps otherLength
    left.domain right.domain equalityEndpoint initial
  apply Nat.lt_of_le_of_lt _ schedule
  change 3 * (_ + _) + 2 ≤ 3 * (_ + _) + 2
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 3
    (Nat.add_le_add (left.cost_le leftCapacityBound) (right.cost_le rightCapacityBound))) 2

theorem grouped_projection_cross_parameter_occurrences_schedule
    (formed : env.Ordered)
    (registered : env.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (parameterCount : params.length = info.nparams)
    (indexCount : indices.length = info.nindices)
    (selected : info.fieldType name levels params index sourceMajor = some fieldType)
    (fieldWF : fieldLevel.WF U)
    (field : EndpointRef env U source fieldType (.sort fieldLevel))
    (major : Derivation env U source sourceMajor majorExpression
      (VExpr.mkApps (.const name levels) (params ++ indices)))
    (closed : info.ctorType.Closed)
    (allowed : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero)
    (seedFormed : seedEnv.Ordered)
    (seedHeader : EndpointRef seedEnv U seedSource seedExpression seedType)
    (seedRoots : List (SelectedParameterDependency env U))
    (seedBound : (seedHeader.dependencyOrigin seedFormed).weight + parameterWeights seedRoots ≤
      (major.dependencyOrigin formed).weight)
    (seedSteps : List (GroupedParameterStep seedFormed formed seedHeader field (.left major) seedRoots))
    (seedLength : seedSteps.length ≤ (params ++ indices).length)
    {seedNodeEnv : VEnv} {seedNodeSource : List VExpr} {seedNodeExpression seedNodeAssigned : VExpr}
    {seedNodeOrdered : seedNodeEnv.Ordered}
    {seedNode : EndpointState seedNodeEnv U seedNodeSource seedNodeExpression seedNodeAssigned}
    (seedOccurrence : ParameterOccurrence seedFormed seedHeader seedRoots seedNodeOrdered seedNode)
    (steps : List (GroupedParameterStep
      (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).ordered formed
      (.left (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).original)
      field (.left major) (projectionParameterDependencies formed registered levelsWF)))
    (length_le : steps.length ≤
      (params ++ (List.range index).map (fun j => VExpr.proj name j sourceMajor)).length)
    {requestedNodeEnv : VEnv} {requestedNodeSource : List VExpr}
    {requestedNodeExpression requestedNodeAssigned : VExpr} {requestedNodeOrdered : requestedNodeEnv.Ordered}
    {requestedNode : EndpointState requestedNodeEnv U requestedNodeSource requestedNodeExpression requestedNodeAssigned}
    (requestedOccurrence : ParameterOccurrence (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).ordered
      (.left (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).original)
      (projectionParameterDependencies formed registered levelsWF) requestedNodeOrdered requestedNode) (initial : List Closure)
    (seedCapacityBound : seedCapacity ≤ environmentCost (groupedParameterEnvironment seedSteps initial))
    (requestedCapacityBound : requestedCapacity ≤ environmentCost (groupedParameterEnvironment steps initial)) :
    richSchedule .expressionReindex
      ((seedNode.dependencyOrigin seedNodeOrdered).weight * (1 + seedCapacity) +
       (requestedNode.dependencyOrigin requestedNodeOrdered).weight * (1 + requestedCapacity)) <
    richSchedule .fundamental
      (Closure.close ((EndpointState.proj registered levelsWF levelCount parameterCount indexCount
        selected fieldWF (.ref field) major closed allowed).dependencyOrigin formed) initial).cost  := by
  have schedule := grouped_projection_cross_parameter_schedule formed registered levelsWF levelCount parameterCount
    indexCount selected fieldWF field major closed allowed seedFormed seedHeader seedRoots seedBound
    seedSteps seedLength seedOccurrence.domain steps length_le requestedOccurrence.domain initial
  apply Nat.lt_of_le_of_lt _ schedule
  change 3 * (_ + _) + 2 ≤ 3 * (_ + _) + 2
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 3
    (Nat.add_le_add (seedOccurrence.cost_le seedCapacityBound)
      (requestedOccurrence.cost_le requestedCapacityBound))) 2

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.Dependency
