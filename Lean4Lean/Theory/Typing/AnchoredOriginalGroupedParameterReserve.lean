import Lean4Lean.Theory.Typing.AnchoredOriginalGroupedHeaderReserve
import Lean4Lean.Theory.Typing.AnchoredOriginalParameterSchedules

namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.Dependency
open VExpr VEnv OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

noncomputable def parameterWeights (roots : List (SelectedParameterDependency env U)) : Nat :=
  (roots.map fun root => (root.root.original.dependencyOrigin root.ordered).weight).sum

inductive ParameterDomain
    {headerEnv : VEnv} (headerFormed : headerEnv.Ordered)
    (header : EndpointRef headerEnv U headerSource headerExpression headerType)
    (roots : List (SelectedParameterDependency env U)) where
  | headerDomain (location : LocatedOrigin headerFormed header)
  | equality (selected : SelectedParameterDependency env U) (member : selected ∈ roots)

noncomputable def ParameterDomain.origin
    (domain : ParameterDomain headerFormed header roots) : Origin :=
  match domain with
  | .headerDomain location => location.node.dependencyOrigin headerFormed
  | .equality selected _ => selected.root.original.dependencyOrigin selected.ordered

private theorem member_le_sum {values : List Nat} (member : value ∈ values) : value ≤ values.sum := by
  induction values with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · simp only [List.sum_cons]; omega
    · have := ih member; simp only [List.sum_cons]; omega

theorem ParameterDomain.weight_le (domain : ParameterDomain headerFormed header roots) :
    domain.origin.weight ≤ (header.dependencyOrigin headerFormed).weight + parameterWeights roots := by
  cases domain with
  | headerDomain location => exact Nat.le_trans location.weight_le (Nat.le_add_right _ _)
  | equality selected member =>
    have bound : (selected.root.original.dependencyOrigin selected.ordered).weight ≤ parameterWeights roots :=
      member_le_sum (List.mem_map.mpr ⟨selected, member, rfl⟩)
    exact Nat.le_trans bound (Nat.le_add_left _ _)

structure GroupedParameterStep
    {headerEnv sourceEnv : VEnv} (headerFormed : headerEnv.Ordered) (sourceFormed : sourceEnv.Ordered)
    (header : EndpointRef headerEnv U headerSource headerExpression headerType)
    (field : EndpointRef sourceEnv U source fieldExpression fieldType)
    (major : EndpointRef sourceEnv U source majorExpression majorType)
    (roots : List (SelectedParameterDependency sourceEnv U)) where
  domain : ParameterDomain headerFormed header roots
  owners : List (Sum (LocatedOrigin sourceFormed field) (LocatedOrigin sourceFormed major))

noncomputable def groupedParameterEnvironment
    (steps : List (GroupedParameterStep headerFormed sourceFormed header field major roots))
    (initial : List Closure) : List Closure :=
  match steps with
  | [] => []
  | step :: rest =>
    let previous := groupedParameterEnvironment rest initial
    let declared := Closure.close step.domain.origin previous
    declared :: step.owners.map (fun owner => Closure.bundle (groupedOwnerClosure owner initial) declared) ++ previous

private theorem environment_bound_of_members {closures : List Closure}
    (bound : ∀ closure ∈ closures, closure.cost ≤ maximum) : environmentCost closures ≤ maximum := by
  induction closures with
  | nil => simp [environmentCost]
  | cons closure rest ih =>
    exact Nat.max_le.mpr ⟨bound closure (List.mem_cons_self), ih (fun c hc => bound c (List.mem_cons_of_mem _ hc))⟩

/-- Multiplicity of queries at one declared slot does not consume extra
slots: the environment measure is a maximum of actual owner bundles. -/
theorem groupedParameterEnvironment_bound
    (steps : List (GroupedParameterStep headerFormed sourceFormed header field major roots)) (initial : List Closure) :
    1 + environmentCost (groupedParameterEnvironment steps initial) ≤
      headerCaptureReserve ((header.dependencyOrigin headerFormed).weight + parameterWeights roots)
        (field.dependencyOrigin sourceFormed).weight (major.dependencyOrigin sourceFormed).weight steps.length *
        (1 + environmentCost initial) := by
  induction steps with
  | nil =>
    simp only [groupedParameterEnvironment, environmentCost, List.length_nil, headerCaptureReserve,
      Nat.pow_zero, Nat.one_mul, Nat.add_zero]
    exact Nat.le_trans (by omega) (Nat.le_mul_of_pos_right _ (by omega))
  | cons step rest ih =>
    let H := ((header.dependencyOrigin headerFormed).weight + parameterWeights roots)
    let R := headerCaptureReserve H (field.dependencyOrigin sourceFormed).weight
      (major.dependencyOrigin sourceFormed).weight rest.length
    let S := 1 + environmentCost initial
    let previous := groupedParameterEnvironment rest initial
    let declared := Closure.close step.domain.origin previous
    have positive : 1 ≤ R * S := Nat.mul_pos headerCaptureReserve_positive (by dsimp [S]; omega)
    have domainBound : declared.cost ≤ H * (R * S) := Nat.mul_le_mul step.domain.weight_le ih
    have argBound : ∀ owner ∈ step.owners, (groupedOwnerClosure owner initial).cost ≤ R * S := by
      intro owner _
      exact Nat.le_trans (groupedOwner_bound owner initial)
        (Nat.mul_le_mul_right S headerCaptureReserve_base_le)
    have prevBound : environmentCost previous ≤ R * S := by change 1 + environmentCost previous ≤ R * S at ih; omega
    have envBound : environmentCost (groupedParameterEnvironment (step :: rest) initial) ≤
        R * S + H * (R * S) := by
      apply environment_bound_of_members
      intro closure member
      change closure ∈ declared :: step.owners.map (fun owner => Closure.bundle (groupedOwnerClosure owner initial) declared) ++ previous at member
      rcases List.mem_cons.mp member with rfl | member
      · omega
      rcases List.mem_append.mp member with member | member
      · obtain ⟨owner, ownerMember, rfl⟩ := List.mem_map.mp member
        change _ + _ ≤ _
        exact Nat.add_le_add (argBound owner ownerMember) domainBound
      · exact Nat.le_trans (environment_entry member) (by omega)
    have joined : 1 + environmentCost (groupedParameterEnvironment (step :: rest) initial) ≤
        (H + 2) * (R * S) := by rw [Nat.add_mul, Nat.two_mul]; omega
    simpa only [List.length_cons, headerCaptureReserve, Nat.pow_succ,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, H, R, S] using joined


/-- Both original comparison roots are selected from the actual earlier
header/parameter ledger. This bound precedes all semantic alignment answers. -/
theorem grouped_parameter_pair_bound
    (steps : List (GroupedParameterStep headerFormed sourceFormed header field major roots))
    (left right : ParameterDomain headerFormed header roots) (initial : List Closure) :
    (Closure.close left.origin (groupedParameterEnvironment steps initial)).cost +
      (Closure.close right.origin (groupedParameterEnvironment steps initial)).cost ≤
    parameterDependencyReserve steps.length (header.dependencyOrigin headerFormed).weight
      (parameterWeights roots) (field.dependencyOrigin sourceFormed).weight
      (major.dependencyOrigin sourceFormed).weight * (1 + environmentCost initial) := by
  exact parameter_pair_bound left.origin right.origin _ initial left.weight_le right.weight_le
    (groupedParameterEnvironment_bound steps initial)

/-- Independent normalization/context-conversion roots remain strictly
smaller under the actual finite declaration captures, not just at empty context. -/
theorem grouped_projection_parameter_schedule
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
    (left right : ParameterDomain
      (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).ordered
      (.left (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).original)
      (projectionParameterDependencies formed registered levelsWF)) (initial : List Closure) :
    richSchedule .expressionReindex
      ((Closure.close left.origin (groupedParameterEnvironment steps initial)).cost +
       (Closure.close right.origin (groupedParameterEnvironment steps initial)).cost) <
    richSchedule .fundamental
      (Closure.close ((EndpointState.proj registered levelsWF levelCount parameterCount indexCount
        selected fieldWF (.ref field) major closed allowed).dependencyOrigin formed) initial).cost := by
  apply richSchedule_strict
  apply Nat.lt_of_le_of_lt (grouped_parameter_pair_bound steps left right initial)
  change _ < _ * (1 + environmentCost initial)
  apply Nat.mul_lt_mul_of_pos_right _ (by omega)
  have countBound : steps.length ≤ info.nparams + index := by
    simpa only [projection_capture_length parameterCount] using length_le
  have bound := parameterDependencyReserve_count_mono
    (header := (EndpointRef.dependencyOrigin
      (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).ordered
      (.left (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).original)).weight)
    (equalities := parameterWeights (projectionParameterDependencies formed registered levelsWF))
    (field := (field.dependencyOrigin formed).weight)
    (major := ((EndpointRef.left major).dependencyOrigin formed).weight) countBound
  have majorBound := parameterDependencyReserve_mono (count := info.nparams + index)
    (headerBound := Nat.le_refl (EndpointRef.dependencyOrigin
      (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).ordered
      (.left (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).original)).weight)
    (equalityBound := Nat.le_refl (parameterWeights (projectionParameterDependencies formed registered levelsWF)))
    (fieldBound := Nat.le_refl (field.dependencyOrigin formed).weight)
    (majorBound := Nat.le_add_right ((major.dependencyOrigin formed).weight) ((major.dependencyOrigin formed).weight))
  simp only [EndpointState.dependencyOrigin, EndpointRef.dependencyOrigin, Origin.weight,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, reserveOrigin_weight,
    parameterWeights] at bound majorBound ⊢
  omega

/-- One selected original domain in its own actual declaration ledger. -/
theorem grouped_parameter_domain_bound
    (steps : List (GroupedParameterStep headerFormed sourceFormed header field major roots))
    (selected : ParameterDomain headerFormed header roots) (initial : List Closure) :
    (Closure.close selected.origin (groupedParameterEnvironment steps initial)).cost ≤
      ((header.dependencyOrigin headerFormed).weight + parameterWeights roots) *
        headerCaptureReserve ((header.dependencyOrigin headerFormed).weight + parameterWeights roots)
          (field.dependencyOrigin sourceFormed).weight (major.dependencyOrigin sourceFormed).weight steps.length *
        (1 + environmentCost initial) := by
  simpa only [Closure.cost, Nat.mul_assoc] using
    Nat.mul_le_mul selected.weight_le (groupedParameterEnvironment_bound steps initial)

/-- The seed and requested-universe contexts stay separate. Their actual
closure costs consume the SUM of the existing family and parameter reserves;
no mixed context or uniform universe-instantiation bound is asserted. The
seed bound is produced by the retained primitive constant in the major. -/
theorem grouped_projection_cross_parameter_schedule
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
    (seedDomain : ParameterDomain seedFormed seedHeader seedRoots)
    (steps : List (GroupedParameterStep
      (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).ordered formed
      (.left (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).original)
      field (.left major) (projectionParameterDependencies formed registered levelsWF)))
    (length_le : steps.length ≤
      (params ++ (List.range index).map (fun j => VExpr.proj name j sourceMajor)).length)
    (requestedDomain : ParameterDomain
      (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).ordered
      (.left (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).original)
      (projectionParameterDependencies formed registered levelsWF)) (initial : List Closure) :
    richSchedule .expressionReindex
      ((Closure.close seedDomain.origin (groupedParameterEnvironment seedSteps initial)).cost +
       (Closure.close requestedDomain.origin (groupedParameterEnvironment steps initial)).cost) <
    richSchedule .fundamental
      (Closure.close ((EndpointState.proj registered levelsWF levelCount parameterCount indexCount
        selected fieldWF (.ref field) major closed allowed).dependencyOrigin formed) initial).cost := by
  apply richSchedule_strict
  have seedCount : seedSteps.length ≤ info.nparams + info.nindices := by
    simpa only [List.length_append, parameterCount, indexCount] using seedLength
  have seedCoefficient : (seedHeader.dependencyOrigin seedFormed).weight + parameterWeights seedRoots ≤
      (field.dependencyOrigin formed).weight + (major.dependencyOrigin formed).weight := by omega
  have seedPower := Nat.le_trans (Nat.pow_le_pow_left (Nat.add_le_add_right seedCoefficient 2) seedSteps.length)
    (Nat.pow_le_pow_right (by omega) seedCount)
  have seedReserve :
      ((seedHeader.dependencyOrigin seedFormed).weight + parameterWeights seedRoots) *
        headerCaptureReserve ((seedHeader.dependencyOrigin seedFormed).weight + parameterWeights seedRoots)
          (field.dependencyOrigin formed).weight ((EndpointRef.left major).dependencyOrigin formed).weight seedSteps.length ≤
      projectionFamilyReserve (info.nparams + info.nindices)
        (field.dependencyOrigin formed).weight (major.dependencyOrigin formed).weight :=
    Nat.mul_le_mul seedCoefficient (Nat.mul_le_mul_right _ seedPower)
  have seedCost := Nat.le_trans (grouped_parameter_domain_bound seedSteps seedDomain initial)
    (Nat.mul_le_mul_right (1 + environmentCost initial) seedReserve)
  have countBound : steps.length ≤ info.nparams + index := by
    simpa only [projection_capture_length parameterCount] using length_le
  have requestedPair := grouped_parameter_pair_bound steps requestedDomain requestedDomain initial
  have requestCount := parameterDependencyReserve_count_mono
    (header := (EndpointRef.dependencyOrigin
      (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).ordered
      (.left (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).original)).weight)
    (equalities := parameterWeights (projectionParameterDependencies formed registered levelsWF))
    (field := (field.dependencyOrigin formed).weight)
    (major := ((EndpointRef.left major).dependencyOrigin formed).weight) countBound
  have requestedCost := Nat.le_trans (Nat.le_add_right _ _) requestedPair
  have requestBudget := Nat.le_trans requestedCost
    (Nat.mul_le_mul_right (1 + environmentCost initial) requestCount)
  apply Nat.lt_of_le_of_lt (Nat.add_le_add seedCost requestBudget)
  rw [← Nat.add_mul]
  change _ < _ * (1 + environmentCost initial)
  apply Nat.mul_lt_mul_of_pos_right _ (by omega)
  simp only [EndpointState.dependencyOrigin, EndpointRef.dependencyOrigin, Origin.weight,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, reserveOrigin_weight,
    parameterWeights, projectionDependencyReserve]

  omega

def ParameterDomain.isEquality (domain : ParameterDomain headerFormed header roots) : Prop :=
  match domain with
  | .headerDomain _ => False
  | .equality _ _ => True

/-- Each actual parameter conversion edge has an original equality endpoint.
This excludes the unused comparison of two independent whole headers. -/
theorem ParameterDomain.pair_weight_le
    (left right : ParameterDomain headerFormed header roots)
    (equalityEndpoint : left.isEquality ∨ right.isEquality) :
    left.origin.weight + right.origin.weight ≤
      (header.dependencyOrigin headerFormed).weight + 2 * parameterWeights roots := by
  have hl := left.weight_le
  have hr := right.weight_le
  rcases equalityEndpoint with hl' | hr'
  · cases left with
    | headerDomain location => cases hl'
    | equality selected member =>
      have bound : (selected.root.original.dependencyOrigin selected.ordered).weight ≤ parameterWeights roots :=
        member_le_sum (List.mem_map.mpr ⟨selected, member, rfl⟩)
      change (selected.root.original.dependencyOrigin selected.ordered).weight + _ ≤ _
      omega
  · cases right with
    | headerDomain location => cases hr'
    | equality selected member =>
      have bound : (selected.root.original.dependencyOrigin selected.ordered).weight ≤ parameterWeights roots :=
        member_le_sum (List.mem_map.mpr ⟨selected, member, rfl⟩)
      change _ + (selected.root.original.dependencyOrigin selected.ordered).weight ≤ _
      omega

/-- A seed-internal pair consumes one family reserve, using the stronger
actual constant-ledger bound; its two closures share the computed seed
prefix but need not share original environments or derivations. -/
theorem grouped_seed_parameter_pair_bound
    (steps : List (GroupedParameterStep headerFormed sourceFormed header field major roots))
    (left right : ParameterDomain headerFormed header roots)
    (equalityEndpoint : left.isEquality ∨ right.isEquality)
    (seedBound : (header.dependencyOrigin headerFormed).weight + 2 * parameterWeights roots ≤
      (major.dependencyOrigin sourceFormed).weight)
    (countBound : steps.length ≤ count) (initial : List Closure) :
    (Closure.close left.origin (groupedParameterEnvironment steps initial)).cost +
      (Closure.close right.origin (groupedParameterEnvironment steps initial)).cost ≤
    projectionFamilyReserve count (field.dependencyOrigin sourceFormed).weight
      (major.dependencyOrigin sourceFormed).weight * (1 + environmentCost initial) := by
  have coefficient : (header.dependencyOrigin headerFormed).weight + parameterWeights roots ≤
      (field.dependencyOrigin sourceFormed).weight + (major.dependencyOrigin sourceFormed).weight := by omega
  have pairBound := Nat.le_trans (left.pair_weight_le right equalityEndpoint) seedBound
  have pairCoefficient : left.origin.weight + right.origin.weight ≤
      (field.dependencyOrigin sourceFormed).weight + (major.dependencyOrigin sourceFormed).weight := by omega
  have power := Nat.le_trans (Nat.pow_le_pow_left (Nat.add_le_add_right coefficient 2) steps.length)
    (Nat.pow_le_pow_right (by omega) countBound)
  have environment := Nat.le_trans (groupedParameterEnvironment_bound steps initial)
    (Nat.mul_le_mul_right (1 + environmentCost initial) (Nat.mul_le_mul_right _ power))
  have pair := Nat.mul_le_mul pairCoefficient environment
  simpa only [Closure.cost, projectionFamilyReserve, headerCaptureReserve, Nat.add_mul, Nat.mul_assoc] using pair

theorem grouped_projection_seed_parameter_schedule
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
    (left right : ParameterDomain seedFormed seedHeader seedRoots)
    (equalityEndpoint : left.isEquality ∨ right.isEquality) (initial : List Closure) :
    richSchedule .expressionReindex
      ((Closure.close left.origin (groupedParameterEnvironment seedSteps initial)).cost +
       (Closure.close right.origin (groupedParameterEnvironment seedSteps initial)).cost) <
    richSchedule .fundamental
      (Closure.close ((EndpointState.proj registered levelsWF levelCount parameterCount indexCount
        selected fieldWF (.ref field) major closed allowed).dependencyOrigin formed) initial).cost := by
  apply richSchedule_strict
  have seedCount : seedSteps.length ≤ info.nparams + info.nindices := by
    simpa only [List.length_append, parameterCount, indexCount] using seedLength
  apply Nat.lt_of_le_of_lt (grouped_seed_parameter_pair_bound seedSteps left right equalityEndpoint seedBound seedCount initial)
  change _ < _ * (1 + environmentCost initial)
  apply Nat.mul_lt_mul_of_pos_right _ (by omega)
  simp only [EndpointState.dependencyOrigin, EndpointRef.dependencyOrigin, Origin.weight,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, reserveOrigin_weight,
    projectionDependencyReserve]
  omega

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.Dependency
