import Lean4Lean.Theory.Typing.AnchoredOriginalDependencyHeaderCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalRichSchedule

/-! Pre-alignment declaration ledgers. Only original locations occur in the
ledger: neither an alignment answer nor an already-constructed semantic
capture frame is needed to pay for the calls that build that frame. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.Dependency
open VExpr VEnv OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

structure GroupedHeaderStep
    {headerEnv sourceEnv : VEnv} (headerFormed : headerEnv.Ordered) (sourceFormed : sourceEnv.Ordered)
    (header : EndpointRef headerEnv U headerSource headerExpression headerType)
    (field : EndpointRef sourceEnv U source fieldExpression fieldType)
    (major : EndpointRef sourceEnv U source majorExpression majorType) where
  domain : LocatedOrigin headerFormed header
  owners : List (Sum (LocatedOrigin sourceFormed field) (LocatedOrigin sourceFormed major))

noncomputable def groupedOwnerClosure
    (owner : Sum (LocatedOrigin sourceFormed field) (LocatedOrigin sourceFormed major))
    (initial : List Closure) : Closure :=
  match owner with
  | .inl owner => owner.closure initial
  | .inr owner => owner.closure initial

theorem groupedOwner_bound
    (owner : Sum (LocatedOrigin sourceFormed field) (LocatedOrigin sourceFormed major))
    (initial : List Closure) :
    (groupedOwnerClosure owner initial).cost ≤
      ((field.dependencyOrigin sourceFormed).weight + (major.dependencyOrigin sourceFormed).weight) *
        (1 + environmentCost initial) := by
  cases owner with
  | inl owner =>
    exact Nat.le_trans (owner.cost_le initial)
      (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
  | inr owner =>
    exact Nat.le_trans (owner.cost_le initial)
      (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))

noncomputable def groupedHeaderEnvironment
    (steps : List (GroupedHeaderStep headerFormed sourceFormed header field major))
    (initial : List Closure) : List Closure :=
  match steps with
  | [] => []
  | step :: rest =>
    let previous := groupedHeaderEnvironment rest initial
    let declared := Closure.close (step.domain.node.dependencyOrigin headerFormed) previous
    declared :: step.owners.map (fun owner => Closure.bundle (groupedOwnerClosure owner initial) declared) ++ previous

private theorem environment_bound_of_members {closures : List Closure}
    (bound : ∀ closure ∈ closures, closure.cost ≤ maximum) : environmentCost closures ≤ maximum := by
  induction closures with
  | nil => simp [environmentCost]
  | cons closure rest ih =>
    exact Nat.max_le.mpr ⟨bound closure (List.mem_cons_self), ih (fun c hc => bound c (List.mem_cons_of_mem _ hc))⟩

/-- Multiplicity of queries at one declared slot does not consume extra
slots: the environment measure is a maximum of actual owner bundles. -/
theorem groupedHeaderEnvironment_bound
    (steps : List (GroupedHeaderStep headerFormed sourceFormed header field major)) (initial : List Closure) :
    1 + environmentCost (groupedHeaderEnvironment steps initial) ≤
      headerCaptureReserve (header.dependencyOrigin headerFormed).weight
        (field.dependencyOrigin sourceFormed).weight (major.dependencyOrigin sourceFormed).weight steps.length *
        (1 + environmentCost initial) := by
  induction steps with
  | nil =>
    simp only [groupedHeaderEnvironment, environmentCost, List.length_nil, headerCaptureReserve,
      Nat.pow_zero, Nat.one_mul, Nat.add_zero]
    exact Nat.le_trans (by omega) (Nat.le_mul_of_pos_right _ (by omega))
  | cons step rest ih =>
    let H := (header.dependencyOrigin headerFormed).weight
    let R := headerCaptureReserve H (field.dependencyOrigin sourceFormed).weight
      (major.dependencyOrigin sourceFormed).weight rest.length
    let S := 1 + environmentCost initial
    let previous := groupedHeaderEnvironment rest initial
    let declared := Closure.close (step.domain.node.dependencyOrigin headerFormed) previous
    have positive : 1 ≤ R * S := Nat.mul_pos headerCaptureReserve_positive (by dsimp [S]; omega)
    have domainBound : declared.cost ≤ H * (R * S) := Nat.mul_le_mul step.domain.weight_le ih
    have argBound : ∀ owner ∈ step.owners, (groupedOwnerClosure owner initial).cost ≤ R * S := by
      intro owner _
      exact Nat.le_trans (groupedOwner_bound owner initial)
        (Nat.mul_le_mul_right S headerCaptureReserve_base_le)
    have prevBound : environmentCost previous ≤ R * S := by change 1 + environmentCost previous ≤ R * S at ih; omega
    have envBound : environmentCost (groupedHeaderEnvironment (step :: rest) initial) ≤
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
    have joined : 1 + environmentCost (groupedHeaderEnvironment (step :: rest) initial) ≤
        (H + 2) * (R * S) := by rw [Nat.add_mul, Nat.two_mul]; omega
    simpa only [List.length_cons, headerCaptureReserve, Nat.pow_succ,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, H, R, S] using joined

/-- This is available BEFORE any of the pending owner alignments has been
computed. Either original field or original major occurrences are allowed. -/
theorem grouped_header_pair_bound
    (steps : List (GroupedHeaderStep headerFormed sourceFormed header field major))
    (selectedHeader : LocatedOrigin headerFormed header)
    (selectedOwner : Sum (LocatedOrigin sourceFormed field) (LocatedOrigin sourceFormed major))
    (initial : List Closure) :
    (groupedOwnerClosure selectedOwner initial).cost +
      (Closure.close (selectedHeader.node.dependencyOrigin headerFormed)
        (groupedHeaderEnvironment steps initial)).cost ≤
    ((field.dependencyOrigin sourceFormed).weight + (major.dependencyOrigin sourceFormed).weight +
      (header.dependencyOrigin headerFormed).weight *
      headerCaptureReserve (header.dependencyOrigin headerFormed).weight
        (field.dependencyOrigin sourceFormed).weight (major.dependencyOrigin sourceFormed).weight steps.length) *
        (1 + environmentCost initial) := by
  have h := Nat.mul_le_mul selectedHeader.weight_le (groupedHeaderEnvironment_bound steps initial)
  have sum := Nat.add_le_add (groupedOwner_bound selectedOwner initial) h
  simpa only [Closure.cost, Nat.add_mul, Nat.mul_assoc] using sum

/-- Each pending owner alignment is strictly below the actual ORIGINAL
projection parent, before constructing its group frame. The ledger counts
original declaration slots; query multiplicity is unrestricted. -/
theorem grouped_projection_reindex_schedule
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
    (steps : List (GroupedHeaderStep
      (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).ordered formed
      (.left (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).original)
      field (.left major)))
    (length_eq : steps.length =
      (params ++ (List.range index).map (fun j => VExpr.proj name j sourceMajor)).length)
    (selectedHeader : LocatedOrigin
      (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).ordered
      (.left (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).original))
    (selectedOwner : Sum (LocatedOrigin formed field) (LocatedOrigin formed (.left major))) (initial : List Closure) :
    richSchedule .expressionReindex
      ((groupedOwnerClosure selectedOwner initial).cost +
       (Closure.close (selectedHeader.node.dependencyOrigin
          (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).ordered)
         (groupedHeaderEnvironment steps initial)).cost) <
    richSchedule .fundamental
      (Closure.close ((EndpointState.proj registered levelsWF levelCount parameterCount indexCount
        selected fieldWF (.ref field) major closed allowed).dependencyOrigin formed) initial).cost := by
  apply richSchedule_strict
  apply Nat.lt_of_le_of_lt (grouped_header_pair_bound steps selectedHeader selectedOwner initial)
  change _ < _ * (1 + environmentCost initial)
  apply Nat.mul_lt_mul_of_pos_right _ (by omega)
  rw [length_eq, projection_capture_length parameterCount]
  simp only [EndpointState.dependencyOrigin, EndpointRef.dependencyOrigin, Origin.weight,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, reserveOrigin_weight,
    projectionDependencyReserve, headerCaptureReserve]
  omega

theorem grouped_projection_prefix_schedule
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
    (steps : List (GroupedHeaderStep
      (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).ordered formed
      (.left (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).original)
      field (.left major)))
    (length_le : steps.length ≤
      (params ++ (List.range index).map (fun j => VExpr.proj name j sourceMajor)).length)
    (selectedHeader : LocatedOrigin
      (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).ordered
      (.left (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).original))
    (selectedOwner : Sum (LocatedOrigin formed field) (LocatedOrigin formed (.left major))) (initial : List Closure) :
    richSchedule .expressionReindex
      ((groupedOwnerClosure selectedOwner initial).cost +
       (Closure.close (selectedHeader.node.dependencyOrigin
          (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).ordered)
         (groupedHeaderEnvironment steps initial)).cost) <
    richSchedule .fundamental
      (Closure.close ((EndpointState.proj registered levelsWF levelCount parameterCount indexCount
        selected fieldWF (.ref field) major closed allowed).dependencyOrigin formed) initial).cost := by
  apply richSchedule_strict
  apply Nat.lt_of_le_of_lt (grouped_header_pair_bound steps selectedHeader selectedOwner initial)
  change _ < _ * (1 + environmentCost initial)
  apply Nat.mul_lt_mul_of_pos_right _ (by omega)
  have reserveMono : headerCaptureReserve
      (EndpointRef.dependencyOrigin
        (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).ordered
        (.left (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).original)).weight
      (field.dependencyOrigin formed).weight ((EndpointRef.left major).dependencyOrigin formed).weight steps.length ≤
    headerCaptureReserve
      (EndpointRef.dependencyOrigin
        (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).ordered
        (.left (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).original)).weight
      (field.dependencyOrigin formed).weight ((EndpointRef.left major).dependencyOrigin formed).weight
      (info.nparams + index) := by
    apply Nat.mul_le_mul_right
    apply Nat.pow_le_pow_right (by omega)
    simpa only [projection_capture_length parameterCount] using length_le
  have weighted := Nat.mul_le_mul_left
    (EndpointRef.dependencyOrigin
      (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).ordered
      (.left (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).original)).weight reserveMono
  simp only [EndpointState.dependencyOrigin, EndpointRef.dependencyOrigin, Origin.weight,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, reserveOrigin_weight,
    projectionDependencyReserve, headerCaptureReserve] at weighted ⊢
  omega

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.Dependency
