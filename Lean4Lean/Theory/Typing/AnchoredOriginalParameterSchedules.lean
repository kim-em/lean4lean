import Lean4Lean.Theory.Typing.AnchoredOriginalDeclarationDependencies

namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false

private theorem member_le_sum {values : List Nat} (member : value ∈ values) : value ≤ values.sum := by
  induction values with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · simp only [List.sum_cons]; omega
    · have := ih member
      simp only [List.sum_cons]; omega

theorem parameterDependencyReserve_covers (count parameters : Nat) :
    parameters ≤ parameterDependencyReserve count 0 parameters 0 0 := by
  have power : 1 ≤ (parameters + 2) ^ count := Nat.pow_pos (by omega)
  have bound := Nat.mul_le_mul_left (2 * parameters) power
  simp only [Nat.mul_one] at bound
  simp only [parameterDependencyReserve, Nat.zero_add, Nat.add_zero, Nat.mul_one]
  omega

/-- The primitive constant pays the selected earlier header and every
actual retained parameter-equality root before interpreting either one. -/
theorem Derivation.constantParameter_pair_lt
    (ordered : env.Ordered) (lookup : env.constants name = some info)
    (leftWF : ∀ level ∈ levels, level.WF U)
    (rightWF : ∀ level ∈ otherLevels, level.WF U)
    (count : levels.length = info.uvars) (equivalent : List.Forall₂ (· ≈ ·) levels otherLevels)
    (levelWF : level.WF U)
    (closed : Derivation env U [] (info.type.instL levels) (info.type.instL otherLevels) (.sort level))
    (ambient : Derivation env U source (info.type.instL levels) (info.type.instL otherLevels) (.sort level))
    (selected : SelectedParameterDependency env U)
    (member : selected ∈ constantParameterDependencies ordered name leftWF rightWF equivalent)
    (captured : List Closure) :
    (Closure.close ((selectOriginalHeader ordered lookup leftWF).original.dependencyOrigin
      (selectOriginalHeader ordered lookup leftWF).ordered) []).cost +
    (Closure.close (selected.root.original.dependencyOrigin selected.ordered) []).cost <
    (Closure.close ((Derivation.constDF lookup leftWF rightWF count equivalent levelWF closed ambient).dependencyOrigin ordered)
      captured).cost := by
  let roots := constantParameterDependencies ordered name leftWF rightWF equivalent
  let total := (roots.map fun root => (root.root.original.dependencyOrigin root.ordered).weight).sum
  have rootBound : (selected.root.original.dependencyOrigin selected.ordered).weight ≤ total :=
    member_le_sum (List.mem_map.mpr ⟨selected, member, rfl⟩)
  have covered := parameterDependencyReserve_covers roots.length total
  have small :
      ((selectOriginalHeader ordered lookup leftWF).original.dependencyOrigin
        (selectOriginalHeader ordered lookup leftWF).ordered).weight +
      (selected.root.original.dependencyOrigin selected.ordered).weight <
      ((Derivation.constDF lookup leftWF rightWF count equivalent levelWF closed ambient).dependencyOrigin ordered).weight := by
    rw [Derivation.dependencyOrigin.eq_def ordered (Derivation.constDF lookup leftWF rightWF count equivalent levelWF closed ambient)]
    simp only [Origin.weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, reserveOrigin_weight]
    change _ < 1 + (_ + (_ + (_ + (1 + parameterDependencyReserve roots.length 0 total 0 0))))
    omega
  have parentBound :
      ((Derivation.constDF lookup leftWF rightWF count equivalent levelWF closed ambient).dependencyOrigin ordered).weight ≤
      (Closure.close ((Derivation.constDF lookup leftWF rightWF count equivalent levelWF closed ambient).dependencyOrigin ordered) captured).cost := by
    change _ ≤ _ * (1 + environmentCost captured)
    exact Nat.le_mul_of_pos_right _ (by omega)
  simpa only [Closure.cost, environmentCost, Nat.add_zero, Nat.mul_one] using Nat.lt_of_lt_of_le small parentBound

/-- The actual seed normalization is a member of the constDF dependency
ledger selected from that very registered family, not a fresh proof choice. -/
theorem constantParameter_seedNormalization_member
    {env : VEnv} {name : Lean.Name} {projection : VProjectionInfo}
    {levels otherLevels : List VLevel}
    (ordered : env.Ordered) (registered : env.projections name projection)
    (leftWF : ∀ level ∈ levels, level.WF U)
    (rightWF : ∀ level ∈ otherLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) levels otherLevels) :
    let packet := selectProjectionParameters ordered registered leftWF
    packet.baseDependency ⟨[], .nil, _, _, _, packet.instantiated.normalization⟩ ∈
      constantParameterDependencies ordered name leftWF rightWF equivalent := by
  rw [constantParameterDependencies_registered ordered registered leftWF rightWF equivalent]
  dsimp only
  apply List.mem_append_left
  apply List.mem_map.mpr
  refine ⟨_, ?_, rfl⟩
  apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_cons_self

/-- Ready-to-use schedule for the exact normalization selected at the
primitive constant's original seed, including a right-endpoint constant
whose displayed levels merely agree semantically with that seed. -/
theorem Derivation.constantNormalization_pair_lt
    (ordered : env.Ordered) (lookup : env.constants name = some info)
    (registered : env.projections name projection)
    (leftWF : ∀ level ∈ levels, level.WF U)
    (rightWF : ∀ level ∈ otherLevels, level.WF U)
    (count : levels.length = info.uvars) (equivalent : List.Forall₂ (· ≈ ·) levels otherLevels)
    (levelWF : level.WF U)
    (closed : Derivation env U [] (info.type.instL levels) (info.type.instL otherLevels) (.sort level))
    (ambient : Derivation env U source (info.type.instL levels) (info.type.instL otherLevels) (.sort level))
    (captured : List Closure) :
    let packet := selectProjectionParameters ordered registered leftWF
    (Closure.close ((selectOriginalHeader ordered lookup leftWF).original.dependencyOrigin
      (selectOriginalHeader ordered lookup leftWF).ordered) []).cost +
    (Closure.close (packet.instantiated.normalization.dependencyOrigin packet.origin.baseOrdered) []).cost <
    (Closure.close ((Derivation.constDF lookup leftWF rightWF count equivalent levelWF closed ambient).dependencyOrigin ordered)
      captured).cost := by
  exact Derivation.constantParameter_pair_lt ordered lookup leftWF rightWF count equivalent levelWF closed ambient
    _ (constantParameter_seedNormalization_member ordered registered leftWF rightWF equivalent) captured

/-- The constant reserve pays a PAIR of its actual seed/display/universe
roots. This stronger weight bound lets a seed capture ledger use the major
reserve without doubling that reserve at each comparison. -/
theorem Derivation.constantParameters_pair_weight_lt
    (ordered : env.Ordered) (lookup : env.constants name = some info)
    (leftWF : ∀ level ∈ levels, level.WF U)
    (rightWF : ∀ level ∈ otherLevels, level.WF U)
    (count : levels.length = info.uvars) (equivalent : List.Forall₂ (· ≈ ·) levels otherLevels)
    (levelWF : level.WF U)
    (closed : Derivation env U [] (info.type.instL levels) (info.type.instL otherLevels) (.sort level))
    (ambient : Derivation env U source (info.type.instL levels) (info.type.instL otherLevels) (.sort level))
    (first second : SelectedParameterDependency env U)
    (firstMember : first ∈ constantParameterDependencies ordered name leftWF rightWF equivalent)
    (secondMember : second ∈ constantParameterDependencies ordered name leftWF rightWF equivalent) :
    (first.root.original.dependencyOrigin first.ordered).weight +
      (second.root.original.dependencyOrigin second.ordered).weight <
    ((Derivation.constDF lookup leftWF rightWF count equivalent levelWF closed ambient).dependencyOrigin ordered).weight := by
  let roots := constantParameterDependencies ordered name leftWF rightWF equivalent
  let total := (roots.map fun root => (root.root.original.dependencyOrigin root.ordered).weight).sum
  have firstBound : (first.root.original.dependencyOrigin first.ordered).weight ≤ total :=
    member_le_sum (List.mem_map.mpr ⟨first, firstMember, rfl⟩)
  have secondBound : (second.root.original.dependencyOrigin second.ordered).weight ≤ total :=
    member_le_sum (List.mem_map.mpr ⟨second, secondMember, rfl⟩)
  have power : 1 ≤ (total + 2) ^ roots.length := Nat.pow_pos (by omega)
  have covered : 2 * total ≤ parameterDependencyReserve roots.length 0 total 0 0 := by
    simpa only [parameterDependencyReserve, Nat.zero_add, Nat.add_zero, Nat.mul_one] using
      Nat.mul_le_mul_left (2 * total) power
  rw [Derivation.dependencyOrigin.eq_def ordered
    (Derivation.constDF lookup leftWF rightWF count equivalent levelWF closed ambient)]
  simp only [Origin.weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero, reserveOrigin_weight]
  change _ < 1 + (_ + (_ + (_ + (1 + parameterDependencyReserve roots.length 0 total 0 0))))
  omega

/-- The entire seed/display/bridge domain ledger, together with the actual
family header, is paid by this primitive constant occurrence. -/
theorem Derivation.constantParameters_header_twice_weight_lt
    (ordered : env.Ordered) (lookup : env.constants name = some info)
    (leftWF : ∀ level ∈ levels, level.WF U)
    (rightWF : ∀ level ∈ otherLevels, level.WF U)
    (count : levels.length = info.uvars) (equivalent : List.Forall₂ (· ≈ ·) levels otherLevels)
    (levelWF : level.WF U)
    (closed : Derivation env U [] (info.type.instL levels) (info.type.instL otherLevels) (.sort level))
    (ambient : Derivation env U source (info.type.instL levels) (info.type.instL otherLevels) (.sort level)) :
    ((selectOriginalHeader ordered lookup leftWF).original.dependencyOrigin
      (selectOriginalHeader ordered lookup leftWF).ordered).weight +
      2 * ((constantParameterDependencies ordered name leftWF rightWF equivalent).map
        (fun selected => (selected.root.original.dependencyOrigin selected.ordered).weight)).sum <
    ((Derivation.constDF lookup leftWF rightWF count equivalent levelWF closed ambient).dependencyOrigin ordered).weight := by
  let roots := constantParameterDependencies ordered name leftWF rightWF equivalent
  let total := (roots.map fun root => (root.root.original.dependencyOrigin root.ordered).weight).sum
  have power : 1 ≤ (total + 2) ^ roots.length := Nat.pow_pos (by omega)
  have covered : 2 * total ≤ parameterDependencyReserve roots.length 0 total 0 0 := by
    simpa only [parameterDependencyReserve, Nat.zero_add, Nat.add_zero, Nat.mul_one] using
      Nat.mul_le_mul_left (2 * total) power
  rw [Derivation.dependencyOrigin.eq_def ordered
    (Derivation.constDF lookup leftWF rightWF count equivalent levelWF closed ambient)]
  simp only [Origin.weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero, reserveOrigin_weight]
  change _ + 2 * total < 1 + (_ + (_ + (_ + (1 + parameterDependencyReserve roots.length 0 total 0 0))))
  omega

theorem Derivation.constantParameters_header_weight_lt
    (ordered : env.Ordered) (lookup : env.constants name = some info)
    (leftWF : ∀ level ∈ levels, level.WF U)
    (rightWF : ∀ level ∈ otherLevels, level.WF U)
    (count : levels.length = info.uvars) (equivalent : List.Forall₂ (· ≈ ·) levels otherLevels)
    (levelWF : level.WF U)
    (closed : Derivation env U [] (info.type.instL levels) (info.type.instL otherLevels) (.sort level))
    (ambient : Derivation env U source (info.type.instL levels) (info.type.instL otherLevels) (.sort level)) :
    ((selectOriginalHeader ordered lookup leftWF).original.dependencyOrigin
      (selectOriginalHeader ordered lookup leftWF).ordered).weight +
      ((constantParameterDependencies ordered name leftWF rightWF equivalent).map
        (fun selected => (selected.root.original.dependencyOrigin selected.ordered).weight)).sum <
    ((Derivation.constDF lookup leftWF rightWF count equivalent levelWF closed ambient).dependencyOrigin ordered).weight := by
  have bound := Derivation.constantParameters_header_twice_weight_lt ordered lookup leftWF rightWF count equivalent levelWF closed ambient
  omega

end Lean4Lean.AnchoredSource.OriginalClosureMeasure
