import Lean4Lean.Theory.Typing.AnchoredNativeCaptureSupportReplay
import Lean4Lean.Theory.Typing.AnchoredNativeCapturePlanSyntax

/-! The semantic capture plan agrees with the actual deterministic native
machine. Identity is proved from literal field roles, not coincident witness
values; proof domains use the original equation's closed telescope syntax. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false

private theorem domains_closed
    {domains : List VExpr} {result : VExpr} {count : Nat}
    (scope : (wrapForalls domains result).ClosedN count) :
    ∀ j (bound : j < domains.length), domains[j].ClosedN (count + j) := by
  induction domains generalizing count with
  | nil => intro j hj; simp at hj
  | cons domain rest ih =>
    intro j hj
    cases j with
    | zero => exact scope.1
    | succ j =>
      simpa only [List.getElem_cons_succ, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih scope.2 j (by simpa using hj)

private theorem instructions_scoped
    {instructions : List CaptureInstruction} {count : Nat}
    (scope : ∀ j (bound : j < instructions.length), instructions[j].domain.ClosedN (count + j)) :
    NativeInstructionsScoped count instructions := by
  induction instructions generalizing count with
  | nil => exact .nil
  | cons instruction rest ih =>
    refine .cons (scope 0 (by simp)) (ih ?_)
    intro j hj
    have next := scope (j + 1) (by simpa using hj)
    change rest[j].domain.ClosedN (count + (j + 1)) at next
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using next

/-- A prefix selection consumes the native tuple in the generator's exact
reverse variable order. -/
private theorem prefix_matches {data : NativeRecursorData} {program : SaturatedProgram data}
    (signature : NativeConstantSignature data program.levels)
    (sameLength : program.prefixArgs.length = signature.domains.length)
    (bound : data.indexOffset ≤ signature.domains.length) :
    NativePlanMatches (nativeCaptureSubst program.prefixArgs)
      (nativePrefixPlan (program.prefixArgs.length - data.indexOffset)
        (signature.domains.take data.indexOffset).reverse)
      { added := [], captures := program.prefixArgs.take data.indexOffset } := by
  constructor
  · exact (nativePrefixPlan_added _ _ _).symm
  · simp [sameLength]
  · have equality := nativePrefixPlan_captures
      (program.prefixArgs.length - data.indexOffset) (signature.domains.take data.indexOffset).reverse
      program.prefixArgs (by simp only [List.length_reverse, List.length_take, Nat.min_eq_left bound]; omega)
    rw [nativeCaptureSubst_prefix _ _ (by omega)] at equality
    intro i _
    exact congrFun equality.symm i

theorem NativeCaptureReplayResult.machineMatch
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {data : NativeRecursorData} {program : SaturatedProgram data}
    {signature : NativeConstantSignature data program.levels}
    {witnesses : List VExpr} {available : Valuation} {required : Footprint}
    (selected : data.saturatedProgram program.levels (program.prefixArgs ++ program.trailing) = some program)
    {bodyType : VExpr}
    (scope : (wrapForalls (program.equationBody.domains.map (·.instL program.levels)) bodyType).Closed)
    (result : NativeCaptureReplayResult sourceEnv env U registry target program signature witnesses
      available program.instructions.length required) :
    NativePlanMatches (nativeCaptureSubst program.prefixArgs) result.plan program.state := by
  obtain ⟨_, _, argumentLength, _, _, _, _, _, _, _, instructionEq, run, captureLength, _⟩ :=
    saturatedProgram_spec selected
  have domainLength := takeForalls_length signature.telescope
  have sameLength : program.prefixArgs.length = signature.domains.length := argumentLength.trans domainLength.symm
  have offsetBound : data.indexOffset ≤ signature.domains.length := by
    rw [domainLength, majorOffset]
    omega
  have argumentBound : data.indexOffset ≤ program.prefixArgs.length := by omega
  have count := (SaturatedCaptureState.run_counts run).1
  simp only [List.length_take, Nat.min_eq_left argumentBound] at count
  have total : data.indexOffset + program.instructions.length = program.equationBody.domains.length := by
    omega
  have domains := fieldInstructions_domains program.source
    ((program.equationBody.domains.drop data.indexOffset).map (·.instL program.levels))
  rw [← instructionEq] at domains
  have instructionScope : NativeInstructionsScoped
      (program.prefixArgs.take data.indexOffset).length program.instructions := by
    rw [List.length_take, Nat.min_eq_left argumentBound]
    apply instructions_scoped
    intro j hj
    have hj' : j < (program.instructions.map CaptureInstruction.domain).length := by simpa using hj
    have access := congrArg (fun ds => ds[j]?) domains
    rw [List.getElem?_map, List.getElem?_eq_getElem hj] at access
    simp only [Option.map_some, List.map_drop, List.getElem?_drop, List.getElem?_map] at access
    have sourceBound : data.indexOffset + j < program.equationBody.domains.length := by omega
    rw [List.getElem?_eq_getElem sourceBound, Option.map_some, Option.some.injEq] at access
    have formed := domains_closed scope (data.indexOffset + j) (by simpa using sourceBound)
    simpa only [List.getElem_map, Nat.zero_add, ← access] using formed
  let position := fun slot => program.prefixArgs.length - 1 - (data.indexOffset + slot)
  have selectors : ∀ slot value,
      ((program.prefixArgs.drop data.indexOffset).take data.numIndices)[slot]? = some value →
      nativeCaptureSubst program.prefixArgs (position slot) = value := by
    intro slot value selectedIndex
    obtain ⟨bound, eq⟩ := List.getElem?_eq_some_iff.mp selectedIndex
    have sourceBound : data.indexOffset + slot < program.prefixArgs.length := by
      simp only [List.length_take, List.length_drop] at bound
      omega
    simp only [List.getElem_take, List.getElem_drop] at eq
    rw [nativeCaptureSubst, dif_pos (by dsimp [position]; omega)]
    have indexEq : program.prefixArgs.length - 1 - position slot = data.indexOffset + slot := by
      dsimp [position]
      omega
    simpa only [indexEq] using eq
  obtain ⟨machineContext, machinePlan, contextEq, matched, roles⟩ :=
    SaturatedCaptureState.run_plan_roles (prefix_matches signature sameLength offsetBound)
      instructionScope position selectors run
  have common := saturatedProgram_commonPrefix selected signature.typeOrigin signature.telescope
  have sourceEq : (program.instructions.map CaptureInstruction.domain).reverse ++
      (signature.domains.take data.indexOffset).reverse =
      ((program.equationBody.domains.take (data.indexOffset + program.instructions.length)).map
        (·.instL program.levels)).reverse := by
    rw [domains, ← common, ← List.reverse_append, List.map_drop, List.take_append_drop, total,
      List.take_length]
  rw [sourceEq] at contextEq
  subst machineContext
  have plansEq : machinePlan = result.plan := by
    apply CapturePlan.eq_of_roles
    rw [roles, result.roles]
    simp only [nativeCaptureRoles, List.take_length, position]
    rfl
  simpa only [plansEq] using matched

theorem NativeCaptureReplayResult.machineMatchRun
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {data : NativeRecursorData} {program : SaturatedProgram data}
    {signature : NativeConstantSignature data program.levels}
    {witnesses : List VExpr} {available : Valuation} {required : Footprint}
    (selected : data.saturatedProgram program.levels (program.prefixArgs ++ program.trailing) = some program)
    (newValues : List VExpr) (newLength : newValues.length = program.prefixArgs.length)
    {final : SaturatedCaptureState}
    (runNew : SaturatedCaptureState.run ((newValues.drop data.indexOffset).take data.numIndices)
      program.instructions { added := [], captures := newValues.take data.indexOffset } = some final)
    {bodyType : VExpr}
    (scope : (wrapForalls (program.equationBody.domains.map (·.instL program.levels)) bodyType).Closed)
    (result : NativeCaptureReplayResult sourceEnv env U registry target program signature witnesses
      available program.instructions.length required) :
    NativePlanMatches (nativeCaptureSubst newValues) result.plan final := by
  obtain ⟨_, _, argumentLength, _, _, _, _, _, _, _, instructionEq, run, captureLength, _⟩ :=
    saturatedProgram_spec selected
  have domainLength := takeForalls_length signature.telescope
  have sameLength : program.prefixArgs.length = signature.domains.length := argumentLength.trans domainLength.symm
  have offsetBound : data.indexOffset ≤ signature.domains.length := by
    rw [domainLength, majorOffset]
    omega
  have argumentBound : data.indexOffset ≤ program.prefixArgs.length := by omega
  have count := (SaturatedCaptureState.run_counts run).1
  simp only [List.length_take, Nat.min_eq_left argumentBound] at count
  have total : data.indexOffset + program.instructions.length = program.equationBody.domains.length := by
    omega
  have domains := fieldInstructions_domains program.source
    ((program.equationBody.domains.drop data.indexOffset).map (·.instL program.levels))
  rw [← instructionEq] at domains
  have newBound : data.indexOffset ≤ newValues.length := by omega
  have instructionScope : NativeInstructionsScoped
      (newValues.take data.indexOffset).length program.instructions := by
    rw [List.length_take, Nat.min_eq_left newBound]
    apply instructions_scoped
    intro j hj
    have hj' : j < (program.instructions.map CaptureInstruction.domain).length := by simpa using hj
    have access := congrArg (fun ds => ds[j]?) domains
    rw [List.getElem?_map, List.getElem?_eq_getElem hj] at access
    simp only [Option.map_some, List.map_drop, List.getElem?_drop, List.getElem?_map] at access
    have sourceBound : data.indexOffset + j < program.equationBody.domains.length := by omega
    rw [List.getElem?_eq_getElem sourceBound, Option.map_some, Option.some.injEq] at access
    have formed := domains_closed scope (data.indexOffset + j) (by simpa using sourceBound)
    simpa only [List.getElem_map, Nat.zero_add, ← access] using formed
  let position := fun slot => newValues.length - 1 - (data.indexOffset + slot)
  have selectors : ∀ slot value,
      ((newValues.drop data.indexOffset).take data.numIndices)[slot]? = some value →
      nativeCaptureSubst newValues (position slot) = value := by
    intro slot value selectedIndex
    obtain ⟨bound, eq⟩ := List.getElem?_eq_some_iff.mp selectedIndex
    have sourceBound : data.indexOffset + slot < newValues.length := by
      simp only [List.length_take, List.length_drop] at bound
      omega
    simp only [List.getElem_take, List.getElem_drop] at eq
    rw [nativeCaptureSubst, dif_pos (by dsimp [position]; omega)]
    have indexEq : newValues.length - 1 - position slot = data.indexOffset + slot := by
      dsimp [position]
      omega
    simpa only [indexEq] using eq
  obtain ⟨machineContext, machinePlan, contextEq, matched, roles⟩ :=
    SaturatedCaptureState.run_plan_roles (prefix_matches (program := { program with prefixArgs := newValues }) signature (newLength.trans sameLength) offsetBound)
      instructionScope position selectors runNew
  have common := saturatedProgram_commonPrefix selected signature.typeOrigin signature.telescope
  have sourceEq : (program.instructions.map CaptureInstruction.domain).reverse ++
      (signature.domains.take data.indexOffset).reverse =
      ((program.equationBody.domains.take (data.indexOffset + program.instructions.length)).map
        (·.instL program.levels)).reverse := by
    rw [domains, ← common, ← List.reverse_append, List.map_drop, List.take_append_drop, total,
      List.take_length]
  rw [sourceEq] at contextEq
  subst machineContext
  have plansEq : machinePlan = result.plan := by
    apply CapturePlan.eq_of_roles
    rw [roles, result.roles]
    simp only [nativeCaptureRoles, List.take_length, position, newLength]
    rfl
  simpa only [plansEq] using matched

end Lean4Lean.AnchoredSource.Adapted
