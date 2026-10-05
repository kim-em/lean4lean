import Lean4Lean.Theory.Typing.NativeInitialSelection
import Lean4Lean.Theory.Typing.NativeSingletonProofFields

/-! Literal copied-index occurrences in the actual original equation.
Instruction selection is syntax, so the chosen native argument must be the
same formal field variable as its equation capture. -/
namespace Lean4Lean.InductiveSignature
open VExpr _root_.Lean4Lean.VEnv NativeRecursorData
open private extract_wrap_const from Lean4Lean.Theory.Typing.NativeResultBridge
open private singleton_ctor from Lean4Lean.Theory.Typing.NativeInitialSelection
open private equation_domains from Lean4Lean.Theory.Typing.NativeSingletonProofFields
set_option backward.isDefEq.respectTransparency false

theorem CaseSchema.ProjectionData.fieldIndex_selected
    {source : CaseSchema.ProjectionData} {field slot : Nat}
    (selected : source.fieldIndex field = some slot) :
    source.constructorIndices[slot]? = some (.bvar (source.fields.length - 1 - field)) := by
  simp only [CaseSchema.ProjectionData.fieldIndex, Option.map_eq_some_iff] at selected
  obtain ⟨⟨expression, position⟩, found, rfl⟩ := selected
  have member := List.mem_of_find?_eq_some found
  have atPosition := List.mk_mem_zipIdx_iff_getElem?.mp member
  have shape := List.find?_some found
  cases expression <;> simp only [Bool.false_eq_true] at shape
  rename_i index
  simp only [beq_iff_eq] at shape
  subst index
  exact atPosition

theorem fieldInstructions_index_origin
    {source : CaseSchema.ProjectionData} {domains : List VExpr} {field slot : Nat} {domain : VExpr}
    (selected : (fieldInstructions source domains)[field]? = some (.index domain slot)) :
    domains[field]? = some domain ∧ source.fieldIndex field = some slot := by
  obtain ⟨bound, selected⟩ := List.getElem?_eq_some_iff.mp selected
  have bound' : field < domains.length := by simpa only [fieldInstructions_length] using bound
  simp only [fieldInstructions, List.getElem_map, List.getElem_zipIdx, Nat.zero_add] at selected
  cases choice : source.fieldIndex field with
  | none => simp only [choice] at selected; contradiction
  | some actual =>
    simp only [choice, CaptureInstruction.index.injEq] at selected
    obtain ⟨domainEq, rfl⟩ := selected
    exact ⟨by rw [List.getElem?_eq_getElem bound']; exact congrArg some domainEq, rfl⟩

private theorem Instance.equation_arguments
    {s : InductiveSignature} (g : Instance s) (index : Fin s.constructors.size)
    {body : CaseSchema.EquationBody}
    (selected : CaseSchema.EquationBody.extract (g.equation index).lhs (g.equation index).rhs
      (g.equation index).type = some body) :
    body.lhs.getAppFnArgs.2 =
      vars (s.params.length + s.families.size + s.constructors.size) s.constructors[index].fields.length ++
      (s.constructors[index].indices.map fun e => (e.instL g.levels).liftN
        (s.families.size + s.constructors.size) s.constructors[index].fields.length) ++
      [g.constructorApp s.constructors[index] (s.families.size + s.constructors.size) 0] := by
  unfold Instance.equation at selected
  dsimp only at selected
  rw [extract_wrap_const (by exact VExpr.getAppFnArgs_mkApps_head _ _)] at selected
  cases selected
  simp only [getAppFnArgs_mkApps_head, Instance.recursorHead, getAppFnArgs_mkApps_const]
  simp only [Nat.add_assoc]

/-- At the original constructor equation, an index-copy instruction selects
literally the same field variable from the native index tuple and the capture
telescope. This includes signatures with repeated or computed other indices. -/
theorem NativeRecursorData.initial_index_occurrence
    {env : VEnv} {data : NativeRecursorData} {program : SaturatedProgram data}
    {index : Fin data.schema.signature.constructors.size} {rule : VDefEq}
    {levels : List VLevel} {arguments : List VExpr}
    (registered : _root_.Lean4Lean.VEnv.NativeRecursorRegistered env data)
    (families : data.schema.signature.families.size = 1)
    (constructors : data.schema.signature.constructors.size ≤ 1)
    (owner : data.schema.signature.constructors[index].owner = data.owner)
    (equation : data.equation index = some rule)
    (selected : data.saturatedProgram levels arguments = some program)
    {field slot : Nat} {domain : VExpr}
    (instruction : program.instructions[field]? = some (.index domain slot)) :
    ((program.equationBody.lhs.instL levels).getAppFnArgs.2)[data.indexOffset + slot]? =
      some (.bvar (program.source.fields.length - 1 - field)) := by
  obtain ⟨_, _, _, _, _, _, _, projection, selectedEquation, extracted, instructions, _, _, _⟩ :=
    saturatedProgram_spec selected
  rw [instructions] at instruction
  obtain ⟨_, selector⟩ := fieldInstructions_index_origin instruction
  have chosenIndex := CaseSchema.ProjectionData.fieldIndex_selected selector
  have slotBound := CaseSchema.ProjectionData.fieldIndex_bound selector
  have identity := VEnv.NativeRecursorRegistered.singleton_restoration registered families
  obtain ⟨ctor, ctorMember, fieldsEq, indicesEq⟩ :=
    CaseSchema.projectionData_empty_origin identity projection
  have ctorEq := singleton_ctor constructors index ctorMember
  subst ctor
  have actualEquation := NativeRecursorData.singletonEquation_of_equation constructors owner equation
  have ruleEq : program.equation = rule := Option.some.inj (selectedEquation.symm.trans actualEquation)
  have generated : data.nativeInstance.equation index = rule := by
    simpa only [NativeRecursorData.equation, identity, Restoration.equation_empty, Option.some.injEq] using equation
  rw [ruleEq, ← generated] at extracted
  have nativeArgs := data.nativeInstance.equation_arguments index extracted
  have fieldLength : program.source.fields.length = data.schema.signature.constructors[index].fields.length := by
    simp only [fieldsEq, List.length_map, fieldTypes, List.length_zipIdx]
  let extra := data.schema.signature.families.size + data.schema.signature.constructors.size
  have argsEq : (program.equationBody.lhs.instL levels).getAppFnArgs.2 =
      (vars data.indexOffset data.schema.signature.constructors[index].fields.length).map (·.instL levels) ++
      program.source.constructorIndices.map (fun e => e.liftN extra data.schema.signature.constructors[index].fields.length) ++
      [(data.nativeInstance.constructorApp data.schema.signature.constructors[index] extra 0).instL levels] := by
    simp only [getAppFnArgs_instL, nativeArgs, List.map_append, List.map_cons, List.map_nil]
    rw [indicesEq]
    simp only [List.map_map, Function.comp_def, instL_liftN, instL_instL, NativeRecursorData.sourceLevels,
      NativeRecursorData.nativeInstance, extra, NativeRecursorData.indexOffset, NativeRecursorData.numParams]
  rw [argsEq]
  have prefixLength : ((vars data.indexOffset data.schema.signature.constructors[index].fields.length).map
      (·.instL levels)).length = data.indexOffset := by simp [vars]
  rw [List.append_assoc, List.getElem?_append_right (by omega)]
  simp only [prefixLength, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simpa only [List.length_map] using slotBound)]
  simp only [List.getElem?_map, chosenIndex, Option.map_some]
  have domainsEq := equation_domains data.nativeInstance index extracted
  have fieldBound : field < data.schema.signature.constructors[index].fields.length := by
    have h := (List.getElem?_eq_some_iff.mp instruction).1
    simp only [fieldInstructions_length, List.length_map, List.length_drop, domainsEq,
      List.length_append, Instance.params, Instance.motives, Instance.minors,
      List.length_map, Array.length_toList, insertBinders, fieldTypes, List.length_zipIdx,
      NativeRecursorData.indexOffset, NativeRecursorData.numParams] at h
    omega
  rw [fieldLength]
  have lt : data.schema.signature.constructors[index].fields.length - 1 - field <
      data.schema.signature.constructors[index].fields.length := by omega
  simp only [VExpr.liftN]
  congr 2
  exact liftVar_lt lt

/-- The same copied field is literally present in the original equation's
binder-order capture tuple. No target substitution or reconstructed argument
is involved in this source occurrence statement. -/
theorem NativeRecursorData.initial_capture_occurrence
    {env : VEnv} {data : NativeRecursorData} {program : SaturatedProgram data}
    {index : Fin data.schema.signature.constructors.size} {rule : VDefEq}
    {levels : List VLevel} {arguments : List VExpr}
    (registered : _root_.Lean4Lean.VEnv.NativeRecursorRegistered env data)
    (families : data.schema.signature.families.size = 1)
    (constructors : data.schema.signature.constructors.size ≤ 1)
    (owner : data.schema.signature.constructors[index].owner = data.owner)
    (equation : data.equation index = some rule)
    (selected : data.saturatedProgram levels arguments = some program)
    {field slot : Nat} {domain : VExpr}
    (instruction : program.instructions[field]? = some (.index domain slot)) :
    (vars program.equationBody.domains.length 0)[data.indexOffset + field]? =
      some (.bvar (program.source.fields.length - 1 - field)) := by
  obtain ⟨_, _, _, _, _, _, _, projection, selectedEquation, extracted, instructions, _, _, _⟩ :=
    saturatedProgram_spec selected
  have lengths := CaseSchema.projectionData_singleton_lengths constructors index projection
  have actualEquation := NativeRecursorData.singletonEquation_of_equation constructors owner equation
  have ruleEq : program.equation = rule := Option.some.inj (selectedEquation.symm.trans actualEquation)
  obtain ⟨body, bodyExtract, domains, _, _⟩ :=
    VEnv.NativeRecursorRegistered.initialEquationBody registered families owner equation
  have bodyEq : body = program.equationBody := by
    rw [ruleEq] at extracted
    exact Option.some.inj (bodyExtract.symm.trans extracted)
  have domainLength : program.equationBody.domains.length = data.indexOffset + program.source.fields.length := by
    rw [← bodyEq, domains, lengths.2.2.1]
  rw [instructions] at instruction
  have fieldBound := (List.getElem?_eq_some_iff.mp instruction).1
  simp only [fieldInstructions_length, List.length_map, List.length_drop, domainLength,
    Nat.add_sub_cancel_left] at fieldBound
  have bound : data.indexOffset + field < (vars program.equationBody.domains.length 0).length := by
    simp only [vars, List.length_map, List.length_reverse, List.length_range, domainLength]
    omega
  rw [List.getElem?_eq_getElem bound]
  simp only [vars, List.getElem_map, List.getElem_reverse, List.getElem_range,
    List.length_range, Nat.zero_add]
  congr 2
  rw [domainLength]
  omega

end Lean4Lean.InductiveSignature
