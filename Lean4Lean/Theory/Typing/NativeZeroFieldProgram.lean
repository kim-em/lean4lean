import Lean4Lean.Theory.Typing.NativeInitialSelection
import Lean4Lean.Theory.Typing.CanonicalDataHead

/-! A zero-field native branch reads only its parameter/motive/minor
prefix. Its actual machine output introduces no binder and does not inspect
the major. Dependent result-type alignment remains a separate typed fact. -/
namespace Lean4Lean.InductiveSignature.NativeRecursorData
open VExpr
set_option backward.isDefEq.respectTransparency false

theorem saturatedProgram_noFields
    {data : NativeRecursorData} {levels : List VLevel} {arguments : List VExpr}
    {program : SaturatedProgram data}
    (selected : data.saturatedProgram levels arguments = some program)
    (noFields : program.source.fields = []) :
    program.instructions = [] ∧
      program.state = ⟨[], program.prefixArgs.take data.indexOffset⟩ ∧
      program.equationBody.domains.length = data.indexOffset := by
  unfold saturatedProgram at selected
  dsimp only at selected
  split at selected <;> try contradiction
  simp only [bind, Option.bind_eq_some_iff] at selected
  obtain ⟨⟨prefixArgs, trailing⟩, _, major, _, source, _, selected⟩ := selected
  split at selected <;> try contradiction
  simp only [Option.bind_eq_some_iff] at selected
  obtain ⟨equation, _, body, _, selected⟩ := selected
  split at selected <;> try contradiction
  rename_i domainCount
  split at selected <;> try contradiction
  simp only [Option.bind_eq_some_iff] at selected
  obtain ⟨state, run, same⟩ := selected
  cases same
  change source.fields = [] at noFields
  have domains : body.domains.length = data.indexOffset := by
    apply Classical.not_not.mp
    simpa only [noFields, List.length_nil, Nat.add_zero, ne_eq, Bool.not_eq_true,
      bne_iff_ne] using domainCount
  have dropped : body.domains.drop data.indexOffset = [] := by
    rw [← domains, List.drop_length]
  simp only [dropped, List.map_nil, fieldInstructions, List.zipIdx_nil, List.map_nil,
    SaturatedCaptureState.run, Option.some.injEq] at run
  cases run
  exact ⟨by simp only [dropped, List.map_nil, fieldInstructions, List.zipIdx_nil], rfl, domains⟩

theorem saturatedProgram_noFields_output
    {data : NativeRecursorData} {levels : List VLevel} {arguments : List VExpr}
    {program : SaturatedProgram data}
    (selected : data.saturatedProgram levels arguments = some program)
    (noFields : program.source.fields = []) :
    CanonicalHead.nativeOutput data levels arguments = some ⟨[],
      mkApps (instantiateParams (program.equationBody.rhs.instL levels)
        (arguments.take data.indexOffset)) (arguments.drop (data.majorOffset + 1))⟩ := by
  obtain ⟨_, state, _⟩ := saturatedProgram_noFields selected noFields
  have spec := saturatedProgram_spec selected
  have enough : data.indexOffset ≤ data.majorOffset + 1 := by unfold majorOffset; omega
  simp only [CanonicalHead.nativeOutput, selected, Option.map_some, SaturatedProgram.result,
    SaturatedProgram.rhs, state, spec.1, spec.2.2.2.2.1, spec.2.2.2.2.2.1,
    List.take_take, Nat.min_eq_left enough, List.length_nil, liftN_zero]
  rw [show (fun x : VExpr => x) = id from rfl, List.map_id]

end Lean4Lean.InductiveSignature.NativeRecursorData

namespace Lean4Lean.VEnv
open VExpr InductiveSignature NativeRecursorData

/-- Existence uses the actual registered equation and parser. No field
proof-eligibility premise is needed when the declared field list is empty. -/
theorem NativeRecursorRegistered.zeroFieldProgram
    {env : VEnv} {data : NativeRecursorData} {rule : VDefEq}
    {index : Fin data.schema.signature.constructors.size}
    (registered : NativeRecursorRegistered env data)
    (families : data.schema.signature.families.size = 1)
    (constructors : data.schema.signature.constructors.size ≤ 1)
    (owner : data.schema.signature.constructors[index].owner = data.owner)
    (equation : data.equation index = some rule)
    (noFields : data.schema.signature.constructors[index].fields = [])
    {levels : List VLevel} (levelLength : levels.length = data.uvars)
    {source : CaseSchema.ProjectionData}
    (projection : data.schema.projectionData data.owner (data.sourceLevels levels) = some source)
    (arguments : List VExpr) (argumentLength : arguments.length = data.majorOffset + 1) :
    ∃ program : SaturatedProgram data,
      data.saturatedProgram levels arguments = some program ∧
      program.equation = rule ∧ program.prefixArgs = arguments ∧ program.trailing = [] ∧
      program.instructions = [] ∧ program.state = ⟨[], arguments.take data.indexOffset⟩ ∧
      CanonicalHead.nativeOutput data levels arguments = some ⟨[],
        instantiateParams (program.equationBody.rhs.instL levels) (arguments.take data.indexOffset)⟩ := by
  obtain ⟨program, selected, ruleEq, prefixEq, noTrailing⟩ := InductiveSignature.VEnv.NativeRecursorRegistered.initialProgram registered
    families constructors owner equation levelLength projection arguments argumentLength
  have spec := saturatedProgram_spec selected
  have sourceEq : program.source = source := Option.some.inj
    (spec.2.2.2.2.2.2.2.1.symm.trans projection)
  have fields : program.source.fields = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [sourceEq, (CaseSchema.projectionData_singleton_lengths constructors index projection).2.2.1,
      noFields, List.length_nil]
  obtain ⟨instructions, state, _⟩ := saturatedProgram_noFields selected fields
  refine ⟨program, selected, ruleEq, prefixEq, noTrailing, instructions, ?_, ?_⟩
  · simpa only [prefixEq] using state
  · simpa only [← argumentLength, List.drop_length, mkApps, List.foldl_nil] using
      saturatedProgram_noFields_output selected fields

end Lean4Lean.VEnv

namespace Lean4Lean.CanonicalDataHead
open VExpr InductiveSignature NativeRecursorData

theorem etaIota_noFields
    {registry : Registry} {chosen : Selected} {rule : Rule}
    (single : chosen.rules = [rule])
    {entry : VProjectionEntry}
    (reverse : registry.structureConstructors rule.constructor = some entry)
    {info : VProjectionInfo} (projection : registry.projections entry.typeName = some info)
    (constructor : info.ctorName = rule.constructor) (unindexed : info.nindices = 0)
    (noFields : info.numFields = 0)
    (arity : rule.constructorArity = info.nparams)
    (fields : rule.fieldCount = 0)
    (levelCount : chosen.levels.length = rule.equation.uvars)
    (prefixBound : rule.prefixCount ≤ chosen.arguments.length) (major : VExpr) :
    etaIota registry chosen major = some
      (mkApps (rule.equation.rhs.instL chosen.levels) (chosen.arguments.take rule.prefixCount)) := by
  simp only [etaIota, single, reverse, projection, bind, Option.bind_some, constructor,
    unindexed, noFields, Nat.add_zero, arity, fields, levelCount, prefixBound,
    and_self, ↓reduceIte, List.range_zero, List.map_nil, List.append_nil]

theorem step_native_noFields
    {registry : Registry} {data : NativeRecursorData}
    (lookup : registry.natives data.name = some data)
    (notDefinition : registry.definitions data.name = none)
    {levels : List VLevel} {arguments : List VExpr} {program : SaturatedProgram data}
    (selected : data.saturatedProgram levels arguments = some program)
    (noFields : program.source.fields = []) :
    step registry (mkApps (.const data.name levels) arguments) = some ⟨[],
      mkApps (instantiateParams (program.equationBody.rhs.instL levels)
        (arguments.take data.indexOffset)) (arguments.drop (data.majorOffset + 1))⟩ := by
  have old : CanonicalHead.step registry (mkApps (.const data.name levels) arguments) =
      some ⟨[], mkApps (instantiateParams (program.equationBody.rhs.instL levels)
        (arguments.take data.indexOffset)) (arguments.drop (data.majorOffset + 1))⟩ := by
    simp only [CanonicalHead.step, getAppFnArgs_mkApps_const, CanonicalHead.spineStep,
      notDefinition, lookup, ↓reduceIte, saturatedProgram_noFields_output selected noFields]
  rw [step.eq_def, old]

end Lean4Lean.CanonicalDataHead
