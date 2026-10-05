import Lean4Lean.Theory.Typing.NativeResultBridge
import Lean4Lean.Theory.Inductive.SingletonCompilation
import Lean4Lean.Theory.Typing.NativeProjectionCompleteness

/-! Initial saturated selection is generated from the actual singleton
constructor equation. The machine cannot fail after extraction: every index
instruction names a position in the actual constructor-index list. -/
namespace Lean4Lean.InductiveSignature
open VExpr VEnv NativeRecursorData
open private registeredInstance from Lean4Lean.Theory.Typing.NativeRuleRegistration
open private extract_wrap_const from Lean4Lean.Theory.Typing.NativeResultBridge
open private rebuild_spine from Lean4Lean.Theory.Inductive.CaseReductionData
open AnchoredSource.Adapted
set_option backward.isDefEq.respectTransparency false

 theorem CaseSchema.ProjectionData.fieldIndex_bound
    {source : CaseSchema.ProjectionData} {field slot : Nat}
    (selected : source.fieldIndex field = some slot) : slot < source.constructorIndices.length := by
  simp only [CaseSchema.ProjectionData.fieldIndex, Option.map_eq_some_iff] at selected
  obtain ⟨⟨expression, position⟩, found, rfl⟩ := selected
  have member := List.mem_of_find?_eq_some found
  have indexed := List.mk_mem_zipIdx_iff_getElem?.mp member
  exact (List.getElem?_eq_some_iff.mp indexed).1

 theorem SaturatedCaptureState.run_exists
    {instructions : List CaptureInstruction} {indices : List VExpr}
    (valid : ∀ domain slot, CaptureInstruction.index domain slot ∈ instructions → slot < indices.length)
    (state : SaturatedCaptureState) : ∃ result, state.run indices instructions = some result := by
  induction instructions generalizing state with
  | nil => exact ⟨state, rfl⟩
  | cons instruction rest ih =>
    obtain ⟨next, step⟩ : ∃ next, state.step indices instruction = some next := by
      cases instruction with
      | proof domain => exact ⟨_, rfl⟩
      | index domain slot =>
        have bound := valid domain slot List.mem_cons_self
        exact ⟨{ state with captures := state.captures ++ [indices[slot].liftN state.added.length] },
          by simp [SaturatedCaptureState.step, List.getElem?_eq_getElem bound]⟩
    obtain ⟨result, run⟩ := ih (fun domain slot member => valid domain slot (List.mem_cons_of_mem _ member)) next
    exact ⟨result, by simp only [SaturatedCaptureState.run, step, bind, Option.bind_some, run]⟩

 theorem fieldInstructions_valid
    (source : CaseSchema.ProjectionData) (domains indices : List VExpr)
    (length : source.constructorIndices.length = indices.length) :
    ∀ domain slot, CaptureInstruction.index domain slot ∈ fieldInstructions source domains → slot < indices.length := by
  intro domain slot member
  obtain ⟨⟨actual, field⟩, _, selected⟩ := List.mem_map.mp member
  dsimp only at selected
  cases selector : source.fieldIndex field with
  | none => simp [selector] at selected
  | some position =>
    simp only [selector, CaptureInstruction.index.injEq] at selected
    cases selected.2
    rw [← length]
    exact CaseSchema.ProjectionData.fieldIndex_bound selector

private theorem singleton_ctor
    {s : InductiveSignature} (single : s.constructors.size ≤ 1)
    (index : Fin s.constructors.size) {ctor : Constructor s.families.size}
    (member : ctor ∈ s.constructors.toList) : ctor = s.constructors[index] := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp member
  have same : i = index.val := by have := index.isLt; simp only [Array.length_toList] at hi; omega
  simp only [Array.getElem_toList, same, Fin.getElem_fin]

/-- Length facts originate in the actual projection extraction, including its
checked constructor-index arity. No guessed native offsets are accepted. -/
 theorem CaseSchema.projectionData_singleton_lengths
    {schema : CaseSchema} {owner : Fin schema.signature.families.size}
    {levels : List VLevel} {source : CaseSchema.ProjectionData}
    (single : schema.signature.constructors.size ≤ 1)
    (index : Fin schema.signature.constructors.size)
    (selected : schema.projectionData owner levels = some source) :
    source.params.length = schema.signature.params.length ∧
    source.indices.length = schema.signature.families[owner].indices.length ∧
    source.fields.length = schema.signature.constructors[index].fields.length ∧
    source.constructorIndices.length = schema.signature.families[owner].indices.length ∧
    schema.signature.constructors[index].indices.length = schema.signature.families[owner].indices.length := by
  unfold CaseSchema.projectionData at selected
  split at selected <;> try contradiction
  split at selected <;> try contradiction
  rename_i ctor filterEq
  dsimp only at selected
  split at selected <;> try contradiction
  rename_i arity
  have member : ctor ∈ schema.signature.constructors.toList := by
    have filtered : ctor ∈ schema.signature.constructors.toList.filter (fun c => c.owner == owner) := by
      rw [filterEq]
      exact List.mem_cons_self
    exact (List.mem_filter.mp filtered).1
  have ctorEq := singleton_ctor single index member
  simp only [bind, Option.bind_eq_some_iff] at selected
  obtain ⟨params, hp, indices, hi, fields, hf, constructorIndices, hc, major, hm, constructor, hctor, selected⟩ := selected
  split at selected <;> try contradiction
  cases selected
  have paramsLength := Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hp)
  have indicesLength := Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hi)
  have fieldsLength := Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hf)
  have constructorLength := Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hc)
  have arityEq : ctor.indices.length = schema.signature.families[owner].indices.length := by simpa using arity
  refine ⟨paramsLength.symm, indicesLength.symm, ?_, constructorLength.symm.trans arityEq, ?_⟩
  · simpa only [fieldTypes, List.length_map, List.length_zipIdx, ctorEq] using fieldsLength.symm
  · simpa only [ctorEq] using arityEq

 theorem VEnv.NativeRecursorRegistered.singleton_restoration
    (registered : NativeRecursorRegistered env data)
    (single : data.schema.signature.families.size = 1) : data.schema.restoration = {} := by
  obtain ⟨base, installBase, source, expanded, auxiliaries, block, installed, compilation, _, restoration, _, _⟩ :=
    registeredInstance registered
  exact restoration.trans (compilation.restoration_of_singleton single)

private theorem singleton_list {values : List α} (small : values.length ≤ 1)
    (member : value ∈ values) : values = [value] := by
  cases values with
  | nil => cases member
  | cons head tail =>
    have empty : tail = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at small; omega)
    subst tail
    cases List.mem_singleton.mp member
    rfl

/-- The singleton selector chooses the actual original constructor equation. -/
theorem NativeRecursorData.singletonEquation_of_equation
    {data : NativeRecursorData} {index : Fin data.schema.signature.constructors.size}
    (single : data.schema.signature.constructors.size ≤ 1)
    (owner : data.schema.signature.constructors[index].owner = data.owner)
    (equation : data.equation index = some rule) : data.singletonEquation = some rule := by
  have filterEq : (List.finRange data.schema.signature.constructors.size).filter
      (fun i => data.schema.signature.constructors[i].owner == data.owner) = [index] := by
    apply singleton_list
    · exact Nat.le_trans (List.length_filter_le _ _) (by simpa using single)
    · exact List.mem_filter.mpr ⟨List.mem_finRange _, by simpa only [owner, beq_self_eq_true]⟩
  simpa only [NativeRecursorData.singletonEquation, NativeRecursorData.equation, filterEq] using equation

private theorem Instance.equation_extract_native
    {s : InductiveSignature} (g : Instance s) (index : Fin s.constructors.size) :
    ∃ body : CaseSchema.EquationBody,
      CaseSchema.EquationBody.extract (g.equation index).lhs (g.equation index).rhs
        (g.equation index).type = some body ∧
      body.domains.length = s.params.length + s.families.size + s.constructors.size +
        s.constructors[index].fields.length ∧
      body.lhs.getAppFnArgs.1 = .const (g.recursorName s.constructors[index].owner) (VLevel.params g.uvars) ∧
      body.lhs.getAppFnArgs.2.length = s.params.length + s.families.size + s.constructors.size +
        s.constructors[index].indices.length + 1 := by
  let ctor := s.constructors[index]
  let extra := s.families.size + s.constructors.size
  let domains := g.params ++ g.motives ++ g.minors ++
    insertBinders ((s.fieldTypes ctor).map (·.instL g.levels)) extra
  let indices := ctor.indices.map fun e => (e.instL g.levels).liftN extra ctor.fields.length
  let major := g.constructorApp ctor extra 0
  let lhs := mkApps (g.recursorHead .native ctor.owner)
    (vars (s.params.length + extra) ctor.fields.length ++ indices ++ [major])
  let rhs := mkApps (.bvar (ctor.fields.length + s.constructors.size - 1 - index.val))
    (vars ctor.fields.length 0 ++ (Instance.recursiveFields ctor).map fun (field, r) => g.recursiveCall ctor field r)
  let type := mkApps (.bvar (ctor.fields.length + s.constructors.size + (s.families.size - 1 - ctor.owner.val)))
    (indices ++ [major])
  have head : lhs.getAppFnArgs.1 = .const (g.recursorName ctor.owner) (VLevel.params g.uvars) := by
    exact getAppFnArgs_mkApps_head _ _
  refine ⟨⟨domains, lhs, rhs, type⟩, ?_, ?_, head, ?_⟩
  · exact extract_wrap_const head domains
  · simp [domains, Instance.params, Instance.motives, Instance.minors, insertBinders, fieldTypes, ctor, extra, Nat.add_assoc]
  · simp [lhs, Instance.recursorHead, getAppFnArgs_mkApps_const, vars, indices, ctor, extra, Nat.add_assoc]

/-- At singleton compilation the restored original equation has an actual
extractable native body, with exact telescope and application arities. -/
theorem VEnv.NativeRecursorRegistered.initialEquationBody
    {data : NativeRecursorData} {index : Fin data.schema.signature.constructors.size}
    (registered : NativeRecursorRegistered env data)
    (families : data.schema.signature.families.size = 1)
    (owner : data.schema.signature.constructors[index].owner = data.owner)
    (equation : data.equation index = some rule) :
    ∃ body : CaseSchema.EquationBody,
      CaseSchema.EquationBody.extract rule.lhs rule.rhs rule.type = some body ∧
      body.domains.length = data.indexOffset + data.schema.signature.constructors[index].fields.length ∧
      body.lhs.getAppFnArgs.1 = .const data.name (VLevel.params data.uvars) ∧
      body.lhs.getAppFnArgs.2.length = data.indexOffset + data.schema.signature.constructors[index].indices.length + 1 := by
  have identity := VEnv.NativeRecursorRegistered.singleton_restoration registered families
  have ruleEq : data.nativeInstance.equation index = rule := by
    simpa only [NativeRecursorData.equation, identity, Restoration.equation_empty, Option.some.injEq] using equation
  rw [← ruleEq]
  obtain ⟨body, extracted, domains, head, arity⟩ := data.nativeInstance.equation_extract_native index
  refine ⟨body, extracted, domains, ?_, arity⟩
  rw [owner] at head
  simpa [NativeRecursorData.nativeInstance, NativeRecursorData.name, identity,
    Restoration.recursorName] using head

/-- All program-selection guards are discharged from the actual restored
singleton equation and actual projection extraction. Index capture execution
is total here; no successful machine run is assumed. -/
theorem VEnv.NativeRecursorRegistered.initialProgram
    {env : VEnv} {data : NativeRecursorData} {rule : VDefEq}
    {index : Fin data.schema.signature.constructors.size}
    (registered : NativeRecursorRegistered env data)
    (families : data.schema.signature.families.size = 1)
    (constructors : data.schema.signature.constructors.size ≤ 1)
    (owner : data.schema.signature.constructors[index].owner = data.owner)
    (equation : data.equation index = some rule)
    {levels : List VLevel} (levelLength : levels.length = data.uvars)
    {source : CaseSchema.ProjectionData}
    (projection : data.schema.projectionData data.owner (data.sourceLevels levels) = some source)
    (arguments : List VExpr) (argumentLength : arguments.length = data.majorOffset + 1) :
    ∃ program : SaturatedProgram data,
      data.saturatedProgram levels arguments = some program ∧
      program.equation = rule ∧ program.prefixArgs = arguments ∧ program.trailing = [] := by
  obtain ⟨body, extracted, domainLength, head, arity⟩ :=
    VEnv.NativeRecursorRegistered.initialEquationBody registered families owner equation
  have sourceLengths := CaseSchema.projectionData_singleton_lengths constructors index projection
  have equationSelected := NativeRecursorData.singletonEquation_of_equation constructors owner equation
  have bodyLength : body.domains.length = data.indexOffset + source.fields.length := by
    rw [domainLength, sourceLengths.2.2.1]
  have argumentArity : body.lhs.getAppFnArgs.2.length = data.majorOffset + 1 := by
    rw [arity, sourceLengths.2.2.2.2]
    rfl
  have indicesLength : ((arguments.drop data.indexOffset).take data.numIndices).length = data.numIndices := by
    simp only [List.length_take, List.length_drop, argumentLength, NativeRecursorData.majorOffset]
    omega
  let instructions := fieldInstructions source ((body.domains.drop data.indexOffset).map (·.instL levels))
  obtain ⟨state, run⟩ := SaturatedCaptureState.run_exists
    (fieldInstructions_valid source ((body.domains.drop data.indexOffset).map (·.instL levels)) ((arguments.drop data.indexOffset).take data.numIndices)
      (by rw [indicesLength]; exact sourceLengths.2.2.2.1))
    { added := [], captures := arguments.take data.indexOffset }
  have majorBound : data.majorOffset < arguments.length := by omega
  let program : SaturatedProgram data :=
    ⟨levels, arguments, [], arguments[data.majorOffset], source, rule, body, instructions, state⟩
  refine ⟨program, ?_, rfl, rfl, rfl⟩
  have enough : data.majorOffset + 1 ≤ arguments.length := by omega
  have fullTake : arguments.take (data.majorOffset + 1) = arguments := by rw [← argumentLength, List.take_length]
  have fullDrop : arguments.drop (data.majorOffset + 1) = [] := by rw [← argumentLength, List.drop_length]
  change data.saturatedProgram levels arguments = some program
  simp only [NativeRecursorData.saturatedProgram, levelLength, bne_self_eq_false,
    Bool.false_eq_true, if_false, splitSaturated, enough, if_pos, fullTake, fullDrop,
    bind, Option.bind_some, List.getElem?_eq_getElem majorBound, projection]
  have params : source.params.length = data.numParams := sourceLengths.1
  have indices : source.indices.length = data.numIndices := sourceLengths.2.1
  have ctorIndices : source.constructorIndices.length = data.numIndices := sourceLengths.2.2.2.1
  simp only [params, indices, ctorIndices, bne_self_eq_false, Bool.or_false, Bool.false_eq_true,
    if_false, equationSelected, Option.bind_some, extracted, bodyLength, head, argumentArity]
  simp only [run, Option.bind_some]
  rfl

/-- The initial native occurrence is the actual instantiated original equation
left side. Its complete argument tuple, including computed and repeated indices,
is derived literally rather than supplied as an alignment guard. -/
theorem VEnv.NativeRecursorRegistered.initialOccurrence
    {env : VEnv} {data : NativeRecursorData} {rule : VDefEq}
    {index : Fin data.schema.signature.constructors.size}
    (registered : NativeRecursorRegistered env data)
    (families : data.schema.signature.families.size = 1)
    (constructors : data.schema.signature.constructors.size ≤ 1)
    (owner : data.schema.signature.constructors[index].owner = data.owner)
    (equation : data.equation index = some rule)
    {levels : List VLevel} (levelLength : levels.length = data.uvars)
    {source : CaseSchema.ProjectionData}
    (projection : data.schema.projectionData data.owner (data.sourceLevels levels) = some source)
    (witnesses : List VExpr) :
    ∃ program : SaturatedProgram data,
      data.saturatedOccurrence ((program.equationBody.lhs.instL levels).subst
        (nativeCaptureSubst witnesses)) = some program ∧
      program.equation = rule ∧ program.levels = levels ∧
      program.prefixArgs = nativeEquationArguments program witnesses ∧
      program.trailing = [] := by
  obtain ⟨body, extracted, _, head, arity⟩ :=
    VEnv.NativeRecursorRegistered.initialEquationBody registered families owner equation
  have sourceLengths := CaseSchema.projectionData_singleton_lengths constructors index projection
  let arguments := ((body.lhs.instL levels).getAppFnArgs.2).map
    (·.subst (nativeCaptureSubst witnesses))
  have argumentLength : arguments.length = data.majorOffset + 1 := by
    simp only [arguments, List.length_map, getAppFnArgs_instL]
    rw [arity, sourceLengths.2.2.2.2]
    rfl
  obtain ⟨program, selected, ruleEq, argsEq, trailing⟩ :=
    VEnv.NativeRecursorRegistered.initialProgram registered families constructors owner equation
      levelLength projection arguments argumentLength
  have spec := saturatedProgram_spec selected
  have bodyEq : program.equationBody = body := by
    have h := spec.2.2.2.2.2.2.2.2.2.1
    rw [ruleEq, extracted] at h
    exact (Option.some.inj h).symm
  have instantiatedHead : (body.lhs.instL levels).getAppFnArgs.1 = .const data.name levels := by
    simp only [getAppFnArgs_instL, head, VExpr.instL]
    rw [VLevel.inst_map_id levelLength]
  have expression : (body.lhs.instL levels).subst (nativeCaptureSubst witnesses) =
      mkApps (.const data.name levels) arguments := by
    have h := congrArg (fun e => e.subst (nativeCaptureSubst witnesses))
      (rebuild_spine (body.lhs.instL levels))
    simpa only [subst_mkApps, instantiatedHead, subst_const] using h.symm
  refine ⟨program, ?_, ruleEq, spec.1, ?_, trailing⟩
  · rw [bodyEq, expression]
    simpa only [NativeRecursorData.saturatedOccurrence, getAppFnArgs_mkApps_const,
      beq_self_eq_true, if_true] using selected
  · simp only [nativeEquationArguments, bodyEq, spec.1]
    exact argsEq

/-- Initial parsing from the actual finite compilation and its original
well-formed declaration. Projection extraction and machine success are both
conclusions; no native selection or index-arity oracle is required. -/
theorem VEnv.NativeRecursorRegistered.initialOccurrence_compilation
    {env base : VEnv} {data : NativeRecursorData} {rule : VDefEq}
    {source expanded : VInductDecl} {auxiliaries : List ContainerSpecialization}
    {block : VInductBlock} {index : Fin data.schema.signature.constructors.size}
    (registered : NativeRecursorRegistered env data)
    (compilation : CompilationData base source expanded data.schema.signature
      data.nativeInstance auxiliaries block)
    (ordered : base.Ordered)
    (families : data.schema.signature.families.size = 1)
    (constructors : data.schema.signature.constructors.size ≤ 1)
    (owner : data.schema.signature.constructors[index].owner = data.owner)
    (equation : data.equation index = some rule)
    {levels : List VLevel} (levelLength : levels.length = data.uvars)
    (witnesses : List VExpr) :
    ∃ program : SaturatedProgram data,
      data.saturatedOccurrence ((program.equationBody.lhs.instL levels).subst
        (nativeCaptureSubst witnesses)) = some program ∧
      program.equation = rule ∧ program.levels = levels ∧
      program.prefixArgs = nativeEquationArguments program witnesses ∧
      program.trailing = [] := by
  have identity := VEnv.NativeRecursorRegistered.singleton_restoration registered families
  obtain ⟨types, _, admissible⟩ := compilation.admissible
  have length : (data.sourceLevels levels).length = data.schema.signature.uvars := by
    simpa only [NativeRecursorData.sourceLevels, List.length_map,
      NativeRecursorData.nativeInstance] using admissible.levels_length
  obtain ⟨projection, selected⟩ := compilation.model.projectionData_exists ordered
    compilation.expandedWF identity constructors index owner length
  exact VEnv.NativeRecursorRegistered.initialOccurrence registered families constructors
    owner equation levelLength selected witnesses

end Lean4Lean.InductiveSignature
