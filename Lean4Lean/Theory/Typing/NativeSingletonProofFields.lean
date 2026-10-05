import Lean4Lean.Theory.Inductive.SingletonCompilation
import Lean4Lean.Theory.Inductive.CompilationLemmas
import Lean4Lean.Theory.Inductive.NativeCommonPrefix
import Lean4Lean.Theory.Inductive.RestorationNaturality
import Lean4Lean.Theory.Typing.EnvLemmas

/-! Recover proof-field formation from the declaration's actual singleton
elimination evidence. A failed index selector alone says nothing about the
field's sort. This module retains the environment in which singleton
elimination was originally checked; transporting changed header types to
the installed environment is a separate obligation. -/

namespace Lean4Lean.InductiveSignature
open VExpr VEnv CaseSchema NativeRecursorData
set_option backward.isDefEq.respectTransparency false

theorem CaseSchema.ProjectionData.fieldIndex_none
    {data : ProjectionData} {field : Nat} (none : data.fieldIndex field = none) :
    VExpr.bvar (data.fields.length - 1 - field) ∉ data.constructorIndices := by
  intro member
  obtain ⟨i, hi, eq⟩ := List.getElem_of_mem member
  have zipped := List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi)
  have selected := none
  simp only [ProjectionData.fieldIndex, Option.map_eq_none_iff, List.find?_eq_none] at selected
  have h := selected _ zipped
  simp only [eq, beq_self_eq_true] at h
  contradiction

private theorem insertBinders_append (fields : List VExpr) (domain : VExpr) (count : Nat) :
    insertBinders (fields ++ [domain]) count =
      insertBinders fields count ++ [domain.liftN count fields.length] := by
  simp [insertBinders, List.zipIdx_append]

private theorem insertBinders_take (fields : List VExpr) (count depth : Nat) :
    (insertBinders fields count).take depth = insertBinders (fields.take depth) count := by
  apply List.ext_getElem
  · simp [insertBinders]
  · intro i hi hj
    simp [insertBinders]

private theorem insertBinders_context (fields extra base : List VExpr) :
    Ctx.LiftN extra.length fields.length (fields.reverse ++ base)
      ((insertBinders fields extra.length).reverse ++ extra.reverse ++ base) := by
  suffices ∀ reversed : List VExpr, Ctx.LiftN extra.length reversed.length (reversed ++ base)
      ((insertBinders reversed.reverse extra.length).reverse ++ extra.reverse ++ base) by
    simpa only [List.length_reverse, List.reverse_reverse] using this fields.reverse
  intro reversed
  induction reversed with
  | nil => exact .zero extra.reverse List.length_reverse
  | cons domain reversed ih =>
    simpa only [List.length_cons, List.length_reverse, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      insertBinders_append, List.append_assoc] using ih.succ (A := domain)

private theorem insertBinders_instL (fields : List VExpr) (count : Nat) (levels : List VLevel) :
    (insertBinders fields count).map (·.instL levels) =
      insertBinders (fields.map (·.instL levels)) count := by
  apply List.ext_getElem
  · simp [insertBinders]
  · intro i hi hj
    simp [insertBinders, VExpr.instL_liftN]

private theorem fieldTypes_get (s : InductiveSignature) (ctor : Constructor s.families.size)
    (i : Nat) (hi : i < ctor.fields.length) :
    (s.fieldTypes ctor)[i]'(by simpa [fieldTypes] using hi) = s.fieldType i ctor.fields[i] := by
  simp [fieldTypes]

/-- Inserting the actual motive/minor telescope preserves the source proof
formation. This is weakening into the declaration context, with no inversion
of a converted constructor type. -/
theorem SingletonElimination.fieldProof_under_prefix
    {s : InductiveSignature} {env : VEnv} {U : Nat} {levels : List VLevel}
    (henv : env.Ordered) (singleton : s.SingletonElimination env U levels)
    {ctor : Constructor s.families.size} (member : ctor ∈ s.constructors.toList)
    (field : Nat) (bound : field < ctor.fields.length)
    (notIndex : VExpr.bvar (ctor.fields.length - 1 - field) ∉ ctor.indices)
    (extra : List VExpr) :
    env.HasType U
      ((insertBinders (((s.fieldTypes ctor).take field).map (·.instL levels)) extra.length).reverse ++
        extra.reverse ++ (s.params.map (·.instL levels)).reverse)
      (((s.fieldType field ctor.fields[field]).instL levels).liftN extra.length field) (.sort .zero) := by
  have proof := (singleton.2.2 ctor member field bound).resolve_right notIndex
  have weakened := proof.weakN henv
    (insertBinders_context (((s.fieldTypes ctor).take field).map (·.instL levels))
      extra (s.params.map (·.instL levels)).reverse)
  have length : (((s.fieldTypes ctor).take field).map (·.instL levels)).length = field := by
    simp only [List.length_map, List.length_take, fieldTypes, List.length_zipIdx]
    omega
  simpa only [length, VExpr.liftN] using weakened

/-- With identity restoration, the actual projection extractor retains the
original constructor fields and result indices after source specialization. -/
theorem CaseSchema.projectionData_empty_origin
    {schema : CaseSchema} {owner : Fin schema.signature.families.size}
    {levels : List VLevel} {data : ProjectionData}
    (identity : schema.restoration = {})
    (selected : schema.projectionData owner levels = some data) :
    ∃ ctor ∈ schema.signature.constructors.toList,
      data.fields = (schema.signature.fieldTypes ctor).map (·.instL levels) ∧
      data.constructorIndices = ctor.indices.map (·.instL levels) := by
  unfold projectionData at selected
  split at selected <;> try contradiction
  split at selected <;> try contradiction
  rename_i ctor constructors
  dsimp only at selected
  split at selected <;> try contradiction
  have mapRestore (expressions : List VExpr) :
      expressions.mapM (fun e => schema.restoration.expr (e.instL levels)) =
        some (expressions.map (·.instL levels)) := by
    rw [identity]
    induction expressions with
    | nil => rfl
    | cons expression expressions ih => rw [List.mapM_cons, ih]; simp
  simp only [mapRestore, bind, Option.bind_some] at selected
  simp only [Option.bind_eq_some_iff] at selected
  obtain ⟨major, _, constructor, _, selected⟩ := selected
  split at selected <;> try contradiction
  cases selected
  refine ⟨ctor, ?_, rfl, rfl⟩
  have mem : ctor ∈ schema.signature.constructors.toList.filter (fun c => c.owner == owner) := by
    rw [constructors]
    exact .head _
  exact (List.mem_filter.mp mem).1

private theorem singleton_members_eq {xs : List α} (length : xs.length ≤ 1)
    (left : a ∈ xs) (right : b ∈ xs) : a = b := by
  cases xs with
  | nil => cases left
  | cons x xs =>
    have tail : xs = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at length; omega)
    subst xs
    exact (List.mem_singleton.mp left).trans (List.mem_singleton.mp right).symm

private theorem extract_wrap_const {lhs rhs type : VExpr}
    {name : Name} {levels : List VLevel}
    (hhead : lhs.getAppFnArgs.1 = .const name levels) (domains : List VExpr) :
    EquationBody.extract (wrapLams domains lhs) (wrapLams domains rhs)
      (wrapForalls domains type) = some ⟨domains, lhs, rhs, type⟩ := by
  induction domains with
  | nil => cases lhs <;> first | rfl | cases hhead
  | cons domain domains ih =>
    change (do
      if domain ≠ domain ∨ domain ≠ domain then none else
      let body ← EquationBody.extract (wrapLams domains lhs) (wrapLams domains rhs)
        (wrapForalls domains type)
      pure { body with domains := domain :: body.domains }) = _
    simp [ih]

private theorem equation_domains {s : InductiveSignature} (g : Instance s)
    (index : Fin s.constructors.size)
    (selected : EquationBody.extract (g.equation index).lhs (g.equation index).rhs
      (g.equation index).type = some body) :
    body.domains = g.params ++ g.motives ++ g.minors ++
      insertBinders ((s.fieldTypes s.constructors[index]).map (·.instL g.levels))
        (s.families.size + s.constructors.size) := by
  unfold Instance.equation at selected
  dsimp only at selected
  rw [extract_wrap_const (by exact VExpr.getAppFnArgs_mkApps_head _ _)] at selected
  cases selected
  rfl

private theorem fieldInstructions_proof
    {source : ProjectionData} {domains : List VExpr} {field : Nat} {domain : VExpr}
    (selected : (fieldInstructions source domains)[field]? = some (.proof domain)) :
    domains[field]? = some domain ∧ source.fieldIndex field = none := by
  obtain ⟨bound, selected⟩ := List.getElem?_eq_some_iff.mp selected
  have bound' : field < domains.length := by simpa only [fieldInstructions_length] using bound
  simp only [fieldInstructions, List.getElem_map, List.getElem_zipIdx, Nat.zero_add] at selected
  cases choice : source.fieldIndex field with
  | some slot => simp only [choice] at selected; contradiction
  | none =>
    simp only [choice, CaptureInstruction.proof.injEq] at selected
    exact ⟨by rw [List.getElem?_eq_getElem bound']; exact congrArg some selected, rfl⟩

/-- The complete selected program's proof instruction is justified by the
source singleton certificate, in that certificate's original environment.
The equation prefix is computed from the same native instance. -/
theorem NativeRecursorData.saturatedProgram_proofField
    {data : NativeRecursorData} {program : SaturatedProgram data}
    {env : VEnv} {U : Nat} {levels : List VLevel} {arguments : List VExpr}
    (henv : env.Ordered) (identity : data.schema.restoration = {})
    (singleton : data.schema.signature.SingletonElimination env U (data.sourceLevels levels))
    (selected : data.saturatedProgram levels arguments = some program)
    {field : Nat} {domain : VExpr}
    (instruction : program.instructions[field]? = some (.proof domain)) :
    env.HasType U
      (((program.equationBody.domains.take (data.indexOffset + field)).map
        (·.instL levels)).reverse) domain (.sort .zero) := by
  obtain ⟨_, _, _, _, _, _, _, projection, equation, body, instructions, _, _, _⟩ :=
    saturatedProgram_spec selected
  rw [instructions] at instruction
  obtain ⟨domainSelected, noIndex⟩ := fieldInstructions_proof instruction
  obtain ⟨ctor, ctorMember, fieldsEq, indicesEq⟩ :=
    data.schema.projectionData_empty_origin identity projection
  unfold singletonEquation at equation
  dsimp only at equation
  split at equation <;> try contradiction
  rename_i index indices
  simp only [identity, Restoration.equation_empty, Option.some.injEq] at equation
  rw [← equation] at body
  have domainsEq := equation_domains data.nativeInstance index body
  have sameCtor : ctor = data.schema.signature.constructors[index] :=
    singleton_members_eq (by simpa using singleton.2.1) ctorMember (Array.getElem_mem_toList ..)
  subst ctor
  let extra := data.nativeInstance.motives ++ data.nativeInstance.minors
  have extraLength : extra.length = data.schema.signature.families.size +
      data.schema.signature.constructors.size := by simp [extra, Instance.motives, Instance.minors]
  have prefixLength : (data.nativeInstance.params ++ extra).length = data.indexOffset := by
    simp only [List.length_append, extraLength, Instance.params, List.length_map,
      indexOffset, numParams, Nat.add_assoc]
  have domainsEq' : program.equationBody.domains = data.nativeInstance.params ++ extra ++
      insertBinders ((data.schema.signature.fieldTypes data.schema.signature.constructors[index]).map
        (·.instL data.levels)) extra.length := by
    rw [extraLength]
    simpa only [extra, List.append_assoc, nativeInstance] using domainsEq
  rw [domainsEq'] at domainSelected ⊢
  change (((data.nativeInstance.params ++ extra ++
      insertBinders ((data.schema.signature.fieldTypes data.schema.signature.constructors[index]).map
        (·.instL data.levels)) extra.length).drop data.indexOffset).map (·.instL levels))[field]? =
      some domain at domainSelected
  rw [← prefixLength, List.drop_left] at domainSelected
  obtain ⟨fieldBound, fieldEq⟩ := List.getElem?_eq_some_iff.mp domainSelected
  have originalBound : field < data.schema.signature.constructors[index].fields.length := by
    simpa only [List.length_map, insertBinders, fieldTypes, List.length_zipIdx] using fieldBound
  have notIndex : .bvar (data.schema.signature.constructors[index].fields.length - 1 - field) ∉
      data.schema.signature.constructors[index].indices := by
    intro member
    apply ProjectionData.fieldIndex_none noIndex
    rw [fieldsEq, indicesEq]
    simpa only [List.length_map, fieldTypes, List.length_zipIdx, VExpr.instL] using
      List.mem_map_of_mem (f := VExpr.instL (data.sourceLevels levels)) member
  have formation := singleton.fieldProof_under_prefix henv
    (Array.getElem_mem_toList ..) field originalBound notIndex (extra.map (·.instL levels))
  simp only [List.length_map] at formation
  have domainEq : domain =
      (((data.schema.signature.fieldType field data.schema.signature.constructors[index].fields[field]).instL
        (data.sourceLevels levels)).liftN extra.length field) := by
    rw [← fieldEq]
    simp only [List.getElem_map, insertBinders, List.getElem_zipIdx, Nat.zero_add,
      VExpr.instL_liftN, VExpr.instL_instL, sourceLevels]
    rw [fieldTypes_get _ _ _ originalBound]
  rw [domainEq]
  change env.HasType U (((data.nativeInstance.params ++ extra ++
    insertBinders ((data.schema.signature.fieldTypes data.schema.signature.constructors[index]).map
      (·.instL data.levels)) extra.length).take
    (data.indexOffset + field)).map (·.instL levels)).reverse _ _
  rw [← prefixLength, List.take_append]
  rw [List.take_of_length_le (Nat.le_add_right (data.nativeInstance.params ++ extra).length field)]
  simp only [Nat.add_sub_cancel_left, List.map_append,
    List.reverse_append, insertBinders_take, List.map_take, insertBinders_instL,
    List.map_map, Function.comp_def, VExpr.instL_instL]
  simpa only [Instance.params, List.map_map, Function.comp_def, VExpr.instL_instL,
    sourceLevels, List.append_assoc, ← List.map_take, nativeInstance, Fin.getElem_fin] using formation

end Lean4Lean.InductiveSignature
