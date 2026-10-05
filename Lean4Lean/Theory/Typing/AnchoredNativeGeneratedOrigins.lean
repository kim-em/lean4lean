import Lean4Lean.Theory.Typing.AnchoredNativeInitialTerminal
import Lean4Lean.Theory.Typing.NativeDeclaredFieldOrigin
import Lean4Lean.Theory.Typing.NativePrefixArity

/-! Generate the complete finite capture-origin chain from actual parser
instructions. The only remaining proof-field input is its original Prop
classification in the source header; copied-field origins are all derived. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature NativeRecursorData
open private Instance.equation_arguments from Lean4Lean.Theory.Typing.NativeInitialFieldOccurrences
open private vars_take from Lean4Lean.Theory.Typing.NativeDeclaredFieldOrigin
set_option backward.isDefEq.respectTransparency false

/-- The literal registered telescope is a parser conclusion at every
universe specialization, not an additional successful-parse assumption. -/
theorem NativeConstantSignature.ofRegisteredType
    {data : NativeRecursorData} {type : VExpr}
    (registeredType : data.recursorType = some type) (levels : List VLevel) :
    Nonempty (NativeConstantSignature data levels) := by
  obtain ⟨domains, body, shape, length⟩ := recursorType_telescope registeredType
  have parsed := NativeRecursorData.takeForalls_wrapForalls (domains.map (·.instL levels)) (body.instL levels)
  simp only [List.length_map, length] at parsed
  refine ⟨⟨type, registeredType, domains.map (·.instL levels), body.instL levels, ?_⟩⟩
  simpa only [shape, instL_wrapForalls] using parsed

private theorem vars_take_prefix (count extra : Nat) :
    (vars (count + extra) 0).take count = vars count extra := by
  apply List.ext_getElem
  · simp [vars]
  · intro i hi hi'
    simp only [List.getElem_take, vars, List.getElem_map, List.getElem_reverse,
      List.getElem_range, List.length_range, Nat.zero_add]
    congr 2
    have bound : i < count := by simpa only [vars, List.length_map,
      List.length_reverse, List.length_range] using hi'
    omega

theorem NativeRecursorData.originalPrefix
    {env : VEnv} {data : NativeRecursorData} {program : SaturatedProgram data}
    {index : Fin data.schema.signature.constructors.size} {rule : VDefEq}
    (registered : NativeRecursorRegistered env data)
    (families : data.schema.signature.families.size = 1)
    (constructors : data.schema.signature.constructors.size ≤ 1)
    (owner : data.schema.signature.constructors[index].owner = data.owner)
    (equation : data.equation index = some rule)
    (selected : data.saturatedProgram program.levels (program.prefixArgs ++ program.trailing) = some program) :
    (vars program.equationBody.domains.length 0).take data.indexOffset =
      (program.equationBody.lhs.instL program.levels).getAppFnArgs.2.take data.indexOffset := by
  have spec := saturatedProgram_spec selected
  have identity := VEnv.NativeRecursorRegistered.singleton_restoration registered families
  have ruleEq : program.equation = rule := Option.some.inj
    (spec.2.2.2.2.2.2.2.2.1.symm.trans (singletonEquation_of_equation constructors owner equation))
  have generated : data.nativeInstance.equation index = rule := by
    simpa only [NativeRecursorData.equation, identity, Restoration.equation_empty,
      Option.some.injEq] using equation
  have extracted := spec.2.2.2.2.2.2.2.2.2.1
  rw [ruleEq, ← generated] at extracted
  have arguments := Instance.equation_arguments data.nativeInstance index extracted
  obtain ⟨body, bodySelected, bodyLength, _, _⟩ :=
    VEnv.NativeRecursorRegistered.initialEquationBody registered families owner equation
  have bodyEq : body = program.equationBody := by
    have h := spec.2.2.2.2.2.2.2.2.2.1
    rw [ruleEq] at h
    exact Option.some.inj (bodySelected.symm.trans h)
  rw [bodyEq] at bodyLength
  rw [bodyLength, vars_take_prefix]
  simp only [getAppFnArgs_instL, arguments, List.map_append]
  have length : (vars (data.schema.signature.params.length + data.schema.signature.families.size +
      data.schema.signature.constructors.size) data.schema.signature.constructors[index].fields.length).length =
      data.indexOffset := by simp [vars, indexOffset, numParams]
  rw [List.append_assoc, List.take_append_of_le_length
    (by simpa only [List.length_map] using Nat.le_of_eq length.symm)]
  rw [← List.map_take, ← length, List.take_length]
  simp [vars, indexOffset, numParams, List.map_map, Function.comp_def, VExpr.instL]

theorem NativeIndexTemplates.ofInstruction
    {data : NativeRecursorData} {program : SaturatedProgram data}
    {signature : NativeConstantSignature data program.levels}
    (selected : data.saturatedProgram program.levels (program.prefixArgs ++ program.trailing) = some program)
    {field slot : Nat} {domain : VExpr}
    (instruction : program.instructions[field]? = some (.index domain slot))
    (indexCount : program.source.constructorIndices.length = data.numIndices) :
    ∃ templates : NativeIndexTemplates program,
      templates.field = field ∧ templates.slot = slot ∧ templates.declaredDomain = domain := by
  have instructions := (saturatedProgram_spec selected).2.2.2.2.2.2.2.2.2.2.1
  have origin := instruction
  rw [instructions] at origin
  have slotBound := CaseSchema.ProjectionData.fieldIndex_bound
    (fieldInstructions_index_origin origin).2
  rw [indexCount] at slotBound
  have length := takeForalls_length signature.telescope
  have bound : data.indexOffset + slot < signature.domains.length := by
    rw [length, majorOffset]
    omega
  exact ⟨{
    selected := selected
    recursorType := signature.type
    registeredType := signature.typeOrigin
    inputDomains := signature.domains
    result := signature.result
    telescope := signature.telescope
    field := field
    slot := slot
    naturalDomain := signature.domains[data.indexOffset + slot]
    declaredDomain := domain
    naturalOrigin := List.getElem?_eq_getElem bound
    declaredOrigin := instruction }, rfl, rfl, rfl⟩

private theorem originalProofField
    {sourceEnv : VEnv} {U : Nat} {domains : List VExpr} {domain result : VExpr} {position : Nat}
    (hsource : sourceEnv.Ordered)
    (scope : (wrapForalls domains result).Closed)
    (selected : domains[position]? = some domain)
    (proof : sourceEnv.IsDefEqStrong U (domains.take position).reverse domain domain (.sort .zero)) :
    let proposition := domain.instOuter ((vars domains.length 0).take position)
    sourceEnv.IsDefEqStrong U domains.reverse proposition proposition (.sort .zero) ∧
    sourceEnv.IsDefEqStrong U domains.reverse (.bvar (domains.length - 1 - position))
      (.bvar (domains.length - 1 - position)) proposition := by
  obtain ⟨domainScope, lookup⟩ := InductiveSignature.declaredFieldOrigin scope selected
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  have extension : Ctx.LiftN (domains.length - position) 0
      (domains.take position).reverse domains.reverse := by
    have lift := Ctx.LiftN.zero (n := domains.length - position) (Γ := (domains.take position).reverse)
      (domains.drop position).reverse (by simp)
    simpa only [← List.reverse_append, List.take_append_drop] using lift
  have lifted := proof.weakN hsource extension
  have proposition : sourceEnv.IsDefEqStrong U domains.reverse
      (domain.instOuter ((vars domains.length 0).take position))
      (domain.instOuter ((vars domains.length 0).take position)) (.sort .zero) := by
    rw [vars_take _ _ (Nat.le_of_lt bound), instOuter_range_bvar' domain position domains.length
      domainScope (Nat.le_of_lt bound)]
    simpa only [VExpr.liftN] using lifted
  exact ⟨proposition, .bvar lookup (show VLevel.zero.WF U from trivial) proposition⟩

/-- Derive the entire origin chain, rather than assuming a preconstructed
chain. `proofs` is the remaining declaration-specific Prop classification in
the actual source header. It contains raw proofs, not semantic callbacks. -/
theorem NativeCaptureOrigins.generated
    {sourceEnv env : VEnv} {U : Nat} {data : NativeRecursorData} {program : SaturatedProgram data}
    (henv : env.Ordered) (hsource : sourceEnv.Ordered)
    {signature : NativeConstantSignature data program.levels}
    {index : Fin data.schema.signature.constructors.size} {rule : VDefEq}
    (registered : NativeRecursorRegistered env data)
    (families : data.schema.signature.families.size = 1)
    (constructors : data.schema.signature.constructors.size ≤ 1)
    (owner : data.schema.signature.constructors[index].owner = data.owner)
    (equation : data.equation index = some rule)
    (selected : data.saturatedProgram program.levels (program.prefixArgs ++ program.trailing) = some program)
    (proofs : ∀ field domain, program.instructions[field]? = some (.proof domain) →
      sourceEnv.IsDefEqStrong U
        (((program.equationBody.domains.take (data.indexOffset + field)).map
          (·.instL program.levels)).reverse) domain domain (.sort .zero)) :
    Nonempty (NativeCaptureOrigins sourceEnv U
      (program.equationBody.domains.map (·.instL program.levels)).reverse program
      (program.equationBody.lhs.instL program.levels).getAppFnArgs.2
      (vars program.equationBody.domains.length 0) program.instructions.length) := by
  have spec := saturatedProgram_spec selected
  have raw := henv.defEqWF (registered.singletonEquation spec.2.2.2.2.2.2.2.2.1)
  obtain ⟨typeLevel, typeWF⟩ := IsDefEq.isType henv (Γ := []) trivial raw.1
  have typeClosed : program.equation.type.Closed := VExpr.WF.closedN henv ⟨_, typeWF⟩ trivial
  have scope : (wrapForalls (program.equationBody.domains.map (·.instL program.levels))
      (program.equationBody.type.instL program.levels)).Closed := by
    rw [← instL_wrapForalls, (CaseSchema.EquationBody.extract_sound spec.2.2.2.2.2.2.2.2.2.1).2.2]
    exact typeClosed.instL
  have rhsClosed : program.equation.rhs.Closed := VExpr.WF.closedN henv ⟨_, raw.2⟩ trivial
  have captureLength := initialCaptureLength selected
  have indexCount := (CaseSchema.projectionData_singleton_lengths constructors index
    spec.2.2.2.2.2.2.2.1).2.2.2.1
  have samePrefix := NativeRecursorData.originalPrefix registered families constructors owner equation selected
  have arity : (program.equationBody.lhs.instL program.levels).getAppFnArgs.2.length = data.majorOffset + 1 := by
    simpa only [nativeEquationArguments, List.length_map] using
      (nativeEquationArguments_length (witnesses := []) selected)
  suffices ∀ count, count ≤ program.instructions.length →
      Nonempty (NativeCaptureOrigins sourceEnv U
        (program.equationBody.domains.map (·.instL program.levels)).reverse program
        (program.equationBody.lhs.instL program.levels).getAppFnArgs.2
        (vars program.equationBody.domains.length 0) count) from
    this program.instructions.length (Nat.le_refl _)
  intro count
  induction count with
  | zero =>
    intro _
    exact ⟨.prefix samePrefix (by rw [arity, majorOffset]; omega)⟩
  | succ field ih =>
    intro bound
    have fieldBound : field < program.instructions.length := by omega
    obtain ⟨previous⟩ := ih (by omega)
    have instruction := List.getElem?_eq_getElem fieldBound
    cases actual : program.instructions[field] with
    | index domain slot =>
      rw [actual] at instruction
      obtain ⟨templates, fieldEq, slotEq, domainEq⟩ := NativeIndexTemplates.ofInstruction
        (signature := signature) selected instruction indexCount
      have nativeOccurrence := NativeRecursorData.initial_index_occurrence registered families
        constructors owner equation selected templates.declaredOrigin
      have captureOccurrence := NativeRecursorData.initial_capture_occurrence registered families
        constructors owner equation selected templates.declaredOrigin
      obtain ⟨domainScope, lookup⟩ := templates.declaredSourceLookup scope captureOccurrence
      have prior : NativeCaptureOrigins sourceEnv U
          (program.equationBody.domains.map (·.instL program.levels)).reverse program
          (program.equationBody.lhs.instL program.levels).getAppFnArgs.2
          (vars program.equationBody.domains.length 0) templates.field := fieldEq ▸ previous
      simpa only [fieldEq] using
        (show Nonempty (NativeCaptureOrigins sourceEnv U
          (program.equationBody.domains.map (·.instL program.levels)).reverse program
          (program.equationBody.lhs.instL program.levels).getAppFnArgs.2
          (vars program.equationBody.domains.length 0) (templates.field + 1)) from
          ⟨.index nativeOccurrence captureOccurrence lookup rfl domainScope prior⟩)
    | proof domain =>
      rw [actual] at instruction
      have instructions := spec.2.2.2.2.2.2.2.2.2.2.1
      have domains := fieldInstructions_domains program.source
        ((program.equationBody.domains.drop data.indexOffset).map (·.instL program.levels))
      rw [← instructions] at domains
      have exactDomain := congrArg (fun ds => ds[field]?) domains
      rw [List.getElem?_map, instruction] at exactDomain
      have domainOrigin : (program.equationBody.domains.map (·.instL program.levels))[data.indexOffset + field]? = some domain := by
        simpa only [Option.map_some, CaptureInstruction.domain, List.map_drop,
          List.getElem?_drop] using exactDomain.symm
      have original := proofs field domain instruction
      obtain ⟨proposition, argument⟩ := originalProofField hsource scope domainOrigin
        (by simpa only [List.map_take] using original)
      simp only [List.length_map] at proposition argument
      have positionBound : data.indexOffset + field < program.equationBody.domains.length := by omega
      have captureBound : data.indexOffset + field < (vars program.equationBody.domains.length 0).length := by
        simpa [vars] using positionBound
      have occurrence : (vars program.equationBody.domains.length 0)[data.indexOffset + field]? =
          some (.bvar (program.equationBody.domains.length - 1 - (data.indexOffset + field))) := by
        rw [List.getElem?_eq_getElem captureBound]
        simp only [vars, List.getElem_map, List.getElem_reverse, List.length_range,
          List.getElem_range, Nat.zero_add]
      have domainScope : domain.ClosedN
          ((vars program.equationBody.domains.length 0).take (data.indexOffset + field)).length := by
        simpa only [List.length_take, vars, List.length_map, List.length_reverse, List.length_range,
          Nat.min_eq_left (Nat.le_of_lt positionBound), CaptureInstruction.domain] using
          native_instruction_scope selected rhsClosed instruction
      exact ⟨.proof instruction occurrence proposition argument original rfl domainScope previous⟩

end Lean4Lean.AnchoredSource.Adapted
