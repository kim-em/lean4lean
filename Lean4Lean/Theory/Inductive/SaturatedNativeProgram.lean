import Lean4Lean.Theory.Inductive.NativeRecursorData

/-! Pure syntax for a saturated native singleton computation. The program
reads index-determined fields from the occurrence and opens a fresh binder
for every remaining field. Typing must separately establish that the latter
domains are inhabited propositions and that the reconstructed indices match.
Neither proof witnesses nor successful typing checks choose this syntax.

The native telescope stops at its major premise. Applications beyond that
point remain a separate spine, including when the native result is a function.
-/

namespace Lean4Lean.InductiveSignature.NativeRecursorData

/-- A field's declared equation domain is retained in both cases. `index`
counts within the actual index spine, rather than the full native spine. -/
inductive CaptureInstruction where
  | index (domain : VExpr) (slot : Nat)
  | proof (domain : VExpr)

def CaptureInstruction.domain : CaptureInstruction → VExpr
  | .index domain _ | .proof domain => domain

def proofCount : List CaptureInstruction → Nat
  | [] => 0
  | .index .. :: rest => proofCount rest
  | .proof .. :: rest => proofCount rest + 1

/-- Captures are in declaration order in the current target context. Added
proof domains are in context order: the newest binder comes first, and each
domain is scoped over the older binders following it. -/
structure SaturatedCaptureState where
  added : List VExpr
  captures : List VExpr

def SaturatedCaptureState.step (state : SaturatedCaptureState)
    (indices : List VExpr) : CaptureInstruction → Option SaturatedCaptureState
  | .index _ slot => do
    let value ← indices[slot]?
    return { state with captures := state.captures ++ [value.liftN state.added.length] }
  | .proof domain =>
    some {
      added := instantiateParams domain state.captures :: state.added
      captures := state.captures.map (·.lift) ++ [.bvar 0] }

def SaturatedCaptureState.run (indices : List VExpr) :
    List CaptureInstruction → SaturatedCaptureState → Option SaturatedCaptureState
  | [], state => some state
  | instruction :: rest, state => do
    let next ← state.step indices instruction
    next.run indices rest

/-- Instructions are fixed before interpreting any major or checking any
guard. The domains supplied here are the universe-instantiated domains of
the generated equation, after its parameter/motive/minor prefixArgs. -/
def fieldInstructions (source : CaseSchema.ProjectionData)
    (domains : List VExpr) : List CaptureInstruction :=
  domains.zipIdx.map fun (domain, field) =>
    match source.fieldIndex field with
    | some slot => .index domain slot
    | none => .proof domain

theorem fieldInstructions_length :
    (fieldInstructions source domains).length = domains.length := by
  simp [fieldInstructions]

theorem SaturatedCaptureState.run_counts
    {state final : SaturatedCaptureState} {indices : List VExpr}
    {instructions : List CaptureInstruction}
    (h : state.run indices instructions = some final) :
    final.captures.length = state.captures.length + instructions.length ∧
    final.added.length = state.added.length + proofCount instructions := by
  induction instructions generalizing state with
  | nil =>
    simp only [run, Option.some.injEq] at h
    subst final
    simp [proofCount]
  | cons instruction rest ih =>
    simp only [run, bind, Option.bind_eq_some_iff] at h
    obtain ⟨next, hstep, hrun⟩ := h
    obtain ⟨hc, ha⟩ := ih hrun
    cases instruction with
    | index domain slot =>
      simp only [step, bind, Option.bind_eq_some_iff] at hstep
      obtain ⟨value, _, hnext⟩ := hstep
      cases hnext
      simpa [proofCount, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using And.intro hc ha
    | proof domain =>
      simp only [step, Option.some.injEq] at hstep
      cases hstep
      simpa [proofCount, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using And.intro hc ha

/-- An undersaturated occurrence has no program. -/
def splitSaturated (count : Nat) (arguments : List VExpr) :
    Option (List VExpr × List VExpr) :=
  if count ≤ arguments.length then
    some (arguments.take count, arguments.drop count)
  else none

theorem splitSaturated_spec
    (h : splitSaturated count arguments = some (prefixArgs, trailing)) :
    prefixArgs.length = count ∧ prefixArgs ++ trailing = arguments ∧
    prefixArgs = arguments.take count ∧ trailing = arguments.drop count := by
  unfold splitSaturated at h
  split at h <;> try contradiction
  rename_i hlength
  cases h
  simp [List.length_take, Nat.min_eq_left hlength]

structure SaturatedProgram (data : NativeRecursorData) where
  levels : List VLevel
  prefixArgs : List VExpr
  trailing : List VExpr
  major : VExpr
  source : CaseSchema.ProjectionData
  equation : VDefEq
  equationBody : CaseSchema.EquationBody
  instructions : List CaptureInstruction
  state : SaturatedCaptureState

/-- Reconstruct the source constructor, whose telescope omits the native
motives and minors. Restoration has already supplied auxiliary parameters. -/
def SaturatedProgram.constructor (program : SaturatedProgram data) : VExpr :=
  instantiateParams program.source.constructor <|
    program.state.captures.take data.numParams ++
      program.state.captures.drop data.indexOffset

def SaturatedProgram.lhs (program : SaturatedProgram data) : VExpr :=
  instantiateParams (program.equationBody.lhs.instL program.levels) program.state.captures

def SaturatedProgram.rhs (program : SaturatedProgram data) : VExpr :=
  instantiateParams (program.equationBody.rhs.instL program.levels) program.state.captures

def SaturatedProgram.type (program : SaturatedProgram data) : VExpr :=
  instantiateParams (program.equationBody.type.instL program.levels) program.state.captures

/-- This expression lives under `state.added`; no fresh data binder is
opened, and the trailing application arguments keep their original order. -/
def SaturatedProgram.result (program : SaturatedProgram data) : VExpr :=
  VExpr.mkApps program.rhs (program.trailing.map (·.liftN program.state.added.length))

/-- Generate only at the first fully saturated native prefixArgs. All structural
arity and parser failures return `none`. A successful result still needs a
typed replay: in particular a non-index field is only a proposed proof slot,
not a claim that its declared domain is a proposition. -/
def saturatedProgram (data : NativeRecursorData) (levels : List VLevel)
    (arguments : List VExpr) : Option (SaturatedProgram data) := do
  if levels.length != data.uvars then none else
  let (prefixArgs, trailing) ← splitSaturated (data.majorOffset + 1) arguments
  let major ← prefixArgs[data.majorOffset]?
  let source ← data.schema.projectionData data.owner (data.sourceLevels levels)
  if source.params.length != data.numParams || source.indices.length != data.numIndices ||
      source.constructorIndices.length != data.numIndices then none else
  let equation ← data.singletonEquation
  let body ← CaseSchema.EquationBody.extract equation.lhs equation.rhs equation.type
  if body.domains.length != data.indexOffset + source.fields.length then none else
  let (head, equationArguments) := body.lhs.getAppFnArgs
  if head != .const data.name (VLevel.params data.uvars) ||
      equationArguments.length != data.majorOffset + 1 then none else
  let instructions := fieldInstructions source <|
    (body.domains.drop data.indexOffset).map (·.instL levels)
  let state ← SaturatedCaptureState.run
    ((prefixArgs.drop data.indexOffset).take data.numIndices) instructions
    { added := [], captures := prefixArgs.take data.indexOffset }
  return ⟨levels, prefixArgs, trailing, major, source, equation, body, instructions, state⟩

/-- Parse the actual constant head as well as its spine. -/
def saturatedOccurrence (data : NativeRecursorData) (expression : VExpr) :
    Option (SaturatedProgram data) :=
  match expression.getAppFnArgs with
  | (.const name levels, arguments) =>
    if name == data.name then data.saturatedProgram levels arguments else none
  | _ => none

theorem saturatedProgram_unique {data : NativeRecursorData}
    {levels : List VLevel} {arguments : List VExpr}
    {program program' : SaturatedProgram data}
    (h : data.saturatedProgram levels arguments = some program)
    (h' : data.saturatedProgram levels arguments = some program') : program = program' :=
  Option.some.inj (h.symm.trans h')

theorem saturatedOccurrence_unique {data : NativeRecursorData}
    {expression : VExpr} {program program' : SaturatedProgram data}
    (h : data.saturatedOccurrence expression = some program)
    (h' : data.saturatedOccurrence expression = some program') : program = program' :=
  Option.some.inj (h.symm.trans h')

/-- Exact occurrence accounting and the generated replay data. Every field
instruction consumes one declared field; only proof instructions add binders. -/
theorem saturatedProgram_spec {data : NativeRecursorData}
    {levels : List VLevel} {arguments : List VExpr} {program : SaturatedProgram data}
    (h : data.saturatedProgram levels arguments = some program) :
    program.levels = levels ∧ levels.length = data.uvars ∧
    program.prefixArgs.length = data.majorOffset + 1 ∧
    program.prefixArgs ++ program.trailing = arguments ∧
    program.prefixArgs = arguments.take (data.majorOffset + 1) ∧
    program.trailing = arguments.drop (data.majorOffset + 1) ∧
    program.prefixArgs[data.majorOffset]? = some program.major ∧
    data.schema.projectionData data.owner (data.sourceLevels levels) = some program.source ∧
    data.singletonEquation = some program.equation ∧
    CaseSchema.EquationBody.extract program.equation.lhs program.equation.rhs
      program.equation.type = some program.equationBody ∧
    program.instructions = fieldInstructions program.source
      ((program.equationBody.domains.drop data.indexOffset).map (·.instL levels)) ∧
    SaturatedCaptureState.run
      ((program.prefixArgs.drop data.indexOffset).take data.numIndices) program.instructions
      { added := [], captures := program.prefixArgs.take data.indexOffset } = some program.state ∧
    program.state.captures.length = program.equationBody.domains.length ∧
    program.state.added.length = proofCount program.instructions := by
  unfold saturatedProgram at h
  dsimp only at h
  split at h <;> try contradiction
  rename_i hlevels
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨prefixArgs, trailing⟩, hsplit, major, hmajor, source, hsource, h⟩ := h
  split at h <;> try contradiction
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨equation, hequation, body, hbody, h⟩ := h
  split at h <;> try contradiction
  rename_i hdomains
  split at h <;> try contradiction
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨state, hrun, h⟩ := h
  cases h
  obtain ⟨hprefix, hargs, htake, hdrop⟩ := splitSaturated_spec hsplit
  obtain ⟨hcaptures, hadded⟩ := SaturatedCaptureState.run_counts hrun
  have hprefixEnough : data.indexOffset ≤ prefixArgs.length := by
    rw [hprefix, majorOffset]
    omega
  have hdomainLength : body.domains.length = data.indexOffset + source.fields.length := by
    simpa using hdomains
  have hcaptureLength : state.captures.length = body.domains.length := by
    simpa [fieldInstructions_length, List.length_take, Nat.min_eq_left hprefixEnough,
      hdomainLength] using hcaptures
  exact ⟨rfl, by simpa using hlevels, hprefix, hargs, htake, hdrop, hmajor,
    hsource, hequation, hbody, rfl, hrun, hcaptureLength, by simpa using hadded⟩

end Lean4Lean.InductiveSignature.NativeRecursorData
