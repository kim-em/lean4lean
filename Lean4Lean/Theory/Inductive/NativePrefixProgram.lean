import Lean4Lean.Theory.Inductive.NativeRecursorData

/-! A native singleton is reconstructed only after checking its actual
indices. The program may be exposed at any prefix: the unsupplied telescope
is opened with fresh variables, and later closed over the generated body.
For equality, opening an arbitrary endpoint does not make reflexivity a
constructor at that endpoint. The typing rule must check that alignment.
-/

namespace Lean4Lean.InductiveSignature.NativeRecursorData

structure PrefixProgram where
  domains : List VExpr
  result : VExpr
  constructor : VExpr
  equation : VDefEq
  equationBody : CaseSchema.EquationBody
  captures : List VExpr
  levels : List VLevel

def PrefixProgram.type (program : PrefixProgram) : VExpr :=
  VExpr.wrapForalls program.domains program.result

def PrefixProgram.rhs (program : PrefixProgram) : VExpr :=
  VExpr.wrapLams program.domains (instantiateParams (program.equationBody.rhs.instL program.levels) program.captures)

/-- The last remaining binder is the major premise. Its domain has to be
lifted across that binder before checking a reconstructed constructor. -/
def PrefixProgram.majorType (program : PrefixProgram) : Option VExpr :=
  program.domains.getLast?.map VExpr.lift

/-- Supply only the actual occurrence prefix to the dependent native type. -/
def supplyType : List VExpr → VExpr → Option VExpr
  | [], type => some type
  | arg :: args, .forallE _ type => supplyType args (type.inst arg)
  | _ :: _, _ => none

/-- Retain the selected equation and its exact deterministic captures. The
generated body is obtained from that equation directly, rather than by
constructing an ill-typed generic delta function and applying it later. -/
def prefixProgram (data : NativeRecursorData) (U : Nat) (levels : List VLevel)
    (arguments : List VExpr) : Option PrefixProgram := do
  if levels.length != data.uvars || arguments.length > data.majorOffset then none else
  let type ← data.recursorType
  let type ← supplyType arguments (type.instL levels)
  let remaining := data.majorOffset + 1 - arguments.length
  let (domains, result) ← takeForalls remaining type
  let allArguments := arguments.map (·.liftN remaining) ++ vars remaining 0
  let constructor ← data.reconstructCanonical U levels allArguments
  let source ← data.schema.projectionData data.owner (data.sourceLevels levels)
  let fields ← source.reconstructionPrefix data.block data.owner.val (data.sourceLevels levels)
    source.fields (List.replicate source.fields.length .zero) []
  let projectionArguments := allArguments.take data.numParams ++
    (allArguments.drop data.indexOffset).take data.numIndices ++ [.bvar 0]
  let captures := allArguments.take data.indexOffset ++
    fields.map (fun field => VExpr.mkApps field.value projectionArguments)
  let equation ← data.singletonEquation
  let equationBody ← CaseSchema.EquationBody.extract equation.lhs equation.rhs equation.type
  if captures.length != equationBody.domains.length then none else
  return ⟨domains, result, constructor, equation, equationBody, captures, levels⟩

theorem prefixProgram_unique {data : NativeRecursorData} {levels : List VLevel}
    (h : data.prefixProgram U levels arguments = some p)
    (h' : data.prefixProgram U levels arguments = some p') : p = p' :=
  Option.some.inj (h.symm.trans h')

/-- Successful generation supplies the finite replay's structural checks;
they need not be postulated separately by its producer. -/
theorem prefixProgram_spec {data : NativeRecursorData} {levels : List VLevel}
    (h : data.prefixProgram U levels arguments = some program) :
    arguments.length ≤ data.majorOffset ∧ program.domains ≠ [] ∧
    program.levels = levels ∧ program.levels.length = program.equation.uvars ∧
    data.singletonEquation = some program.equation ∧
    CaseSchema.EquationBody.extract program.equation.lhs program.equation.rhs
      program.equation.type = some program.equationBody ∧
    program.captures.length = program.equationBody.domains.length := by
  unfold prefixProgram at h
  dsimp only at h
  split at h <;> try contradiction
  rename_i hguard
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨type, _, remainingType, _, ⟨domains, result⟩, hdomains,
    constructor, _, source, _, fields, _, equation, hequation, body, hbody, h⟩ := h
  split at h <;> try contradiction
  rename_i hcaptures
  cases h
  simp at hguard
  have hargs : arguments.length ≤ data.majorOffset := by simpa using hguard.2
  have hlevels : levels.length = data.uvars := by simpa using hguard.1
  have hlen := takeForalls_length hdomains
  refine ⟨hargs, ?_, rfl, hlevels.trans (singletonEquation_uvars hequation).symm,
    hequation, hbody, ?_⟩
  · intro hnil
    change domains = [] at hnil
    simp only [hnil, List.length_nil] at hlen
    omega
  · simpa using hcaptures

end Lean4Lean.InductiveSignature.NativeRecursorData
