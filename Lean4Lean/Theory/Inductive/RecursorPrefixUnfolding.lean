import Lean4Lean.Theory.Inductive.RecursorData

/-! A native singleton is reconstructed only after checking its actual
indices. The program may be exposed at any prefix: the unsupplied telescope
is opened with fresh variables, and later closed over the generated body.
For equality, opening an arbitrary endpoint does not make reflexivity a
constructor at that endpoint. The typing rule must check that alignment.
-/

namespace Lean4Lean.InductiveSignature.RecursorData

structure PrefixUnfolding where
  domains : List VExpr
  result : VExpr
  constructor : VExpr
  equation : VDefEq
  equationBody : CaseSchema.EquationBody
  captures : List VExpr
  levels : List VLevel

def PrefixUnfolding.type (program : PrefixUnfolding) : VExpr :=
  VExpr.wrapForalls program.domains program.result

def PrefixUnfolding.rhs (program : PrefixUnfolding) : VExpr :=
  VExpr.wrapLams program.domains (instantiateParams (program.equationBody.rhs.instL program.levels) program.captures)

/-- Supply only the actual occurrence prefix to the dependent native type. -/
def supplyType : List VExpr → VExpr → Option VExpr
  | [], type => some type
  | arg :: args, .forallE _ type => supplyType args (type.inst arg)
  | _ :: _, _ => none

/-- Retain the selected equation and its exact deterministic captures. The
generated body is obtained from that equation directly, rather than by
constructing an ill-typed generic delta function and applying it later. -/
def prefixProgram (data : RecursorData) (U : Nat) (levels : List VLevel)
    (arguments : List VExpr) : Option PrefixUnfolding := do
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

end Lean4Lean.InductiveSignature.RecursorData
