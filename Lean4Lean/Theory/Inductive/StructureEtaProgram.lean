import Lean4Lean.Theory.Inductive.ProjectionProgram

/-! Declaration-generated structure eta templates. Eta is a separate equality
principle; generating these terms does not derive eta from case iota. -/

namespace Lean4Lean.InductiveSignature.CaseSchema

/-- Reconstruct the original constructor from all its generated field
projections in the common-parameter/major context. -/
def ProjectionData.etaReconstruction (data : ProjectionData)
    (projections : List ProjectionFunction) : VExpr :=
  instantiateParams data.constructor <|
    vars data.params.length 1 ++ projections.map fun projection =>
      VExpr.mkApps projection.value (vars data.params.length 1 ++ [.bvar 0])

/-- A complete, closed template for the structure eta equality. Indexed
families are rejected, matching the separate structure eta principle. Every
field is supplied by this schema's actual projection generator. -/
def structureEta (schema : CaseSchema) (block : Name)
    (owner : Fin schema.signature.families.size) (uvars : Nat)
    (levels fieldSorts : List VLevel) : Option VDefEq := do
  let data ← schema.projectionData owner levels
  if data.indices.length != 0 || data.fields.length != fieldSorts.length then none else
  let projections ← schema.projectionPrefix block owner uvars levels fieldSorts
  let domains := data.params ++ [data.major]
  return {
    uvars := uvars
    lhs := VExpr.wrapLams domains (data.etaReconstruction projections)
    rhs := VExpr.wrapLams domains (.bvar 0)
    type := VExpr.wrapForalls domains data.major.lift }

end Lean4Lean.InductiveSignature.CaseSchema
