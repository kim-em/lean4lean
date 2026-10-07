import Lean4Lean.Theory.Typing.ShapeModel.RuleValidSig

/-!
# Validity of generic eliminator equations
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean InductiveSignature

set_option linter.unusedSectionVars false

noncomputable section

variable {env : VEnv}

theorem generic_elimOK {E base : VEnv} {T : Tables} {source : VInductDecl}
    {block : VInductBlock} {schema : CaseSchema} {key : Name}
    (H : env.WF) (hgood : Good env E) (hEW : E.WF) (hle : E.addEliminator key schema ≤ env)
    (hbase : base.WF) (hbl : base ≤ E) (hcert : schema.Certified base source block)
    (hkey : source.types.head?.map (·.name) = some key)
    (hconsts : (∀ value ∈ block.types ++ block.ctors,
      E.constants value.name = some value.toVConstant) ∧ E.defeqs = base.defeqs ∧
      schema.ProjNamesRegistered E key)
    (hfresh : schema.Fresh E key) (hcompat : schema.StructCompat E) (hT : T.Inv E)
    (hext : (T.addSchema E source).Extends (envTables env))
    (hfam : ∀ I d, (T.addSchema E source).fam I = some d →
      letI := envSig env; FamSem env I d.resultLevel (d.nparams + d.nindices))
    (hfrz : ∀ c, SchemaCtorReserved (E.addEliminator key schema) c →
      (T.addSchema E source).fam c = none → (envTables env).fam c = none) :
    letI := envSig env; ElimOK env key schema := sorry


end

end Lean4Lean.ShapeModel
