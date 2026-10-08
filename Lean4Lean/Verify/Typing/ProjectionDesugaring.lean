import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.Inductive.ProjectionProgram
import Lean4Lean.Theory.Typing.CaseMajorDomain

/-! Typed projection abbreviations use fixed, declaration-derived case
programs. Only the occurrence's universe and term arguments vary. -/

namespace Lean4Lean

open InductiveSignature.CaseSchema

inductive ProjectionDesugaring (env : VEnv) (U : Nat) (Γ : List VExpr)
    (structName : Name) (index : Nat) (major : VExpr) : VExpr → Prop
  | intro {schema : InductiveSignature.CaseSchema}
      {owner : Fin schema.signature.families.size}
      {program : ProjectionFunction}
      (registered : env.eliminators block schema)
      (original : schema.originalFamilies[owner.val]? = some structName)
      (family : schema.signature.families[owner].name = structName)
      (generated : schema.genericProjectionPrefix block owner (index + 1) = some programs)
      (selected : programs[index]? = some program)
      (sourceLevels : levels.length = schema.signature.uvars)
      (fieldLevels : fieldSorts.length = index + 1)
      (levelWF : ∀ level ∈ fieldSorts ++ levels, level.WF U)
      (permission : ∀ target ∈ fieldSorts, schema.ProjectionAdmissible owner levels target)
      (parameterCount : params.length = schema.signature.params.length)
      (indexCount : indices.length = schema.signature.families[owner].indices.length)
      (source : env.HasType U Γ major
        (VExpr.mkApps (.const structName levels) (params ++ indices)))
      (target : VExpr.WF env U Γ
        (VExpr.mkApps (program.value.instL (fieldSorts ++ levels))
          (params ++ indices ++ [major]))) :
      ProjectionDesugaring env U Γ structName index major
        (VExpr.mkApps (program.value.instL (fieldSorts ++ levels))
          (params ++ indices ++ [major]))

namespace ProjectionDesugaring

end ProjectionDesugaring
end Lean4Lean
