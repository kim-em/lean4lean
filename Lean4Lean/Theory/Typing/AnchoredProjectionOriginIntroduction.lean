import Lean4Lean.Theory.Typing.AnchoredDataProjection
import Lean4Lean.Theory.Typing.AnchoredProjectionOriginTransport
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.AnchoredSourceFuture

/-! Projection provenance is produced from the actual original projDF
children, including its index arguments. Paired substitutions retain the
left assigned family and field type by explicit typed conversion paths. -/
namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false

def ProjectionOrigin.ofRule
    {env : VEnv} {U : Nat} {source : List VExpr}
    {info : VProjectionInfo} {name : Name} {index : Nat}
    {levels : List VLevel} {params indexArgs : List VExpr}
    {sourceMajor major fieldType : VExpr} {fieldLevel : VLevel}
    (registered : env.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (paramCount : params.length = info.nparams)
    (indexCount : indexArgs.length = info.nindices)
    (selected : info.fieldType name levels params index sourceMajor = some fieldType)
    (formation : env.HasType U source fieldType (.sort fieldLevel))
    (majorEq : env.IsDefEq U source sourceMajor major
      (mkApps (.const name levels) (params ++ indexArgs)))
    (ctorClosed : info.ctorType.Closed)
    (guard : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero) :
    ProjectionOrigin env U source info name index major
      (mkApps (.const name levels) (params ++ indexArgs)) fieldType where
  registered := registered
  levels := levels
  levelsWF := levelsWF
  levelCount := levelCount
  params := params
  paramCount := paramCount
  indexArgs := indexArgs
  indexCount := indexCount
  sourceMajor := sourceMajor
  fieldType := fieldType
  fieldLevel := fieldLevel
  selected := selected
  formation := formation
  familyPath := .refl
  majorEq := majorEq
  ctorClosed := ctorClosed
  guard := guard
  fieldPath := .refl

/-- The two original major children may realize different family parameters
and indices. Their source family's formation supplies the bridge; no type
uniqueness or reflection from the target world is used. -/
theorem ProjectionOrigin.pairedStrong
    {env : VEnv} {U : Nat} {source target : List VExpr} {σ τ : Subst}
    (henv : env.Ordered)
    (targetFormed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    {info : VProjectionInfo} {name : Name} {index : Nat}
    {levels : List VLevel} {params indexArgs : List VExpr}
    {sourceMajor left right fieldType : VExpr} {fieldLevel : VLevel}
    (registered : env.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (paramCount : params.length = info.nparams)
    (indexCount : indexArgs.length = info.nindices)
    (selected : info.fieldType name levels params index sourceMajor = some fieldType)
    (formation : env.IsDefEqStrong U source fieldType fieldType (.sort fieldLevel))
    (leftMajor : env.IsDefEqStrong U source sourceMajor left
      (mkApps (.const name levels) (params ++ indexArgs)))
    (rightMajor : env.IsDefEqStrong U source sourceMajor right
      (mkApps (.const name levels) (params ++ indexArgs)))
    (ctorClosed : info.ctorType.Closed)
    (guard : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero) :
    Nonempty (ProjectionOrigin env U target info name index (left.subst σ)
      ((mkApps (.const name levels) (params ++ indexArgs)).subst σ) (fieldType.subst σ)) ∧
    Nonempty (ProjectionOrigin env U target info name index (right.subst τ)
      ((mkApps (.const name levels) (params ++ indexArgs)).subst σ) (fieldType.subst σ)) := by
  let before := ProjectionOrigin.ofRule registered levelsWF levelCount paramCount indexCount selected
    formation.defeq leftMajor.defeq ctorClosed guard
  let after := ProjectionOrigin.ofRule registered levelsWF levelCount paramCount indexCount selected
    formation.defeq rightMajor.defeq ctorClosed guard
  have first := before.substitute henv targetFormed substitutions.left
  have second := after.substitute henv targetFormed (substitutions.right henv targetFormed)
  obtain ⟨familyLevel, familyFormation⟩ := leftMajor.defeq.isType henv substitutions.wf
  have familyEq := familyFormation.substDF henv substitutions.wf targetFormed substitutions
  have fieldEq := formation.defeq.substDF henv substitutions.wf targetFormed substitutions
  have aligned := second.convertAssignedType (.single familyEq.symm)
  exact ⟨⟨first⟩, ⟨{ aligned with fieldPath := aligned.fieldPath.trans (.single fieldEq.symm) }⟩⟩

end Lean4Lean.AnchoredSemantics.RankedData
