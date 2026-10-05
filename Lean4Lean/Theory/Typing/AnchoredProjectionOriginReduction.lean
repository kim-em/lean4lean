import Lean4Lean.Theory.Typing.AnchoredDataRelations

/-! Projection congruence uses the literal typing origin of each endpoint.
No common literal type is required between different fields or endpoints. -/
namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false

variable {env : VEnv} {U : Nat} {Γ : List VExpr}
  {info : VProjectionInfo} {name : Name} {index : Nat}
  {major next assignedType domain : VExpr}

def ProjectionOrigin.replaceMajor
    (origin : ProjectionOrigin env U Γ info name index major assignedType domain)
    (equal : env.IsDefEq U Γ major next assignedType) :
    ProjectionOrigin env U Γ info name index next assignedType domain :=
  { origin with majorEq := origin.majorEq.trans (origin.familyPath.cast equal) }

theorem ProjectionOrigin.congr
    (origin : ProjectionOrigin env U Γ info name index major assignedType domain)
    (equal : env.IsDefEq U Γ major next assignedType) :
    env.IsDefEq U Γ (.proj name index major) (.proj name index next) domain := by
  apply origin.fieldPath.cast
  have before : env.IsDefEq U Γ origin.sourceMajor major
      (mkApps (.const name origin.levels) (origin.params ++ origin.indexArgs)) := origin.majorEq
  have after : env.IsDefEq U Γ origin.sourceMajor next
      (mkApps (.const name origin.levels) (origin.params ++ origin.indexArgs)) :=
    origin.majorEq.trans (origin.familyPath.cast equal)
  exact .projDF origin.registered origin.levelsWF origin.levelCount origin.paramCount
    origin.indexCount origin.selected
    origin.formation before after origin.ctorClosed origin.guard

end Lean4Lean.AnchoredSemantics.RankedData
