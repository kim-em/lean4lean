import Lean4Lean.Theory.Typing.AnchoredDataRelations

/-! Projection provenance follows actual context maps and assigned-type
conversions while retaining its registered field computation. -/
namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv

private theorem head_lift (name : Name) (levels : List VLevel) (arguments : List VExpr) (ρ : Lift) :
    (mkApps (.const name levels) arguments).lift' ρ =
      mkApps (.const name levels) (arguments.map (·.lift' ρ)) := by
  suffices ∀ head, (mkApps head arguments).lift' ρ =
      mkApps (head.lift' ρ) (arguments.map (·.lift' ρ)) from this _
  induction arguments with
  | nil => intro head; rfl
  | cons arg rest ih => intro head; exact ih (.app head arg)

def ProjectionOrigin.transport (henv : env.Ordered)
    (origin : ProjectionOrigin env U Γ info name index major assignedType domain)
    (route : MixedInsertion env U Γ Δ ρ) :
    ProjectionOrigin env U Δ info name index (major.lift' ρ)
      (assignedType.lift' ρ) (domain.lift' ρ) :=
  { origin with
    params := origin.params.map (·.lift' ρ)
    paramCount := by simpa only [List.length_map] using origin.paramCount
    indexArgs := origin.indexArgs.map (·.lift' ρ)
    indexCount := by simpa only [List.length_map] using origin.indexCount
    sourceMajor := origin.sourceMajor.lift' ρ
    fieldType := origin.fieldType.lift' ρ
    selected := by
      simpa only [← lift'_subst, subst_id] using
        info.fieldType_subst_some (substitution := Subst.id.lift_r ρ) origin.ctorClosed origin.selected
    formation := by simpa only [HasType, lift'] using route.eq henv origin.formation
    familyPath := by simpa only [head_lift, List.map_append] using route.path henv origin.familyPath
    majorEq := by simpa only [head_lift, List.map_append] using route.eq henv origin.majorEq
    fieldPath := route.path henv origin.fieldPath }

def ProjectionOrigin.convertAssignedType
    (origin : ProjectionOrigin env U Γ info name index major assignedType domain)
    (path : TypeConversion env U Γ assignedType assignedType') :
    ProjectionOrigin env U Γ info name index major assignedType' domain :=
  { origin with familyPath := path.symm.trans origin.familyPath }

def ProjectionOrigin.changeLevels (henv : env.Ordered) (formed : OnCtx Γ (env.IsType U))
    (origin : ProjectionOrigin env U Γ info name index major assignedType domain)
    (equal : EqUpToLevels U major major') :
    ProjectionOrigin env U Γ info name index major' assignedType domain :=
  { origin with
    majorEq := origin.majorEq.trans (origin.majorEq.hasType.2.eqUpToLevels henv formed equal) }

end Lean4Lean.AnchoredSemantics.RankedData
