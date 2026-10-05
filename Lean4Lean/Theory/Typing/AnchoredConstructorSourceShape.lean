import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSyntax

/-! Literal declaration shape distinguishes family-producing plans from
constructor-producing plans before any semantic interpretation. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles InductiveSignature

private def returnsSort : VExpr → Bool
  | .forallE _ body => returnsSort body
  | .sort _ => true
  | _ => false

private theorem returnsSort_instL (expression : VExpr) (levels : List VLevel) :
    returnsSort (expression.instL levels) = returnsSort expression := by
  induction expression <;> simp_all only [VExpr.instL, returnsSort]

private theorem returnsSort_wrap (domains : List VExpr) (result : VExpr) :
    returnsSort (wrapForalls domains result) = returnsSort result := by
  induction domains with
  | nil => rfl
  | cons domain domains ih => exact ih

private theorem returnsSort_family (name : Name) (levels : List VLevel) (arguments : List VExpr) :
    returnsSort (mkApps (.const name levels) arguments) = false := by
  have general : ∀ fn, returnsSort fn = false → returnsSort (mkApps fn arguments) = false := by
    induction arguments with
    | nil => exact fun _ h => h
    | cons argument arguments ih => exact fun fn _ => ih (.app fn argument) rfl
  exact general _ rfl

private theorem FamilyPlan.returnsSort
    {declaredType : VExpr} {signature : ConstantTelescope declaredType}
    (plan : FamilyPlan env U registry target name levels signature arguments demand footprint) :
    returnsSort declaredType = true := by
  match plan with
  | .terminal _ resultSort _ _ => rw [signature.type_eq, returnsSort_wrap, resultSort]; rfl
  | .binder _ _ _ body _ _ => exact body.returnsSort
  | .view source _ => exact source.returnsSort
  | .pad source => exact source.returnsSort
termination_by sizeOf plan

theorem FamilyPlan.not_constructorHeader
    {declaredType : VExpr} {signature : ConstantTelescope (declaredType.instL seedLevels)}
    {domains arguments : List VExpr} {family : Name} {familyLevels : List VLevel}
    (shape : declaredType = wrapForalls domains (mkApps (.const family familyLevels) arguments))
    (plan : FamilyPlan env U registry target name levels signature supplied demand footprint) : False := by
  have value := plan.returnsSort
  rw [returnsSort_instL, shape, returnsSort_wrap, returnsSort_family] at value
  cases value

private theorem ConstructorPlan.returnsSort
    {declaredType : VExpr} {signature : ConstantTelescope declaredType}
    (plan : ConstructorPlan env U registry target name levels signature arguments demand footprint) :
    returnsSort declaredType = false := by
  match plan with
  | .terminal _ resultShape _ _ _ =>
    rw [signature.type_eq, returnsSort_wrap, resultShape, returnsSort_family]
  | .binder _ _ _ body _ _ => exact body.returnsSort
  | .view source _ => exact source.returnsSort
  | .pad source => exact source.returnsSort
termination_by sizeOf plan

theorem ConstructorPlan.not_familyHeader
    {declaredType : VExpr} {signature : ConstantTelescope (declaredType.instL seedLevels)}
    {domains : List VExpr} {level : VLevel}
    (shape : declaredType = wrapForalls domains (.sort level))
    (plan : ConstructorPlan env U registry target name levels signature supplied demand footprint) : False := by
  have value := plan.returnsSort
  rw [returnsSort_instL, shape, returnsSort_wrap] at value
  cases value

end Lean4Lean.AnchoredSource.Adapted
