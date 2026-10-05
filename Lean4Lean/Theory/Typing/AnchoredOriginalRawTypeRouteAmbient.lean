import Lean4Lean.Theory.Typing.AnchoredOriginalRawTypeRoute

/-! The finite environment provenance of a raw route. Frame generation is
not a substitute for this invariant: an empty frame can be built over an
arbitrary source environment. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

/-- Only missing inclusion evidence is recorded. Equality and application
constructors already retain their actual source inclusions. -/
def RawGeneratedTypeRoute.Ambient
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final) : Prop :=
  match route with
  | .identity display _ => display.sourceEnv ≤ env
  | .same left right .. | .assigned left right .. => left.sourceEnv ≤ env ∧ right.sourceEnv ≤ env
  | .equality .. => True
  | .typedEquality (left := left) .. => left.sourceEnv ≤ env
  | .trans first second => first.Ambient ∧ second.Ambient
  | .piDomain _ _ _ child => child.Ambient
  | .applyPi (whole := whole) .. => whole.Ambient
termination_by sizeOf route

/-- Actual endpoint inclusion follows from the finite route evidence. -/
theorem RawGeneratedTypeRoute.ambient_leftBelow
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final)
    (ambient : route.Ambient) : left.sourceEnv ≤ env := by
  match route with
  | .identity .. => rw [Ambient.eq_def] at ambient; exact ambient
  | .same .. | .assigned .. => rw [Ambient.eq_def] at ambient; exact ambient.1
  | .equality (below := below) .. => exact below
  | .typedEquality .. => rw [Ambient.eq_def] at ambient; exact ambient
  | .trans first second =>
    rw [Ambient.eq_def] at ambient
    exact first.ambient_leftBelow ambient.1
  | .piDomain _ _ below _ => exact below
  | .applyPi (sourceBelow := below) .. => exact below
termination_by sizeOf route

theorem RawGeneratedTypeRoute.ambient_rightBelow
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final)
    (ambient : route.Ambient) : right.sourceEnv ≤ env := by
  match route with
  | .identity .. => rw [Ambient.eq_def] at ambient; exact ambient
  | .same .. | .assigned .. => rw [Ambient.eq_def] at ambient; exact ambient.2
  | .equality (below := below) .. | .typedEquality (below := below) .. => exact below
  | .trans first second =>
    rw [Ambient.eq_def] at ambient
    exact second.ambient_rightBelow ambient.2
  | .piDomain _ _ _ child =>
    rw [Ambient.eq_def] at ambient
    exact child.ambient_rightBelow ambient
  | .applyPi (headerBelow := below) .. => exact below
termination_by sizeOf route

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
