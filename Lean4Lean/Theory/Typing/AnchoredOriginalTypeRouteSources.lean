import Lean4Lean.Theory.Typing.AnchoredOriginalRawTypeRouteAmbient

/-! Hereditary source-environment predicates for finite type histories.
Unlike ambient inclusion, this records equality/application sources even when
the constructor already carries a subenvironment proof. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096

def RawGeneratedTypeRoute.AllSources (P : VEnv → Prop)
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final) : Prop :=
  P left.sourceEnv ∧ P right.sourceEnv ∧ match route with
  | .trans first second => first.AllSources P ∧ second.AllSources P
  | .piDomain _ _ _ child => child.AllSources P
  | .applyPi (whole := whole) .. => whole.AllSources P
  | .identity .. | .same .. | .assigned .. | .equality .. | .typedEquality .. => True
termination_by sizeOf route

theorem RawGeneratedTypeRoute.AllSources.left
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    {route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final}
    (sources : route.AllSources P) : P left.sourceEnv := by
  rw [RawGeneratedTypeRoute.AllSources.eq_def] at sources
  exact sources.1

theorem RawGeneratedTypeRoute.AllSources.right
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    {route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final}
    (sources : route.AllSources P) : P right.sourceEnv := by
  rw [RawGeneratedTypeRoute.AllSources.eq_def] at sources
  exact sources.2.1

theorem RawGeneratedTypeRoute.AllSources.mono
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final)
    (sources : route.AllSources P) (implication : ∀ source, P source → Q source) : route.AllSources Q := by
  match route with
  | .trans first second =>
    rw [RawGeneratedTypeRoute.AllSources.eq_def] at sources ⊢
    exact ⟨implication _ sources.1, implication _ sources.2.1,
      RawGeneratedTypeRoute.AllSources.mono first sources.2.2.1 implication,
      RawGeneratedTypeRoute.AllSources.mono second sources.2.2.2 implication⟩
  | .piDomain _ _ _ child =>
    rw [RawGeneratedTypeRoute.AllSources.eq_def] at sources ⊢
    exact ⟨implication _ sources.1, implication _ sources.2.1,
      RawGeneratedTypeRoute.AllSources.mono child sources.2.2 implication⟩
  | .applyPi (whole := whole) .. =>
    rw [RawGeneratedTypeRoute.AllSources.eq_def] at sources ⊢
    exact ⟨implication _ sources.1, implication _ sources.2.1,
      RawGeneratedTypeRoute.AllSources.mono whole sources.2.2 implication⟩
  | .identity .. | .same .. | .assigned .. | .equality .. | .typedEquality .. =>
    rw [RawGeneratedTypeRoute.AllSources.eq_def] at sources ⊢
    exact ⟨implication _ sources.1, implication _ sources.2.1, trivial⟩
termination_by sizeOf route


theorem RawGeneratedTypeRoute.AllSources.ofAmbient
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final)
    (ambient : route.Ambient) (included : ∀ source, source ≤ env → P source) : route.AllSources P := by
  match route with
  | .identity .. =>
    rw [RawGeneratedTypeRoute.Ambient.eq_def] at ambient
    rw [RawGeneratedTypeRoute.AllSources.eq_def]
    exact ⟨included _ ambient, included _ ambient, trivial⟩
  | .same .. | .assigned .. =>
    rw [RawGeneratedTypeRoute.Ambient.eq_def] at ambient
    rw [RawGeneratedTypeRoute.AllSources.eq_def]
    exact ⟨included _ ambient.1, included _ ambient.2, trivial⟩
  | .equality (below := below) .. =>
    rw [RawGeneratedTypeRoute.AllSources.eq_def]
    exact ⟨included _ below, included _ below, trivial⟩
  | .typedEquality (below := below) .. =>
    rw [RawGeneratedTypeRoute.Ambient.eq_def] at ambient
    rw [RawGeneratedTypeRoute.AllSources.eq_def]
    exact ⟨included _ ambient, included _ below, trivial⟩
  | .trans first second =>
    rw [RawGeneratedTypeRoute.Ambient.eq_def] at ambient
    have firstSources := RawGeneratedTypeRoute.AllSources.ofAmbient first ambient.1 included
    have secondSources := RawGeneratedTypeRoute.AllSources.ofAmbient second ambient.2 included
    rw [RawGeneratedTypeRoute.AllSources.eq_def]
    exact ⟨firstSources.left, secondSources.right, firstSources, secondSources⟩
  | .piDomain _ _ below child =>
    rw [RawGeneratedTypeRoute.Ambient.eq_def] at ambient
    have childSources := RawGeneratedTypeRoute.AllSources.ofAmbient child ambient included
    rw [RawGeneratedTypeRoute.AllSources.eq_def]
    exact ⟨included _ below, childSources.right, childSources⟩
  | .applyPi (sourceBelow := sourceBelow) (headerBelow := headerBelow) (whole := whole) .. =>
    rw [RawGeneratedTypeRoute.Ambient.eq_def] at ambient
    have childSources := RawGeneratedTypeRoute.AllSources.ofAmbient whole ambient included
    rw [RawGeneratedTypeRoute.AllSources.eq_def]
    exact ⟨included _ sourceBelow, included _ headerBelow, childSources⟩
termination_by sizeOf route

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
