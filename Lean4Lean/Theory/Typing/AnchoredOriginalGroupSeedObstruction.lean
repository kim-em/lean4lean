import Lean4Lean.Theory.Typing.AnchoredOriginalRichPendingCapture

/-! Empty capture groups must retain an independent actual owner seed.
Charged roots alone do not imply that the nominal capture occurs in them. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- Even allowing all assigned-formation and exposure paths, a unit-weight
original root cannot own a lambda occurrence. -/
theorem Located.noLambda_of_weight_le_one
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U context (.lam A body) assigned}
    (location : Located root node) (small : root.origin.weight ≤ 1) : False := by
  let view := lamView location
  have selected := view.location.cost_le []
  have positive := (Closure.close view.domain.origin (view.location.environment [])).cost_pos
  have strict := binder_domain_cost view.domain.origin [view.codomain.origin, view.body.origin] []
    (view.location.environment [])
  change (Closure.close (.binder view.domain.origin [view.codomain.origin, view.body.origin] [])
    (view.location.environment [])).cost ≤ _ at selected
  have rootCost : (Closure.close root.origin []).cost = root.origin.weight := by
    simp [Closure.cost, environmentCost]
  rw [rootCost] at selected
  omega

/-- The expression-origin requirement already fails before a query,
formation certificate, or alignment can be requested. -/
theorem HeaderOwner.noLambda_of_small_roots
    {source : List VExpr} {A body : VExpr} {ρ : Lift}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (owner : HeaderOwner field major)
    (fieldSmall : field.origin.weight ≤ 1) (majorSmall : major.origin.weight ≤ 1)
    (same : owner.expression = (VExpr.lam A body).lift' ρ) : False := by
  cases owner with
  | inl origin =>
    cases origin with
    | mk context expression assigned node location =>
      change expression = .lam (A.lift' ρ) (body.lift' ρ.cons) at same
      cases same
      exact Located.noLambda_of_weight_le_one location fieldSmall
  | inr origin =>
    cases origin with
    | mk context expression assigned node location =>
      change expression = .lam (A.lift' ρ) (body.lift' ρ.cons) at same
      cases same
      exact Located.noLambda_of_weight_le_one location majorSmall

/-- Taking both charged roots to actual sort derivations satisfies the
small-root premise. A lambda nominal capture can therefore have no pending
owner under those roots, regardless of its requested profile. -/
theorem PendingRichCapture.noLambda_of_small_roots
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource domainExpression (.sort level)}
    (fieldSmall : field.origin.weight ≤ 1) (majorSmall : major.origin.weight ≤ 1)
    (pending : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial (.lam A body) leftValue rightValue) : False :=
  pending.owner.noLambda_of_small_roots fieldSmall majorSmall pending.expression_eq


/-- Actual sort references provide concrete roots for the obstruction. -/
theorem PendingRichCapture.noLambda_under_sort_roots
    {source : List VExpr} {u : VLevel} {U : Nat} (wellformed : u.WF U)
    {domain : EndpointRef headerEnv U headerSource domainExpression (.sort level)}
    (pending : PendingRichCapture
      (field := (EndpointRef.left (Derivation.sortDF (env := sourceEnv) (Γ := source) wellformed wellformed rfl)))
      (major := (EndpointRef.left (Derivation.sortDF (env := sourceEnv) (Γ := source) wellformed wellformed rfl)))
      domain env registry target headerLocals declaredLeft headerAvailable ownerInitial
      (.lam A body) leftValue rightValue) : False :=
  pending.noLambda_of_small_roots (by simp [EndpointRef.origin, Derivation.origin, Origin.weight])
    (by simp [EndpointRef.origin, Derivation.origin, Origin.weight])

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
