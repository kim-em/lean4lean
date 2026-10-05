import Lean4Lean.Theory.Typing.AnchoredOriginalWorldLocatedCoverage

/-! The actual capture environment attached to a retained original owner.
This is the world annotation of the existing location-derived ledger. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv OriginalClosureMeasure OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable def HeaderOwner.worldEnvironment
    {strata : EquationStratification env} {source : List VExpr}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (owner : HeaderOwner field major)
    (controls : OriginalWorldControls strata sourceEnv)
    (initial : WorldEnvironmentProvenance strata U ownerInitial) :
    WorldEnvironmentProvenance strata U (owner.dependencyEnvironment controls.ordered ownerInitial) :=
  match owner with
  | .inl selected | .inr selected => initial.located controls selected.location

/-- The envelope matches the actual original owner in the numeric ledger. -/
theorem HeaderOwner.worldEnvironment_owner
    {strata : EquationStratification env} {source : List VExpr}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (owner : HeaderOwner field major)
    (controls : OriginalWorldControls strata sourceEnv)
    (initial : WorldEnvironmentProvenance strata U ownerInitial) :
    (WorldEnvironmentProvenance.owner controls owner initial).worlds =
      [originalCallWorld controls .expressionReindex owner.node (owner.worldEnvironment controls initial)] := by
  cases owner <;> rfl


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
