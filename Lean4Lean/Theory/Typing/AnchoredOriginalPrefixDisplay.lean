import Lean4Lean.Theory.Typing.AnchoredOriginalRawTypeRouteOperations

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

/-- Exposing a prefix preserves the original context and capture graph.
Only the term endpoint and its actual provenance change. -/
noncomputable def originalPrefixDisplay
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {first : EndpointState sourceEnv U source expression assigned}
    {last : EndpointState sourceEnv U source expression natural}
    (initial : ContextDerivation sourceEnv U rootSource) (location : Located root first)
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
    (route : PrefixRoute sourceEnv U source expression first last) :
    OriginalNestedDisplay U common (expression.subst raw) (natural.subst raw) where
  sourceEnv := sourceEnv
  source := source
  sourceExpression := expression
  sourceType := natural
  context := location.contextDerivation initial
  node := last
  provenance := ⟨rootSource, rootExpression, rootType, root, initial,
    route.locate location, (route.locate_contextDerivation location initial).symm⟩
  raw := raw
  graph := graph
  expression_eq := rfl
  type_eq := rfl


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
