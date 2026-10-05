import Lean4Lean.Theory.Typing.AnchoredOriginalRawTypeRoute

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- The right variable is an actual original endpoint. Its source capture
map retains the nominal original value; selected query owners are separate. -/
def groupCaptureVariableDisplay
    {context : ContextDerivation headerEnv U headerSource}
    (graph : OriginalCaptureMap (common := common) context raw)
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    {nominalContext : ContextDerivation nominalEnv U nominalSource}
    (nominalGraph : OriginalCaptureMap (common := common) nominalContext nominalRaw)
    (nominal : EndpointState nominalEnv U nominalSource argument assigned)
    (provenance : EndpointProvenance nominalContext nominal)
    (variableNode : EndpointState headerEnv U (A :: headerSource) (.bvar 0) variableType)
    (variableProvenance : EndpointProvenance (.cons context domain) variableNode) :
    OriginalNestedDisplay U common (argument.subst nominalRaw)
      (variableType.subst (raw.cons (argument.subst nominalRaw))) where
  sourceEnv := headerEnv
  source := A :: headerSource
  sourceExpression := .bvar 0
  sourceType := variableType
  context := .cons context domain
  node := variableNode
  provenance := variableProvenance
  raw := raw.cons (argument.subst nominalRaw)
  graph := .capture graph domain nominalGraph nominal provenance
  expression_eq := rfl
  type_eq := rfl

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
