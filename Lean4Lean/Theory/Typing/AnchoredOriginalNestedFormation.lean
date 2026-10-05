import Lean4Lean.Theory.Typing.AnchoredOriginalSourceCaptureSyntax

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv OriginalClosureMeasure
open OriginalEndpointFactor
set_option backward.isDefEq.respectTransparency false

/-- The assigned formation retains the actual original term occurrence,
context, capture map and provenance. The assigned source type is never
replaced by the type of a second derivation of the same displayed term. -/
noncomputable def OriginalNestedDisplay.formationDisplay
    (display : OriginalNestedDisplay U common expression assigned) :
    OriginalNestedDisplay U common assigned (.sort display.node.typeFormation.level) where
  sourceEnv := display.sourceEnv
  source := display.source
  sourceExpression := display.sourceType
  sourceType := .sort display.node.typeFormation.level
  context := display.context
  node := display.node.typeFormation.node
  provenance := {
    rootSource := display.provenance.rootSource
    rootExpression := display.provenance.rootExpression
    rootType := display.provenance.rootType
    root := display.provenance.root
    initial := display.provenance.initial
    location := .assignedFormation display.provenance.location
    context_eq := display.provenance.context_eq }
  raw := display.raw
  graph := display.graph
  expression_eq := display.type_eq
  type_eq := rfl

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
