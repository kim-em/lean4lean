import Lean4Lean.Theory.Typing.AnchoredOriginalConstructorProfileResult
import Lean4Lean.Theory.Typing.AnchoredOriginalConstructorSpine
import Lean4Lean.Theory.Typing.AnchoredOriginalStagedConstructorTerminalReindex

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

/-- A recursive telescope result retains the selected parent and every
pre-existing capture need, so the next enclosing binder can close it. -/
structure ConstructorSpineReply
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {header : EndpointRef sourceEnv U [] declaredType (.sort headerLevel)}
    {signature : ConstantTelescope declaredType}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source expression assigned}
    {graph : OriginalCaptureMap (common := common) context raw}
    (P : VEnv → Prop) (name : Name) (levels : List VLevel) (arguments : List VExpr)
    (frame : OriginalCaptureRealization graph env registry target (List.range arguments.length)
      commonLeft commonRight available)
    (ordered : sourceEnv.Ordered) (demand : Profile n) where
  nextAvailable : Valuation
  nextFrame : OriginalCaptureRealization graph env registry target (List.range arguments.length)
    commonLeft commonRight nextAvailable
  generation : SourceCaptureGenerated P base caps commonLeft commonRight graph nextFrame.frame.raw
  closed : nextAvailable.AtomClosed
  included : ∀ index need, need ∈ available index → need ∈ nextAvailable index
  result : RichConstructorProfileResult env registry target header name levels signature context node
    (raw.comp commonLeft) arguments nextAvailable demand
  bounded : environmentCost (nextFrame.frame.dependencyEnvironment ordered) ≤
    environmentCost (frame.frame.dependencyEnvironment ordered)

noncomputable def constructorOccurrenceDisplay
    {root : EndpointRef sourceEnv U [] declaredType (.sort headerLevel)}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source expression assigned}
    (location : Located root node) (lineage : location.contextDerivation .nil = context)
    (graph : OriginalCaptureMap (common := common) context raw) :
    OriginalNestedDisplay U common (expression.subst raw) (assigned.subst raw) := {
  sourceEnv := sourceEnv, source := source, sourceExpression := expression, sourceType := assigned
  context := context, node := node
  provenance := ⟨_, _, _, root, .nil, location, lineage.symm⟩
  raw := raw, graph := graph, expression_eq := rfl, type_eq := rfl }

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
