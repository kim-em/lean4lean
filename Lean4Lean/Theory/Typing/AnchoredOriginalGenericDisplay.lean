import Lean4Lean.Theory.Typing.AnchoredOriginalGenericComputational
import Lean4Lean.Theory.Typing.AnchoredOriginalCoherenceContract

/-! Ordinary original displays equipped with arbitrary actual rich source
frames. Costs use those frames, including captured argument owners and
heterogeneous groups. The fixed-frame C/R contracts below are induction
obligations; they do not assert global reindexing or choose destination
resources before the query graph has produced them. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

structure OriginalRichDisplayFrame
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    {sourceEnv : VEnv} {U : Nat} {displayed : List VExpr} {expression assigned : VExpr}
    (display : EndpointDisplay sourceEnv U displayed expression assigned)
    (common : Subst) (locals : List Nat) (available : Valuation) where
  frame : OriginalRichFrame sourceEnv env U registry target display.context locals
    (display.sourceSubst common) (display.sourceSubst common) available
  substitutions : Ctx.SubstEq env U target (display.sourceSubst common) (display.sourceSubst common) display.source

noncomputable def OriginalRichDisplayFrame.cost
    {display : EndpointDisplay sourceEnv U displayed expression assigned}
    (frame : OriginalRichDisplayFrame env registry target display common locals available)
    (ordered : sourceEnv.Ordered) : Nat :=
  (Closure.close (display.node.dependencyOrigin ordered) (frame.frame.dependencyEnvironment ordered)).cost

/-- Change only the common displayed spelling, preserving every original
source node, location, context, weakening map and semantic frame. -/
def _root_.Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.EndpointDisplay.relabelExpression
    (display : EndpointDisplay sourceEnv U displayed expression assigned)
    (same : newExpression = expression) : EndpointDisplay sourceEnv U displayed newExpression assigned :=
  { display with expression_eq := same.trans display.expression_eq }

def OriginalRichDisplayFrame.relabelExpression
    {display : EndpointDisplay sourceEnv U displayed expression assigned}
    (frame : OriginalRichDisplayFrame env registry target display common locals available)
    (same : newExpression = expression) :
    OriginalRichDisplayFrame env registry target (display.relabelExpression same) common locals available :=
  ⟨frame.frame, frame.substitutions⟩

/-- The source occurrence for an assigned-type query is computed from its
original endpoint and location, while source weakening remains delayed. -/
noncomputable def _root_.Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.EndpointDisplay.formationDisplay
    (display : EndpointDisplay sourceEnv U displayed expression assigned) :
    EndpointDisplay sourceEnv U displayed assigned (.sort display.node.typeFormation.level) where
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
  map := display.map
  insertion := display.insertion
  expression_eq := display.type_eq
  type_eq := rfl

noncomputable def OriginalRichDisplayFrame.formation
    {display : EndpointDisplay sourceEnv U displayed expression assigned}
    (frame : OriginalRichDisplayFrame env registry target display common locals available) :
    OriginalRichDisplayFrame env registry target display.formationDisplay common locals available :=
  ⟨frame.frame, frame.substitutions⟩

theorem OriginalRichDisplayFrame.formation_cost_le
    {display : EndpointDisplay sourceEnv U displayed expression assigned}
    (frame : OriginalRichDisplayFrame env registry target display common locals available)
    (ordered : sourceEnv.Ordered) :
    frame.formation.cost ordered ≤ frame.cost ordered :=
  display.node.typeFormation_dependency_cost_le ordered (frame.frame.dependencyEnvironment ordered)

/-- Same displayed term, potentially different assigned types. Both source
certificates remain indexed by their actual computed formation occurrences.
The raw path is independent of whether a query is empty. -/
structure OriginalRichDisplayCoherence
    {left : EndpointDisplay leftEnv U displayed expression leftType}
    {right : EndpointDisplay rightEnv U displayed expression rightType}
    (leftFrame : OriginalRichDisplayFrame env registry target left common leftLocals leftAvailable)
    (rightFrame : OriginalRichDisplayFrame env registry target right common rightLocals rightAvailable) : Prop where
  path : TypeConversion env U target (leftType.subst common) (rightType.subst common)
  queries : RichCodeTransfer env U registry target left.node.typeFormation.node right.node.typeFormation.node
    leftLocals rightLocals (left.sourceSubst common) (right.sourceSubst common) leftAvailable rightAvailable

/-- Same displayed source expression at two original formation occurrences.
Sort equalities only cast the retained nodes; no proof is reconstructed. -/
def OriginalRichDisplayReindex
    {left : EndpointDisplay leftEnv U displayed expression leftType}
    {right : EndpointDisplay rightEnv U displayed expression rightType}
    (_leftFrame : OriginalRichDisplayFrame env registry target left common leftLocals leftAvailable)
    (_rightFrame : OriginalRichDisplayFrame env registry target right common rightLocals rightAvailable) : Prop :=
  ∀ {leftLevel rightLevel : VLevel}
    (leftSort : left.sourceType = .sort leftLevel) (rightSort : right.sourceType = .sort rightLevel),
    RichCodeTransfer env U registry target (left.node.cast rfl leftSort) (right.node.cast rfl rightSort)
      leftLocals rightLocals (left.sourceSubst common) (right.sourceSubst common) leftAvailable rightAvailable

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
