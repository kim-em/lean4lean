import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationTypeRouteSide

/-! The finite original history skeleton below all query/frame grammar.
Every endpoint is an actual original display. In particular assigned comparison
stores two actual term occurrences and derives their formation displays;
application specialization keeps the distinct caller and declaration binders.
No certificate, frame, resource table, or semantic relation occurs here. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv OriginalClosureMeasure OriginalEndpointFactor
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096

def originalTypeRouteSide
    (original : Derivation sourceEnv U source A B assigned) (forward : Bool) :
    EndpointRef sourceEnv U source (if forward then A else B) assigned := by
  cases forward
  · exact .right original
  · exact .left original

noncomputable def OriginalCaptureMap.typeEqualityDisplay
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (original : Derivation sourceEnv U source A B assigned) (forward : Bool) :
    OriginalNestedDisplay U common ((if forward then A else B).subst raw) (assigned.subst raw) where
  sourceEnv := sourceEnv
  source := source
  sourceExpression := if forward then A else B
  sourceType := assigned
  context := context
  node := .ref (originalTypeRouteSide original forward)
  provenance := .ofLocation .here context
  raw := raw
  graph := graph
  expression_eq := rfl
  type_eq := rfl

inductive OriginalTypeRouteSyntax (env : VEnv) (U : Nat) (common : List VExpr) :
    {leftExpression leftAssigned rightExpression rightAssigned : VExpr} →
    OriginalNestedDisplay U common leftExpression leftAssigned →
    OriginalNestedDisplay U common rightExpression rightAssigned → Type where
  | identity (display : OriginalNestedDisplay U common expression assigned) :
      OriginalTypeRouteSyntax env U common display display
  | same
      (left : OriginalNestedDisplay U common expression leftAssigned)
      (right : OriginalNestedDisplay U common expression rightAssigned)
      (leftOrdered : left.sourceEnv.Ordered) (rightOrdered : right.sourceEnv.Ordered) :
      OriginalTypeRouteSyntax env U common left right
  | equality {context : ContextDerivation sourceEnv U source}
      (graph : OriginalCaptureMap (common := common) context raw)
      (original : Derivation sourceEnv U source A B (.sort level)) (forward : Bool)
      (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env) :
      OriginalTypeRouteSyntax env U common
        (graph.typeEqualityDisplay original forward) (graph.typeEqualityDisplay original (!forward))
  | typedEquality {context : ContextDerivation sourceEnv U source}
      (graph : OriginalCaptureMap (common := common) context raw)
      (original : Derivation sourceEnv U source A B assigned)
      (left : OriginalNestedDisplay U common expression (.sort level))
      (same : expression = A.subst raw)
      (leftOrdered : left.sourceEnv.Ordered) (ordered : sourceEnv.Ordered)
      (below : sourceEnv ≤ env) :
      OriginalTypeRouteSyntax env U common left (graph.typeEqualityDisplay original false)
  | trans (first : OriginalTypeRouteSyntax env U common left middle)
      (second : OriginalTypeRouteSyntax env U common middle right) :
      OriginalTypeRouteSyntax env U common left right
  | assigned
      (left : OriginalNestedDisplay U common expression leftAssigned)
      (right : OriginalNestedDisplay U common expression rightAssigned)
      (leftOrdered : left.sourceEnv.Ordered) (rightOrdered : right.sourceEnv.Ordered) :
      OriginalTypeRouteSyntax env U common left.formationDisplay right.formationDisplay
  | piDomain (left right : OriginalPiTypeRouteSide U common)
      (leftBelow : left.sourceEnv ≤ env)
      (whole : OriginalTypeRouteSyntax env U common left.display right.display) :
      OriginalTypeRouteSyntax env U common left.domainDisplay right.domainDisplay
  | applyPi (source : OriginalApplicationTypeRouteSide U common)
      (header : OriginalPiTypeRouteSide U common)
      (headerDomain : EndpointRef header.sourceEnv U header.source header.A (.sort header.u))
      (domainEq : header.domain = .ref headerDomain)
      (noBinders : source.location.binderPrefix = [])
      (sourceOrdered : source.sourceEnv.Ordered) (headerOrdered : header.sourceEnv.Ordered)
      (sourceBelow : source.sourceEnv ≤ env) (headerBelow : header.sourceEnv ≤ env)
      (whole : OriginalTypeRouteSyntax env U common source.pi.display header.display) :
      OriginalTypeRouteSyntax env U common source.resultDisplay
        (header.capturedBody headerDomain domainEq source)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
