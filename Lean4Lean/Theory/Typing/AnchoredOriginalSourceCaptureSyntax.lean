import Lean4Lean.Theory.Typing.AnchoredOriginalDisplay

/-! Positive source-map syntax, independent of query certificates and their
semantic realizations. Captures retain their actual original owner and raw
substitution; they do not assert typing at the captured domain. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv OriginalClosureMeasure OriginalEndpointFactor

inductive OriginalCaptureMap :
    {sourceEnv : VEnv} → {U : Nat} → {source common : List VExpr} →
    ContextDerivation sourceEnv U source → Subst → Type where
  | empty (common : List VExpr) :
      OriginalCaptureMap (common := common) (ContextDerivation.nil (env := sourceEnv) (U := U)) .id
  | identity (context : ContextDerivation sourceEnv U source) :
      OriginalCaptureMap (common := source) context .id
  | tail
      {context : ContextDerivation sourceEnv U source}
      {domain : EndpointRef sourceEnv U source A (.sort level)}
      (graph : OriginalCaptureMap (common := common) (.cons context domain) raw) :
      OriginalCaptureMap (common := common) context raw.tail
  | capture
      {context : ContextDerivation headerEnv U headerSource}
      (tail : OriginalCaptureMap (common := common) context raw)
      (domain : EndpointRef headerEnv U headerSource A (.sort level))
      {ownerContext : ContextDerivation ownerEnv U ownerSource}
      (ownerMap : OriginalCaptureMap (common := common) ownerContext ownerRaw)
      (owner : EndpointState ownerEnv U ownerSource argument assigned)
      (provenance : EndpointProvenance ownerContext owner) :
      OriginalCaptureMap (common := common) (.cons context domain)
        (raw.cons (argument.subst ownerRaw))
  | bind
      {context : ContextDerivation sourceEnv U source}
      (graph : OriginalCaptureMap (common := common) context raw)
      (domain : EndpointRef sourceEnv U source A (.sort level))
      (annotation : VExpr) (displayed : A.subst raw = annotation) :
      OriginalCaptureMap (common := annotation :: common) (.cons context domain) raw.lift
  | weaken
      (graph : OriginalCaptureMap (common := common) context raw)
      {ρ : Lift} (insertion : Ctx.Lift' ρ common next) :
      OriginalCaptureMap (common := next) context (raw.lift_r ρ)

/-- Displays are computed from the finite source map. No original node is
relabeled to the substituted expression or assigned type. -/
structure OriginalNestedDisplay
    (U : Nat) (common : List VExpr) (expression assigned : VExpr) where
  sourceEnv : VEnv
  source : List VExpr
  sourceExpression : VExpr
  sourceType : VExpr
  context : ContextDerivation sourceEnv U source
  node : EndpointState sourceEnv U source sourceExpression sourceType
  provenance : EndpointProvenance context node
  raw : Subst
  graph : OriginalCaptureMap (common := common) context raw
  expression_eq : expression = sourceExpression.subst raw
  type_eq : assigned = sourceType.subst raw

noncomputable def OriginalNestedDisplay.ofOccurrence
    {sourceEnv : VEnv} {source common : List VExpr} {raw : Subst}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned}
    (initial : ContextDerivation sourceEnv U rootSource) (location : Located root node)
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw) :
    OriginalNestedDisplay U common (expression.subst raw) (assigned.subst raw) :=
  ⟨sourceEnv, source, expression, assigned, location.contextDerivation initial, node,
    .ofLocation location initial, raw, graph, rfl, rfl⟩

theorem OriginalNestedDisplay.realizedExpression
    {source : List VExpr}
    (display : OriginalNestedDisplay U source expression assigned) (common : Subst) :
    display.sourceExpression.subst (display.raw.comp common) = expression.subst common := by
  exact subst_subst.symm.trans (congrArg (·.subst common) display.expression_eq.symm)

theorem OriginalNestedDisplay.realizedType
    {source : List VExpr}
    (display : OriginalNestedDisplay U source expression assigned) (common : Subst) :
    display.sourceType.subst (display.raw.comp common) = assigned.subst common := by
  exact subst_subst.symm.trans (congrArg (·.subst common) display.type_eq.symm)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
