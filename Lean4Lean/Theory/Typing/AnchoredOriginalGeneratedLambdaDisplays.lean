import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedPiDisplays

/-! Lambda source displays retain each side's independent original domain,
codomain, and body while sharing only raw displayed syntax. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

section
variable
  {sourceEnv : VEnv} {source : List VExpr} {raw : Subst}
  {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
  {domain : EndpointRef sourceEnv U source A (.sort u)}
  {codomain : EndpointState sourceEnv U (A :: source) B (.sort v)}
  {body : EndpointState sourceEnv U (A :: source) b B}
  {hu : u.WF U} {hv : v.WF U}
  (location : Located root (.lam hu hv (.ref domain) codomain body))
  (initial : ContextDerivation sourceEnv U rootSource)
  (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
  (annotationEq : annotation = A.subst raw)
  (bodyEq : displayedBody = b.subst raw.lift)

noncomputable def OriginalNestedDisplay.lambda :
    OriginalNestedDisplay U common (.lam annotation displayedBody)
      (.forallE annotation (B.subst raw.lift)) where
  sourceEnv := sourceEnv
  source := source
  sourceExpression := .lam A b
  sourceType := .forallE A B
  context := location.contextDerivation initial
  node := .lam hu hv (.ref domain) codomain body
  provenance := .ofLocation location initial
  raw := raw
  graph := graph
  expression_eq := by simp only [subst, ← annotationEq, ← bodyEq]
  type_eq := by simp only [subst, ← annotationEq]

noncomputable def OriginalNestedDisplay.lambdaDomain :
    OriginalNestedDisplay U common annotation (.sort u) where
  sourceEnv := sourceEnv
  source := source
  sourceExpression := A
  sourceType := .sort u
  context := location.contextDerivation initial
  node := .ref domain
  provenance := .ofLocation (.lamDomain location) initial
  raw := raw
  graph := graph
  expression_eq := annotationEq
  type_eq := rfl

noncomputable def OriginalNestedDisplay.lambdaBody :
    OriginalNestedDisplay U (annotation :: common) displayedBody (B.subst raw.lift) where
  sourceEnv := sourceEnv
  source := A :: source
  sourceExpression := b
  sourceType := B
  context := .cons (location.contextDerivation initial) domain
  node := body
  provenance := {
    rootSource := rootSource, rootExpression := rootExpression, rootType := rootType
    root := root, initial := initial, location := .lamBody location
    context_eq := by
      have selected : Classical.choose location.originalDomains.1 = domain :=
        (EndpointState.ref.inj (Classical.choose_spec location.originalDomains.1)).symm
      change ContextDerivation.cons (location.contextDerivation initial) domain =
        ContextDerivation.cons (location.contextDerivation initial) (Classical.choose location.originalDomains.1)
      rw [selected] }
  raw := raw.lift
  graph := .bind graph domain annotation annotationEq.symm
  expression_eq := bodyEq
  type_eq := rfl

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
