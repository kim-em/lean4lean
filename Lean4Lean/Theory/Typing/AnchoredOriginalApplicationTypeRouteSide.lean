import Lean4Lean.Theory.Typing.AnchoredOriginalPiTypeRouteSide

/-! Original application occurrences and their capture displays, independent
of generated-frame predicates and semantic replay. These are finite source
provenance data for application specialization in type histories. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv OriginalClosureMeasure
open OriginalEndpointFactor
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

section
variable
  {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
  (initial : ContextDerivation sourceEnv U rootSource)
  (domain : EndpointRef sourceEnv U source A (.sort u))
  (body : EndpointState sourceEnv U (A :: source) B (.sort v))
  (function : EndpointState sourceEnv U source f (.forallE A B))
  (argument : EndpointState sourceEnv U source a A)
  (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
  (hu : u.WF U) (hv : v.WF U)
  (location : Located root (.app hu hv (.ref domain) body function argument result))
  (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)

noncomputable def applicationResultDisplay :
    OriginalNestedDisplay U common ((B.inst a).subst raw) (.sort v) := {
  sourceEnv := sourceEnv, source := source, sourceExpression := B.inst a, sourceType := .sort v
  context := location.contextDerivation initial, node := result
  provenance := .ofLocation (.appResult location) initial
  raw := raw, graph := graph, expression_eq := rfl, type_eq := rfl }

noncomputable def applicationBodyDisplay :
    OriginalNestedDisplay U common ((B.inst a).subst raw) (.sort v) := {
  sourceEnv := sourceEnv, source := A :: source, sourceExpression := B, sourceType := .sort v
  context := .cons (location.contextDerivation initial) domain, node := body
  provenance := by
    have contextEq : (Located.appCodomain location).contextDerivation initial =
        .cons (location.contextDerivation initial) domain := by
      change ContextDerivation.cons (location.contextDerivation initial) (Classical.choose location.originalDomains.1) = _
      exact congrArg (ContextDerivation.cons (location.contextDerivation initial))
        (EndpointState.ref.inj (Classical.choose_spec location.originalDomains.1).symm)
    exact contextEq ▸ EndpointProvenance.ofLocation (.appCodomain location) initial
  raw := raw.cons (a.subst raw)
  graph := .capture graph domain graph argument (.ofLocation (.appArgument location) initial)
  expression_eq := by rw [subst_inst, inst_lift_cons]
  type_eq := rfl }

end

structure OriginalApplicationTypeRouteSide (U : Nat) (common : List VExpr) where
  sourceEnv : VEnv
  source : List VExpr
  A : VExpr
  B : VExpr
  f : VExpr
  a : VExpr
  u : VLevel
  v : VLevel
  hu : u.WF U
  hv : v.WF U
  domain : EndpointRef sourceEnv U source A (.sort u)
  body : EndpointState sourceEnv U (A :: source) B (.sort v)
  function : EndpointState sourceEnv U source f (.forallE A B)
  argument : EndpointState sourceEnv U source a A
  result : EndpointState sourceEnv U source (B.inst a) (.sort v)
  rootSource : List VExpr
  rootExpression : VExpr
  rootType : VExpr
  root : EndpointRef sourceEnv U rootSource rootExpression rootType
  initial : ContextDerivation sourceEnv U rootSource
  location : Located root (.app hu hv (.ref domain) body function argument result)
  raw : Subst
  graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw

/-- Construct the route side directly from an actual original application
occurrence; no source endpoint is synthesized for the substituted result. -/
noncomputable def originalApplicationTypeRouteSide
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (function : EndpointState sourceEnv U source f (.forallE A B))
    (argument : EndpointState sourceEnv U source a A)
    (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (location : Located root (.app hu hv (.ref domain) body function argument result))
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw) :
    OriginalApplicationTypeRouteSide U common :=
  ⟨sourceEnv, source, A, B, f, a, u, v, hu, hv, domain, body, function, argument,
    result, rootSource, rootExpression, rootType, root, initial, location, raw, graph⟩

noncomputable def OriginalApplicationTypeRouteSide.node
    (side : OriginalApplicationTypeRouteSide U common) :=
  EndpointState.app side.hu side.hv (.ref side.domain) side.body side.function side.argument side.result

noncomputable def OriginalApplicationTypeRouteSide.pi
    (side : OriginalApplicationTypeRouteSide U common) : OriginalPiTypeRouteSide U common where
  sourceEnv := side.sourceEnv
  source := side.source
  A := side.A
  B := side.B
  u := side.u
  v := side.v
  hu := side.hu
  hv := side.hv
  domain := .ref side.domain
  body := side.body
  rootSource := side.rootSource
  rootExpression := side.rootExpression
  rootType := side.rootType
  root := side.root
  initial := side.initial
  location := .appPiFormation side.location
  raw := side.raw
  graph := side.graph

noncomputable def OriginalApplicationTypeRouteSide.argumentDisplay
    (side : OriginalApplicationTypeRouteSide U common) :=
  OriginalNestedDisplay.ofOccurrence side.initial (.appArgument side.location) side.graph

noncomputable def OriginalApplicationTypeRouteSide.resultDisplay
    (side : OriginalApplicationTypeRouteSide U common) :=
  applicationResultDisplay side.initial side.domain side.body side.function side.argument side.result
    side.hu side.hv side.location side.graph

noncomputable def OriginalApplicationTypeRouteSide.ownBodyDisplay
    (side : OriginalApplicationTypeRouteSide U common) :=
  applicationBodyDisplay side.initial side.domain side.body side.function side.argument side.result
    side.hu side.hv side.location side.graph

/-- This display captures the actual caller argument in the original header
body. It makes no claim that the argument was originally typed at that header
domain. The separately generated target frame must establish that alignment. -/
noncomputable def OriginalPiTypeRouteSide.capturedBody
    (side : OriginalPiTypeRouteSide U common)
    (domain : EndpointRef side.sourceEnv U side.source side.A (.sort side.u))
    (domainEq : side.domain = .ref domain)
    (owner : OriginalApplicationTypeRouteSide U common) :
    OriginalNestedDisplay U common
      (side.B.subst (side.raw.cons (owner.a.subst owner.raw))) (.sort side.v) where
  sourceEnv := side.sourceEnv
  source := side.A :: side.source
  sourceExpression := side.B
  sourceType := .sort side.v
  context := .cons (side.location.contextDerivation side.initial) domain
  node := side.body
  provenance := by
    have contextEq : (Located.piBody side.location).contextDerivation side.initial =
        .cons (side.location.contextDerivation side.initial) domain := by
      change ContextDerivation.cons (side.location.contextDerivation side.initial)
        (Classical.choose side.location.originalDomains.1) = _
      exact congrArg (ContextDerivation.cons (side.location.contextDerivation side.initial))
        (EndpointState.ref.inj ((Classical.choose_spec side.location.originalDomains.1).symm.trans domainEq))
    exact contextEq ▸ EndpointProvenance.ofLocation (.piBody side.location) side.initial
  raw := side.raw.cons (owner.a.subst owner.raw)
  graph := .capture side.graph domain owner.graph owner.argument
    (.ofLocation (.appArgument owner.location) owner.initial)
  expression_eq := rfl
  type_eq := rfl

noncomputable def originalNativePiRouteSide
    {root : EndpointRef headerEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation headerEnv U rootSource)
    (domain : EndpointRef headerEnv U headerSource A (.sort u))
    (body : EndpointState headerEnv U (A :: headerSource) B (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (location : Located root (.pi hu hv (.ref domain) body))
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw) :
    OriginalPiTypeRouteSide U common :=
  ⟨headerEnv, headerSource, A, B, u, v, hu, hv, .ref domain, body,
    rootSource, rootExpression, rootType, root, initial, location, raw, graph⟩

noncomputable def OriginalApplicationTypeRouteSide.termDisplay
    (side : OriginalApplicationTypeRouteSide U common) :
    OriginalNestedDisplay U common ((VExpr.app side.f side.a).subst side.raw)
      ((side.B.inst side.a).subst side.raw) :=
  .ofOccurrence side.initial side.location side.graph

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
