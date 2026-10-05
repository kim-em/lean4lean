import Lean4Lean.Theory.Typing.AnchoredOriginalNestedFormation

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv OriginalClosureMeasure
open OriginalEndpointFactor
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- A native Pi and its actual domain are two locations in the SAME retained
original tree. No domain source certificate is transported by definitional
rewriting to a different occurrence. -/
structure OriginalPiTypeRouteSide (U : Nat) (common : List VExpr) where
  sourceEnv : VEnv
  source : List VExpr
  A : VExpr
  B : VExpr
  u : VLevel
  v : VLevel
  hu : u.WF U
  hv : v.WF U
  domain : EndpointState sourceEnv U source A (.sort u)
  body : EndpointState sourceEnv U (A :: source) B (.sort v)
  rootSource : List VExpr
  rootExpression : VExpr
  rootType : VExpr
  root : EndpointRef sourceEnv U rootSource rootExpression rootType
  initial : ContextDerivation sourceEnv U rootSource
  location : Located root (.pi hu hv domain body)
  raw : Subst
  graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw

noncomputable def OriginalPiTypeRouteSide.display (side : OriginalPiTypeRouteSide U common) :=
  OriginalNestedDisplay.ofOccurrence side.initial side.location side.graph

noncomputable def OriginalPiTypeRouteSide.domainDisplay (side : OriginalPiTypeRouteSide U common) :=
  OriginalNestedDisplay.ofOccurrence side.initial (.piDomain side.location) side.graph


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
