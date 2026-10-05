import Lean4Lean.Theory.Typing.AnchoredOriginalRichConstructorPlanResult

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

/-- Profile-indexed form of the concrete plan/type packet, for structural
recursion through arbitrary finite padding and views. -/
structure RichConstructorProfileResult
    {sourceEnv : VEnv} {U : Nat}
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    {declaredType : VExpr} {headerLevel : VLevel}
    (header : EndpointRef sourceEnv U [] declaredType (.sort headerLevel))
    (name : Name) (levels : List VLevel) (signature : ConstantTelescope declaredType)
    {source : List VExpr} (context : ContextDerivation sourceEnv U source)
    {expression assigned : VExpr} (node : EndpointState sourceEnv U source expression assigned)
    (σ : Subst) (arguments : List VExpr) (available : Valuation) (demand : Profile n) where
  footprint : Footprint
  plan : RichConstructorPlan env U registry target header name levels signature context σ arguments demand footprint
  resources : footprint.Available available
  support : Profile n
  typeFootprint : Footprint
  certificate : RichCert sourceEnv env U registry target node (List.range arguments.length) σ true support typeFootprint
  typeResources : typeFootprint.Available available
  typed : demand.HasType support

def RichConstructorPlanResult.toProfile
    (result : RichConstructorPlanResult env U registry target header name levels signature context node σ arguments available atom) :
    RichConstructorProfileResult env registry target header name levels signature context node σ arguments available (.singleton atom) :=
  ⟨result.footprint, result.plan, result.resources, result.support, result.typeFootprint,
    result.certificate, result.typeResources, result.typed⟩

def RichConstructorProfileResult.toAtom
    (result : RichConstructorProfileResult (U := U) env registry target header name levels signature context node σ arguments available (.singleton atom)) :
    RichConstructorPlanResult env U registry target header name levels signature context node σ arguments available atom :=
  ⟨result.footprint, result.plan, result.resources, result.support, result.typeFootprint,
    result.certificate, result.typeResources, result.typed⟩

def RichConstructorProfileResult.pad
    (result : RichConstructorProfileResult (U := U) env registry target header name levels signature context node σ arguments available demand) :
    RichConstructorProfileResult env registry target header name levels signature context node σ arguments available demand.pad :=
  ⟨result.footprint, .pad result.plan, result.resources, result.support.pad, result.typeFootprint,
    .pad result.certificate, result.typeResources, result.typed.pad⟩

noncomputable def RichConstructorProfileResult.view
    (result : RichConstructorProfileResult (U := U) env registry target header name levels signature context node σ arguments available (.singleton atom))
    (view : AtomView env U registry target atom next) :
    RichConstructorProfileResult env registry target header name levels signature context node σ arguments available (.singleton next) :=
  (result.toAtom.view view).toProfile

def RichConstructorProfileResult.restoreRoute
    (route : PrefixRoute sourceEnv U source expression first last)
    (result : RichConstructorProfileResult (U := U) env registry target header name levels signature context last σ arguments available demand) :
    RichConstructorProfileResult env registry target header name levels signature context first σ arguments available demand :=
  { result with certificate := .route route result.certificate }

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
