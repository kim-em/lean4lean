import Lean4Lean.Theory.Typing.AnchoredOriginalGenericPiComputational
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiComputationalReplay

/-! Complete paired Pi F through the rich and legacy query grammars. The
native step consumes only strictly smaller fixed original child calls. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
variable {root : EndpointRef headerEnv U rootSource rootExpression rootType}

theorem OriginalRichFrame.piComputationalInterpret
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (hf : headerEnv.Ordered) (initialContext : ContextDerivation headerEnv U rootSource)
    (domain : EndpointRef headerEnv U headerSource A (.sort u))
    (location : Located root (.ref domain)) (lineage : location.contextDerivation initialContext = context)
    (body : EndpointState headerEnv U (A :: headerSource) B (.sort v))
    (bodyLocation : Located root body)
    (bodyLineage : bodyLocation.contextDerivation initialContext = .cons context domain)
    (hu : u.WF U) (hv : v.WF U)
    (frame : OriginalRichFrame headerEnv env U registry target context locals σ τ available)
    (domainF : OriginalComputationalInductionAt env registry hf initialContext location
      (Closure.close ((EndpointState.pi hu hv (.ref domain) body).dependencyOrigin hf)
        (frame.dependencyEnvironment hf)).cost)
    (bodyF : OriginalComputationalInductionAt env registry hf initialContext bodyLocation
      (Closure.close ((EndpointState.pi hu hv (.ref domain) body).dependencyOrigin hf)
        (frame.dependencyEnvironment hf)).cost)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ headerSource)
    {profile : Profile n}
    (query : RichObs headerEnv env U registry target (.pi hu hv (.ref domain) body)
      locals σ profile footprint)
    (resources : footprint.Available available) :
    Nonempty (RichComputationalValue headerEnv env U registry target (.pi hu hv (.ref domain) body)
      locals σ τ available profile) := by
  apply query.replayComputationalPi henv hscoped formed (domain := .ref domain) (body := body) ?_
    hu hv (.done _) resources
  intro n ambient relevant prototypeDomain prototypeBody table domainFootprint rowFootprint domainCode guard rows
    domainAvailable rowAvailable
  exact frame.nativePiComputationalStep henv hscoped headerBelow hf initialContext domain location lineage
    body bodyLocation bodyLineage hu hv domainF bodyF closed formed substitutions
    domainCode domainAvailable guard rows rowAvailable

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
