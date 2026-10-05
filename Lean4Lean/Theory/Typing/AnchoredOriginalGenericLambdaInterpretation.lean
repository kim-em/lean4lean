import Lean4Lean.Theory.Typing.AnchoredOriginalGenericLambda
import Lean4Lean.Theory.Typing.AnchoredOriginalRichLambdaComputationalReplay

/-! The complete paired lambda case handles every legacy and rich query
wrapper, using only the original domain/body/codomain calls and their fixed
same-expression formation comparison. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
variable {root : EndpointRef sourceEnv U rootSource rootExpression rootType}

theorem OriginalRichFrame.lambdaComputationalInterpret
    {context : ContextDerivation sourceEnv U source}
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (ordered : sourceEnv.Ordered) (initialContext : ContextDerivation sourceEnv U rootSource)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (codomain : EndpointState sourceEnv U (A :: source) B (.sort v))
    (body : EndpointState sourceEnv U (A :: source) b B)
    (hu : u.WF U) (hv : v.WF U)
    (location : Located root (.lam hu hv (.ref domain) codomain body))
    (lineage : location.contextDerivation initialContext = context)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (domainF : OriginalCodeInductionAt env registry ordered initialContext (.lamDomain location)
      (Closure.close ((EndpointState.lam hu hv (.ref domain) codomain body).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost)
    (codomainF : OriginalCodeInductionAt env registry ordered initialContext (.lamCodomain location)
      (Closure.close ((EndpointState.lam hu hv (.ref domain) codomain body).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost)
    (bodyF : OriginalComputationalInductionAt env registry ordered initialContext (.lamBody location)
      (Closure.close ((EndpointState.lam hu hv (.ref domain) codomain body).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost)
    (codomainR : LambdaCodomainInductionAt env registry ordered context domain codomain body
      (Closure.close ((EndpointState.lam hu hv (.ref domain) codomain body).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    {profile : Profile n}
    (query : RichObs sourceEnv env U registry target (.lam hu hv (.ref domain) codomain body)
      locals σ profile footprint)
    (resources : footprint.Available available) :
    Nonempty (RichComputationalValue sourceEnv env U registry target
      (.lam hu hv (.ref domain) codomain body) locals σ τ available profile) := by
  apply query.replayComputationalLambda henv hscoped formed (domain := .ref domain)
    (codomain := codomain) (body := body) ?_ hu hv (.done _) resources
  intro n ambient key output domainFootprint bodyFootprint outside packed domainCode guard observation
    pack covered domainAvailable outsideAvailable
  exact frame.nativeLambdaComputationalStep henv hscoped sourceBelow ordered initialContext domain codomain body
    hu hv location lineage domainF codomainF bodyF codomainR closed formed substitutions
    domainCode domainAvailable guard observation pack covered outsideAvailable

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
