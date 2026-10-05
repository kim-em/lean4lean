import Lean4Lean.Theory.Typing.AnchoredOriginalRichPrefixMeasure
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiDomainAlignment
import Lean4Lean.Theory.Typing.AnchoredOriginalRichTypeFormationMeasure
import Lean4Lean.Theory.Typing.AnchoredOriginalPiPrefix

/-! Seed a function's actual assigned Pi formation from the application's
separately retained domain occurrence. The empty-row query is built only
after a strictly smaller same-source original-domain reindex call. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

 theorem AppView.exposedDomain_schedule
    (ordered : sourceEnv.Ordered)
    {node : EndpointState sourceEnv U source (.app f a) assigned}
    {start : Located root node} (app : ApplicationPrefix start)
    (pi : PiPrefix (Located.assignedFormation (Located.appFunction app.view.location)))
    (captured : List Closure) :
    richSchedule .expressionReindex
      ((Closure.close (app.view.domain.dependencyOrigin ordered) captured).cost +
       (Closure.close (pi.view.domain.dependencyOrigin ordered) captured).cost) <
    richSchedule .fundamental (Closure.close (node.dependencyOrigin ordered) captured).cost := by
  have reserve := EndpointState.application_function_type_reindex_schedule ordered
    app.view.domainWF app.view.bodyWF app.view.domain app.view.codomain app.view.function
    app.view.argument app.view.result captured
  have parent := app.route.dependency_cost_le ordered captured
  have exposed := pi.route.dependency_cost_le ordered captured
  have selected := binder_domain_cost (pi.view.domain.dependencyOrigin ordered)
    [pi.view.body.dependencyOrigin ordered] [] captured
  have original := binder_domain_cost (app.view.domain.dependencyOrigin ordered)
    [app.view.codomain.dependencyOrigin ordered] [] captured
  simp only [richSchedule, RichPhase.code, EndpointState.dependencyOrigin] at *
  omega

/-- The result is an actual rich Pi certificate at the function's computed
formation endpoint, retaining all original domain children and footprints. -/
theorem AppView.seedFunctionPi
    (ordered : sourceEnv.Ordered)
    {node : EndpointState sourceEnv U source (.app f a) assigned}
    {start : Located root node} (app : ApplicationPrefix start)
    (pi : PiPrefix (Located.assignedFormation (Located.appFunction app.view.location)))
    (captured : List Closure)
    (certificate : RichCert sourceEnv env U registry target app.view.domain locals σ true
      (support : Profile n) footprint)
    (resources : footprint.Available available)
    (domainR : richSchedule .expressionReindex
      ((Closure.close (app.view.domain.dependencyOrigin ordered) captured).cost +
       (Closure.close (pi.view.domain.dependencyOrigin ordered) captured).cost) <
      richSchedule .fundamental (Closure.close (node.dependencyOrigin ordered) captured).cost →
      RichCodeTransfer env U registry target app.view.domain pi.view.domain
        locals locals σ σ available available) :
    ∃ outputFootprint,
      Nonempty (RichCert sourceEnv env U registry target app.view.function.typeFormation.node locals σ true
        (Profile.pi (app.view.domainExpression.subst σ) (app.view.codomainExpression.subst σ.lift) support [])
        outputFootprint) ∧ outputFootprint.Available available := by
  obtain ⟨domain⟩ := domainR (AppView.exposedDomain_schedule ordered app pi captured) certificate resources
  exact ⟨domain.footprint, ⟨.route pi.route
    (domain.certificate.domainOnly pi.view.body pi.view.domainWF pi.view.bodyWF)⟩, domain.resources⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
