import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyArgumentPair
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiDomainAlignment
import Lean4Lean.Theory.Typing.AnchoredOriginalRichTypeFormationMeasure

/-! Align an actual family-spine argument with an earlier declaration
domain. The source argument keeps its inferred type. Its actual formation is
first reindexed at the application's own domain occurrence; an exact Pi
domain query then follows the retained function/header comparison. -/
namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false

theorem EndpointState.application_argument_type_reindex_schedule
    (ordered : sourceEnv.Ordered) (hu : u.WF U) (hv : v.WF U)
    (domain : EndpointState sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (function : EndpointState sourceEnv U source f (.forallE A B))
    (argument : EndpointState sourceEnv U source a A)
    (result : EndpointState sourceEnv U source (B.inst a) (.sort v)) (captured : List Closure) :
    richSchedule .expressionReindex
      ((Closure.close (argument.typeFormation.node.dependencyOrigin ordered) captured).cost +
       (Closure.close (domain.dependencyOrigin ordered) captured).cost) <
    richSchedule .fundamental
      (Closure.close ((EndpointState.app hu hv domain body function argument result).dependencyOrigin ordered) captured).cost := by
  apply richSchedule_strict
  apply Nat.lt_of_le_of_lt (Nat.add_le_add_right (argument.typeFormation_dependency_cost_le ordered captured) _)
  apply Nat.lt_of_lt_of_le _ (application_cost_le_captured
    (domain.dependencyOrigin ordered) (body.dependencyOrigin ordered) (function.dependencyOrigin ordered)
    (argument.dependencyOrigin ordered) (result.dependencyOrigin ordered) captured)
  change ((argument.dependencyOrigin ordered).weight * (1 + environmentCost captured)) +
    ((domain.dependencyOrigin ordered).weight * (1 + environmentCost captured)) < _
  rw [← Nat.add_mul]
  apply Nat.mul_lt_mul_of_pos_right _ (by omega)
  simp only [applicationOrigin, Origin.weight, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]
  have positive := (result.dependencyOrigin ordered).weight_pos
  omega

end Lean4Lean.AnchoredSource.OriginalClosureMeasure

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- This owner is the actual second occurrence in the major's assigned
family formation, with its enclosing original application still available. -/
noncomputable def _root_.Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.SpineApplication.headerOwner
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (application : SpineApplication major source [] argument) : HeaderOwner field major :=
  .inr ⟨source, argument, application.view.domainExpression, application.view.argument,
    application.argument.location⟩

theorem _root_.Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.SpineApplication.alignHeaderDomainExact
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (application : SpineApplication major source [] argument)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered)
    (initialContext : ContextDerivation sourceEnv U source)
    (frame : OriginalRichFrame sourceEnv env U registry target
      (application.argument.location.contextDerivation initialContext) locals σ τ available)
    (domain : EndpointRef headerEnv U headerSource C (.sort u'))
    (body : EndpointState headerEnv U (C :: headerSource) D (.sort v'))
    (hu : u'.WF U) (hv : v'.WF U)
    {header : EndpointState headerEnv U headerSource (.forallE C D) (.sort headerLevel)}
    (headerRoute : PrefixRoute headerEnv U headerSource (.forallE C D)
      header (.pi hu hv (.ref domain) body))
    (value : RichBinderValue sourceEnv env U registry target application.view.argument
      locals σ τ available (input : Profile n))
    (argumentFormationR : richSchedule .expressionReindex
        ((Closure.close (application.view.argument.typeFormation.node.dependencyOrigin ordered)
          (frame.dependencyEnvironment ordered)).cost +
         (Closure.close (application.view.domain.dependencyOrigin ordered)
          (frame.dependencyEnvironment ordered)).cost) <
      richSchedule .fundamental
        (Closure.close ((EndpointState.app application.view.domainWF application.view.bodyWF
          application.view.domain application.view.codomain application.view.function application.view.argument
          application.view.result).dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost →
      RichCodeTransfer env U registry target application.view.argument.typeFormation.node application.view.domain
        locals locals σ σ available available)
    (functionHeader : RichCodeTransfer env U registry target
      (.pi application.view.domainWF application.view.bodyWF application.view.domain application.view.codomain)
      header locals headerLocals σ declaredLeft available headerAvailable) :
    ∃ answer : HeaderValueAlignment (application.headerOwner (field := field)) domain env registry target
      locals headerLocals σ τ declaredLeft available headerAvailable input, answer.value = value := by
  obtain ⟨natural⟩ := argumentFormationR
    (EndpointState.application_argument_type_reindex_schedule ordered
      application.view.domainWF application.view.bodyWF application.view.domain application.view.codomain
      application.view.function application.view.argument application.view.result (frame.dependencyEnvironment ordered))
    value.certificate value.resources
  obtain ⟨declared, path⟩ := functionHeader.piDomainAlignment henv hscoped formed
    application.view.domainWF application.view.bodyWF hu hv (.done _) headerRoute
    natural.certificate natural.resources
  exact ⟨{
    value := value
    aligned := {
      footprint := declared.footprint
      certificate := declared.certificate
      resources := declared.resources
      related := natural.related.trans henv declared.related }
    path := path }, rfl⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
