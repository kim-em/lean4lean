import Lean4Lean.Theory.Typing.AnchoredOriginalGenericPiReanchor
import Lean4Lean.Theory.Typing.AnchoredOriginalRichTypeFormationMeasure
import Lean4Lean.Theory.Typing.AnchoredOriginalRichVariableValue

/-! The function answer is aligned with the application's own Pi formation
before rows are extracted. Both endpoints display the same source Pi under
the same actual frame, so this call requires no target-only equality premise
and never relabels the returned function's original type certificate. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem OriginalRichFrame.applicationFunctionRowGeneric
    {root : EndpointRef headerEnv U rootSource rootExpression rootType}
    (initialContext : ContextDerivation headerEnv U rootSource)
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (hf : headerEnv.Ordered)
    (domain : EndpointRef headerEnv U headerSource A (.sort u))
    (location : Located root (.ref domain))
    (body : EndpointState headerEnv U (A :: headerSource) B (.sort v))
    (function : EndpointState headerEnv U headerSource f (.forallE A B))
    (argument : EndpointState headerEnv U headerSource a A)
    (result : EndpointState headerEnv U headerSource (B.inst a) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (bodyLocation : Located root body)
    (bodyContext : bodyLocation.contextDerivation initialContext =
      .cons (location.contextDerivation initialContext) domain)
    (frame : OriginalRichFrame headerEnv env U registry target (location.contextDerivation initialContext) locals σ σ available)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ headerSource)
    (functionAnswer : RichBinderValue headerEnv env U registry target function locals σ σ available
      (Profile.fn (key : Key n) output))
    (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ))
    (domainF : OriginalCodeInductionAt env registry hf initialContext location
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin hf)
        (frame.dependencyEnvironment hf)).cost)
    (bodyF : OriginalCodeInductionAt env registry hf initialContext bodyLocation
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin hf)
        (frame.dependencyEnvironment hf)).cost)
    (typeR : richSchedule .expressionReindex
        ((Closure.close (function.typeFormation.node.dependencyOrigin hf)
          (frame.dependencyEnvironment hf)).cost +
         (Closure.close ((EndpointState.pi hu hv (.ref domain) body).dependencyOrigin hf)
          (frame.dependencyEnvironment hf)).cost) <
      richSchedule .fundamental
        (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin hf)
          (frame.dependencyEnvironment hf)).cost →
      RichCodeTransfer env U registry target function.typeFormation.node (.pi hu hv (.ref domain) body)
        locals locals σ σ available available) :
    ∃ outputSupport,
      Nonempty (RichPiRowCertificate env U registry target locals σ available true (.ref domain) body key outputSupport) ∧
      (Profile.singleton output).HasType outputSupport := by
  obtain ⟨aligned⟩ := typeR
    (EndpointState.application_function_type_reindex_schedule hf hu hv (.ref domain) body function argument result
      (frame.dependencyEnvironment hf)) functionAnswer.certificate functionAnswer.resources
  have piBound :
      (Closure.close (.binder (domain.dependencyOrigin hf) [body.dependencyOrigin hf] [])
        (frame.dependencyEnvironment hf)).cost ≤
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin hf)
        (frame.dependencyEnvironment hf)).cost := by
    apply Nat.le_trans _ (application_cost_le_captured
      (domain.dependencyOrigin hf) (body.dependencyOrigin hf) (function.dependencyOrigin hf)
      (argument.dependencyOrigin hf) (result.dependencyOrigin hf) (frame.dependencyEnvironment hf))
    apply Nat.mul_le_mul_right
    simp only [applicationOrigin, Origin.weight, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    omega
  have anchor : Admitted env U registry target key key.anchor key.anchor := by
    obtain ⟨rawAnchor, _, support, typed, supportFormed, code, toArgument, _⟩ := admitted
    exact ⟨rawAnchor.hasType.1, rawAnchor.hasType.1, support, typed,
      supportFormed, code, Related.left_diagonal toArgument, Related.left_diagonal toArgument⟩
  exact aligned.certificate.piRowGeneric initialContext henv hscoped headerBelow hf domain location body hu hv
    bodyLocation bodyContext domainF bodyF frame piBound closed formed substitutions (.done _) aligned.resources functionAnswer.typed aligned.related anchor

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
