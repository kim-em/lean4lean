import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiReanchor
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

variable {header : EndpointRef headerEnv U [] headerExpression headerType}
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  {major : EndpointRef sourceEnv U source majorExpression majorType}

theorem HeaderBinderFrame.applicationFunctionRowStep
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (hf : headerEnv.Ordered) (sf : sourceEnv.Ordered) (initial : List Closure)
    (domain : EndpointRef headerEnv U headerSource A (.sort u))
    (location : Located header (.ref domain)) (lineage : location.contextDerivation .nil = context)
    (body : EndpointState headerEnv U (A :: headerSource) B (.sort v))
    (function : EndpointState headerEnv U headerSource f (.forallE A B))
    (argument : EndpointState headerEnv U headerSource a A)
    (result : EndpointState headerEnv U headerSource (B.inst a) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (frame : HeaderBinderFrame header field major env registry target context locals σ σ available)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ headerSource)
    (functionAnswer : RichBinderValue headerEnv env U registry target function locals σ σ available
      (Profile.fn (key : Key n) output))
    (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ))
    (domainF : HeaderCodeInductionAt header field major env registry hf sf initial context (.ref domain)
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin hf)
        (frame.dependencyEnvironment hf sf initial)).cost)
    (bodyF : HeaderCodeInductionAt header field major env registry hf sf initial (.cons context domain) body
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin hf)
        (frame.dependencyEnvironment hf sf initial)).cost)
    (typeR : richSchedule .expressionReindex
        ((Closure.close (function.typeFormation.node.dependencyOrigin hf)
          (frame.dependencyEnvironment hf sf initial)).cost +
         (Closure.close ((EndpointState.pi hu hv (.ref domain) body).dependencyOrigin hf)
          (frame.dependencyEnvironment hf sf initial)).cost) <
      richSchedule .fundamental
        (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin hf)
          (frame.dependencyEnvironment hf sf initial)).cost →
      RichCodeTransfer env U registry target function.typeFormation.node (.pi hu hv (.ref domain) body)
        locals locals σ σ available available) :
    ∃ outputSupport,
      Nonempty (RichPiRowCertificate env U registry target locals σ available true (.ref domain) body key outputSupport) ∧
      (Profile.singleton output).HasType outputSupport := by
  obtain ⟨aligned⟩ := typeR
    (EndpointState.application_function_type_reindex_schedule hf hu hv (.ref domain) body function argument result
      (frame.dependencyEnvironment hf sf initial)) functionAnswer.certificate functionAnswer.resources
  have piBound :
      (Closure.close (.binder (domain.dependencyOrigin hf) [body.dependencyOrigin hf] [])
        (frame.dependencyEnvironment hf sf initial)).cost ≤
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin hf)
        (frame.dependencyEnvironment hf sf initial)).cost := by
    apply Nat.le_trans _ (application_cost_le_captured
      (domain.dependencyOrigin hf) (body.dependencyOrigin hf) (function.dependencyOrigin hf)
      (argument.dependencyOrigin hf) (result.dependencyOrigin hf) (frame.dependencyEnvironment hf sf initial))
    apply Nat.mul_le_mul_right
    simp only [applicationOrigin, Origin.weight, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    omega
  have anchor : Admitted env U registry target key key.anchor key.anchor := by
    obtain ⟨rawAnchor, _, support, typed, supportFormed, code, toArgument, _⟩ := admitted
    exact ⟨rawAnchor.hasType.1, rawAnchor.hasType.1, support, typed,
      supportFormed, code, Related.left_diagonal toArgument, Related.left_diagonal toArgument⟩
  exact aligned.certificate.piRowStep henv hscoped headerBelow hf sf initial domain location lineage body hu hv
    domainF bodyF frame piBound closed formed substitutions (.done _) aligned.resources functionAnswer.typed aligned.related anchor

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
