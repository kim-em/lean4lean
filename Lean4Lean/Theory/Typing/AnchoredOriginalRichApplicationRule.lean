import Lean4Lean.Theory.Typing.AnchoredOriginalRichValueInduction
import Lean4Lean.Theory.Typing.AnchoredOriginalRichApplicationRows
import Lean4Lean.Theory.Typing.AnchoredOriginalRichApplicationStep

/-! The actual rich application F rule. Its value children, Pi row reanchoring,
function-formation reindexing, and captured-result reindexing are fixed original
induction calls, each passed its checked bound at the actual rich frame. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

variable {header : EndpointRef headerEnv U [] headerExpression headerType}
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  {major : EndpointRef sourceEnv U source majorExpression majorType}


theorem HeaderBinderFrame.applicationStep
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
    (functionQuery : RichObs headerEnv env U registry target function locals σ
      (Profile.fn (key : Key n) output) functionFootprint)
    (argumentQuery : RichObs headerEnv env U registry target argument locals σ rawInput argumentFootprint)
    (arguments : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ))
    (resources : (functionFootprint ++ argumentFootprint).Available available)
    (functionF : HeaderValueInductionAt header field major env registry hf sf initial context function
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin hf)
        (frame.dependencyEnvironment hf sf initial)).cost)
    (argumentF : HeaderValueInductionAt header field major env registry hf sf initial context argument
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin hf)
        (frame.dependencyEnvironment hf sf initial)).cost)
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
        locals locals σ σ available available)
    (resultR : ∀ {q : Profile n} (capture : HeaderApplicationCapture frame domain body argument q),
      richSchedule .expressionReindex
        ((Closure.close (result.dependencyOrigin hf) (frame.dependencyEnvironment hf sf initial)).cost +
         (Closure.close (body.dependencyOrigin hf) (capture.dependencyEnvironment hf sf initial)).cost) <
      richSchedule .fundamental
        (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin hf)
          (frame.dependencyEnvironment hf sf initial)).cost →
      Nonempty (RichCodeTransferResult env U registry target body result locals
        (σ.cons (a.subst σ)) σ available true q)) :
    Nonempty (RichSupportedValue headerEnv env U registry target
      (.app hu hv (.ref domain) body function argument result) locals σ σ available (.singleton output)) := by
  have reserve := application_cost_le_captured (domain.dependencyOrigin hf) (body.dependencyOrigin hf)
    (function.dependencyOrigin hf) (argument.dependencyOrigin hf) (result.dependencyOrigin hf)
    (frame.dependencyEnvironment hf sf initial)
  have functionResources := fun index need member => resources index need (List.mem_append_left _ member)
  have argumentResources := fun index need member => resources index need (List.mem_append_right _ member)
  obtain ⟨functionAnswer⟩ := functionF target locals σ σ available frame
    (Nat.lt_of_lt_of_le (binder_other_cost (by simp) _) reserve)
    closed formed substitutions functionQuery functionResources
  obtain ⟨argumentAnswer⟩ := argumentF target locals σ σ available frame
    (Nat.lt_of_lt_of_le (binder_other_cost (by simp) _) reserve)
    closed formed substitutions argumentQuery argumentResources
  obtain ⟨outputSupport, ⟨row⟩, outputTyped⟩ := frame.applicationFunctionRowStep henv hscoped headerBelow hf sf initial
    domain location lineage body function argument result hu hv closed formed substitutions
    functionAnswer.toRichBinderValue admitted domainF bodyF typeR
  apply frame.applicationRowStep henv hscoped hf sf headerBelow formed closed substitutions domain location lineage
    body function argument result hu hv initial row outputTyped functionAnswer.toRichBinderValue
    argumentAnswer.toRichBinderValue argumentQuery argumentResources arguments admitted domainF
  · intro needs bodyClosed bodyFrame smaller bodySubstitutions
    intro relevant rank profile footprint query queryAvailable
    apply bodyF target (Locals.push locals) (σ.cons key.anchor) (σ.cons (a.subst σ)) (available.push needs)
      bodyFrame _ bodyClosed formed bodySubstitutions query queryAvailable
    simp only [richSchedule, RichPhase.code] at smaller
    omega
  · exact resultR

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
