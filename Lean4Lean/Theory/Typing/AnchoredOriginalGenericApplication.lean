import Lean4Lean.Theory.Typing.AnchoredOriginalGenericApplicationStep
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichFrameDiagonal

/-! The full paired computational application rule. Both original children
are called at the actual paired frame. Left support reconstruction uses the
checked diagonal rule; diagonalization preserves the original closure cost. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem OriginalRichFrame.applicationComputational
    {root : EndpointRef headerEnv U rootSource rootExpression rootType}
    (initialContext : ContextDerivation headerEnv U rootSource)
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (hf : headerEnv.Ordered)
    (domain : EndpointRef headerEnv U headerSource A (.sort u))
    (body : EndpointState headerEnv U (A :: headerSource) B (.sort v))
    (function : EndpointState headerEnv U headerSource f (.forallE A B))
    (argument : EndpointState headerEnv U headerSource a A)
    (result : EndpointState headerEnv U headerSource (B.inst a) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (location : Located root (.app hu hv (.ref domain) body function argument result))
    (frame : OriginalRichFrame headerEnv env U registry target
      (location.contextDerivation initialContext) locals σ τ available)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ headerSource)
    (functionQuery : RichObs headerEnv env U registry target function locals σ
      (Profile.fn (key : Key n) output) functionFootprint)
    (argumentQuery : RichObs headerEnv env U registry target argument locals σ rawInput argumentFootprint)
    (arguments : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ))
    (resources : (functionFootprint ++ argumentFootprint).Available available)
    (functionF : OriginalComputationalInductionAt env registry hf initialContext (.appFunction location)
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin hf)
        (frame.dependencyEnvironment hf)).cost)
    (argumentF : OriginalComputationalInductionAt env registry hf initialContext (.appArgument location)
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin hf)
        (frame.dependencyEnvironment hf)).cost)
    (domainF : OriginalCodeInductionAt env registry hf initialContext (.appDomain location)
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin hf)
        (frame.dependencyEnvironment hf)).cost)
    (bodyF : OriginalCodeInductionAt env registry hf initialContext (.appCodomain location)
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
        locals locals σ σ available available)
    (resultR : ∀ {q : Profile n} (capture : GenericApplicationCapture frame.leftDiagonal domain body argument q),
      richSchedule .expressionReindex
        ((Closure.close (result.dependencyOrigin hf) (frame.dependencyEnvironment hf)).cost +
         (Closure.close (body.dependencyOrigin hf) (capture.frame.dependencyEnvironment hf)).cost) <
      richSchedule .fundamental
        (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin hf)
          (frame.dependencyEnvironment hf)).cost →
      Nonempty (RichCodeTransferResult env U registry target body result locals
        (σ.cons (a.subst σ)) σ available true q)) :
    Nonempty (RichComputationalValue headerEnv env U registry target
      (.app hu hv (.ref domain) body function argument result) locals σ τ available (.singleton output)) := by
  have reserve := application_cost_le_captured (domain.dependencyOrigin hf) (body.dependencyOrigin hf)
    (function.dependencyOrigin hf) (argument.dependencyOrigin hf) (result.dependencyOrigin hf)
    (frame.dependencyEnvironment hf)
  have functionResources := fun index need member => resources index need (List.mem_append_left _ member)
  have argumentResources := fun index need member => resources index need (List.mem_append_right _ member)
  obtain ⟨functionAnswer⟩ := functionF target locals σ τ available frame
    (Nat.lt_of_lt_of_le (binder_other_cost (by simp) _) reserve)
    closed formed substitutions functionQuery functionResources
  obtain ⟨argumentAnswer⟩ := argumentF target locals σ τ available frame
    (Nat.lt_of_lt_of_le (binder_other_cost (by simp) _) reserve)
    closed formed substitutions argumentQuery argumentResources
  let leftFunction : RichBinderValue headerEnv env U registry target function locals σ σ available
      (Profile.fn key output) := { functionAnswer.toRichBinderValue with related := functionAnswer.related.left_diagonal }
  let leftArgument : RichBinderValue headerEnv env U registry target argument locals σ σ available rawInput :=
    { argumentAnswer.toRichBinderValue with related := argumentAnswer.related.left_diagonal }
  have domainF' := domainF
  have bodyF' := bodyF
  have typeR' := typeR
  rw [← frame.dependencyEnvironment_leftDiagonal hf] at domainF' bodyF' typeR'
  have bodyContext : (Located.appCodomain location).contextDerivation initialContext =
      .cons (location.contextDerivation initialContext) domain := by
    change ContextDerivation.cons (location.contextDerivation initialContext) (Classical.choose location.originalDomains.1) = _
    exact congrArg (ContextDerivation.cons (location.contextDerivation initialContext))
      (EndpointState.ref.inj (Classical.choose_spec location.originalDomains.1).symm)
  obtain ⟨outputSupport, ⟨row⟩, outputTyped⟩ := frame.leftDiagonal.applicationFunctionRowGeneric
    initialContext henv hscoped headerBelow hf domain (.appDomain location) body function argument result hu hv
    (.appCodomain location) bodyContext closed formed substitutions.left leftFunction admitted domainF' bodyF' typeR'
  obtain ⟨leftAnswer⟩ := frame.leftDiagonal.applicationRowGeneric
    initialContext henv hscoped hf headerBelow formed closed domain body function argument result hu hv
    location substitutions.left row outputTyped leftFunction leftArgument argumentQuery argumentResources
    arguments admitted domainF'
    (by
      intro needs bodyClosed bodyFrame smaller bodySubstitutions
      intro relevant rank profile footprint query queryAvailable
      unfold OriginalCodeInductionAt at bodyF'
      rw [bodyContext] at bodyF'
      apply bodyF' target (Locals.push locals) (σ.cons key.anchor) (σ.cons (a.subst σ))
        (available.push needs) bodyFrame _ bodyClosed formed bodySubstitutions query queryAvailable
      simp only [richSchedule, RichPhase.code] at smaller
      omega)
    (fun capture smaller => resultR capture (by
      simpa only [OriginalRichFrame.dependencyEnvironment_leftDiagonal] using smaller))
  exact RichComputationalValue.apply henv hscoped formed closed (.ref domain) body result hu hv leftAnswer
    functionAnswer argumentAnswer arguments
    ((argument.sound.defeq.mono headerBelow).substDF henv substitutions.wf formed substitutions) admitted

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
