import Lean4Lean.Theory.Typing.AnchoredOriginalGenericApplication

/-! All application query wrappers retain both paired value semantics and
actual right source output. The body/code induction channel is consequently
a checked projection of the same computational answer. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem OriginalRichFrame.applicationComputationalInterpret
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
    (appLocation : Located root (.app hu hv (.ref domain) body function argument result))
    (frame : OriginalRichFrame headerEnv env U registry target
      (appLocation.contextDerivation initialContext) locals σ τ available)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ headerSource)
    (functionF : OriginalComputationalInductionAt env registry hf initialContext (.appFunction appLocation)
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin hf)
        (frame.dependencyEnvironment hf)).cost)
    (argumentF : OriginalComputationalInductionAt env registry hf initialContext (.appArgument appLocation)
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin hf)
        (frame.dependencyEnvironment hf)).cost)
    (domainF : OriginalCodeInductionAt env registry hf initialContext (.appDomain appLocation)
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin hf)
        (frame.dependencyEnvironment hf)).cost)
    (bodyF : OriginalCodeInductionAt env registry hf initialContext (.appCodomain appLocation)
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
    (resultR : ∀ {n : Nat} {q : Profile n} (capture : GenericApplicationCapture frame.leftDiagonal domain body argument q),
      richSchedule .expressionReindex
        ((Closure.close (result.dependencyOrigin hf) (frame.dependencyEnvironment hf)).cost +
         (Closure.close (body.dependencyOrigin hf) (capture.frame.dependencyEnvironment hf)).cost) <
      richSchedule .fundamental
        (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin hf)
          (frame.dependencyEnvironment hf)).cost →
      Nonempty (RichCodeTransferResult env U registry target body result locals
        (σ.cons (a.subst σ)) σ available true q))
    {profile : Profile n}
    (query : RichObs headerEnv env U registry target (.app hu hv (.ref domain) body function argument result)
      locals σ profile footprint)
    (resources : footprint.Available available) :
    Nonempty (RichComputationalValue headerEnv env U registry target
      (.app hu hv (.ref domain) body function argument result) locals σ τ available profile) := by
  have each : ∀ atom ∈ profile.atoms,
      Nonempty (RichComputationalValue headerEnv env U registry target
        (.app hu hv (.ref domain) body function argument result) locals σ τ available (.singleton atom)) := by
    intro atom member
    obtain ⟨origin, ⟨path⟩, included, rooted⟩ := query.applicationOriginRooted appLocation member
    obtain ⟨⟨fnQuery⟩, ⟨argQuery⟩⟩ := origin.originalQueriesAt hu hv rooted
    obtain ⟨answer⟩ := frame.applicationComputational initialContext henv hscoped headerBelow hf domain body
      function argument result hu hv appLocation closed formed substitutions fnQuery argQuery origin.arguments origin.admitted
      (fun i need member => resources i need (included member)) functionF argumentF domainF bodyF typeR resultR
    exact answer.outputPath henv hscoped formed path
  suffices collect : ∀ atoms : List (Atom n),
      (∀ atom ∈ atoms, Nonempty (RichComputationalValue headerEnv env U registry target
        (.app hu hv (.ref domain) body function argument result) locals σ τ available (.singleton atom))) →
      Nonempty (RichComputationalValue headerEnv env U registry target
        (.app hu hv (.ref domain) body function argument result) locals σ τ available (.mk atoms)) from
    collect profile.atoms each
  intro atoms
  induction atoms with
  | nil => intro _; exact ⟨.empty⟩
  | cons atom rest ih =>
    intro each
    obtain ⟨head⟩ := each atom List.mem_cons_self
    obtain ⟨tail⟩ := ih (fun next member => each next (List.mem_cons_of_mem _ member))
    exact ⟨head.union henv hscoped formed tail⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
