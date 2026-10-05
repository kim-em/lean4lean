import Lean4Lean.Theory.Typing.AnchoredOriginalRichApplicationRule
import Lean4Lean.Theory.Typing.AnchoredOriginalRichApplicationSeeding

/-! Full computational wrapper interpretation at an actual structural
application. Each demanded atom comes from its retained original application
query; finite output paths replay all support/code/action and grade changes.
The only semantic recursion is the checked original application rule. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- Whole original function/argument queries are recovered at the caller's
actual structural application, before any original child F is invoked. -/
theorem RichAppOrigin.originalQueriesAt {A B f a : VExpr} {u v : VLevel}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {function : EndpointState sourceEnv U source f (.forallE A B)}
    {argument : EndpointState sourceEnv U source a A}
    {result : EndpointState sourceEnv U source (B.inst a) (.sort v)}
    (hu : u.WF U) (hv : v.WF U)
    (origin : RichAppOrigin root env registry target source locals σ f a)
    (rooted : origin.RootedAt (.app hu hv domain body function argument result)) :
    Nonempty (RichObs sourceEnv env U registry target function locals σ
      (Profile.fn origin.key origin.output) origin.functionFootprint) ∧
    Nonempty (RichObs sourceEnv env U registry target argument locals σ
      origin.rawInput origin.argumentFootprint) := by
  obtain ⟨route⟩ := rooted
  have equal := route.structural_unique (by trivial) (.done _) (by trivial)
  cases origin with
  | mk A' B' u' v' hu' hv' domain' codomain' functionNode argumentNode result' location rank key output
      functionFootprint argumentFootprint functionQuery rawInput argumentQuery arguments admitted =>
    simp only [RichAppOrigin.node] at equal
    obtain ⟨_, _, _, domainEq, _, bodyEq, _, _, _, _, _, functionEq, argumentEq, _⟩ :=
      EndpointState.app.hinj rfl rfl rfl rfl equal.1 equal.2
    cases domainEq
    cases bodyEq
    have functionEq := eq_of_heq functionEq
    have argumentEq := eq_of_heq argumentEq
    cases functionEq
    cases argumentEq
    exact ⟨⟨functionQuery⟩, ⟨argumentQuery⟩⟩

variable {header : EndpointRef headerEnv U [] headerExpression headerType}
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  {major : EndpointRef sourceEnv U source majorExpression majorType}

theorem HeaderBinderFrame.applicationInterpret
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
    (resultR : ∀ {n : Nat} {q : Profile n} (capture : HeaderApplicationCapture frame domain body argument q),
      richSchedule .expressionReindex
        ((Closure.close (result.dependencyOrigin hf) (frame.dependencyEnvironment hf sf initial)).cost +
         (Closure.close (body.dependencyOrigin hf) (capture.dependencyEnvironment hf sf initial)).cost) <
      richSchedule .fundamental
        (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin hf)
          (frame.dependencyEnvironment hf sf initial)).cost →
      Nonempty (RichCodeTransferResult env U registry target body result locals
        (σ.cons (a.subst σ)) σ available true q))
    {profile : Profile n}
    (query : RichObs headerEnv env U registry target (.app hu hv (.ref domain) body function argument result)
      locals σ profile footprint)
    (appLocation : Located header (.app hu hv (.ref domain) body function argument result))
    (resources : footprint.Available available) :
    Nonempty (RichSupportedValue headerEnv env U registry target
      (.app hu hv (.ref domain) body function argument result) locals σ σ available profile) := by
  have each : ∀ atom ∈ profile.atoms,
      Nonempty (RichSupportedValue headerEnv env U registry target
        (.app hu hv (.ref domain) body function argument result) locals σ σ available (.singleton atom)) := by
    intro atom member
    obtain ⟨origin, ⟨path⟩, included, rooted⟩ := query.applicationOriginRooted appLocation member
    obtain ⟨⟨fnQuery⟩, ⟨argQuery⟩⟩ := origin.originalQueriesAt hu hv rooted
    obtain ⟨answer⟩ := frame.applicationStep henv hscoped headerBelow hf sf initial domain location lineage body
      function argument result hu hv closed formed substitutions fnQuery argQuery origin.arguments origin.admitted
      (fun i need member => resources i need (included member)) functionF argumentF domainF bodyF typeR resultR
    exact answer.outputPath henv hscoped formed path
  suffices collect : ∀ atoms : List (Atom n),
      (∀ atom ∈ atoms, Nonempty (RichSupportedValue headerEnv env U registry target
        (.app hu hv (.ref domain) body function argument result) locals σ σ available (.singleton atom))) →
      Nonempty (RichSupportedValue headerEnv env U registry target
        (.app hu hv (.ref domain) body function argument result) locals σ σ available (.mk atoms)) from
    collect profile.atoms each
  intro atoms
  induction atoms with
  | nil => intro _; exact ⟨.empty⟩
  | cons atom rest ih =>
    intro each
    obtain ⟨head⟩ := each atom List.mem_cons_self
    obtain ⟨tail⟩ := ih (fun next member => each next (List.mem_cons_of_mem _ member))
    exact ⟨head.union henv tail⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
