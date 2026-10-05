import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationTypeRouteSide
import Lean4Lean.Theory.Typing.AnchoredOriginalCappedApplicationCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedNativePiReindex

/-! Backwards replay starts at the actual original application result. The
codomain is captured with the application's own original argument, before
any demand or semantic alignment has been supplied. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

section
variable
  {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
  (initial : ContextDerivation sourceEnv U rootSource)
  (domain : EndpointRef sourceEnv U source A (.sort u))
  (body : EndpointState sourceEnv U (A :: source) B (.sort v))
  (function : EndpointState sourceEnv U source f (.forallE A B))
  (argument : EndpointState sourceEnv U source a A)
  (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
  (hu : u.WF U) (hv : v.WF U)
  (location : Located root (.app hu hv (.ref domain) body function argument result))
  (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)

/-- The empty starting frame retains the genuine argument closure and its
own domain. It uses no value query, domain comparison, or semantic IH. -/
theorem emptyApplicationBodyFrame
    {base : OriginalCaptureBase env U registry target}
    (henv : env.Ordered) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (realized : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (capped : CappedCaptureGenerated base commonCaps commonLeft commonRight graph realized.frame.raw) :
    ∃ next : OriginalCaptureRealization
        (applicationBodyDisplay initial domain body function argument result hu hv location graph).graph
        env registry target (Locals.push locals) commonLeft commonRight (available.push []),
      CappedCaptureGenerated base commonCaps commonLeft commonRight
        (applicationBodyDisplay initial domain body function argument result hu hv location graph).graph next.frame.raw ∧
      ∀ ordered : sourceEnv.Ordered,
        next.frame.dependencyEnvironment ordered =
          Closure.bundle (.close (argument.dependencyOrigin ordered) (realized.frame.dependencyEnvironment ordered))
            (.close (domain.dependencyOrigin ordered) (realized.frame.dependencyEnvironment ordered)) ::
          realized.frame.dependencyEnvironment ordered := by
  let query : RichObs sourceEnv env U registry target argument locals (raw.comp commonLeft)
      (.empty : Profile 0) [] := .legacy (.legacy .empty)
  let certificate : RichCert sourceEnv env U registry target (.ref domain) locals (raw.comp commonLeft)
      true (.empty : Profile 0) [] :=
    .legacy (.seed .empty (Profile.HasType.empty (Profile.WF.sort true)))
  have resources : Footprint.Available [] available := fun _ _ h => nomatch h
  have typed : (.empty : Profile 0).HasType .empty := Profile.HasType.empty Profile.WF.empty
  have arguments : Related env U registry target (a.subst (raw.comp commonLeft))
      (a.subst (raw.comp commonRight)) (A.subst (raw.comp commonLeft)) (.empty : Profile 0) .empty :=
    Related.of_singletons (fun _ h => nomatch h)
  let frame := realized.frame.capture domain initial argument (.appArgument location) rfl
    query resources certificate resources typed arguments [] (fun _ h => nomatch h) (fun _ h => nomatch h)
  have nextCapped : CappedCaptureGenerated base commonCaps commonLeft commonRight
      (applicationBodyDisplay initial domain body function argument result hu hv location graph).graph frame.raw :=
    .capture capped domain initial argument (.appArgument location) rfl query resources
      (Nat.le_refl _) (by rw [raiseProfile_self]; exact .refl _) certificate resources
      typed arguments [] (fun _ h => nomatch h) (fun _ h => nomatch h)
  have rawPair := (argument.sound.defeq.mono below).substDF henv realized.substitutions.wf formed realized.substitutions
  have substitutions : Ctx.SubstEq env U target
      ((raw.comp commonLeft).cons (a.subst (raw.comp commonLeft)))
      ((raw.comp commonRight).cons (a.subst (raw.comp commonRight))) (A :: source) :=
    .cons realized.substitutions (domain.sound.defeq.mono below) rawPair
  obtain ⟨next, generated, environment⟩ := nextCapped.realize frame substitutions
  exact ⟨next, generated, environment⟩

/-- An actual result-type query determines the finite prior demands in its
own captured codomain. The call consumes two original children and its
strict bound includes the retained original argument closure. -/
theorem generatedApplicationBody
    {base : OriginalCaptureBase env U registry target}
    (henv : env.Ordered) (below : sourceEnv ≤ env) (ordered : sourceEnv.Ordered)
    (formed : OnCtx target (env.IsType U))
    (realized : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (capped : CappedCaptureGenerated base commonCaps commonLeft commonRight graph realized.frame.raw)
    (closed : available.AtomClosed)
    (bodyR : GeneratedObservationCall base commonCaps
      (applicationResultDisplay initial domain body function argument result hu hv location graph)
      (applicationBodyDisplay initial domain body function argument result hu hv location graph)
      commonLeft commonRight ordered ordered
      (richSchedule .fundamental
        (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin ordered)
          (realized.frame.dependencyEnvironment ordered)).cost))
    (certificate : RichCert sourceEnv env U registry target result locals (raw.comp commonLeft)
      relevant (profile : Profile n) footprint)
    (resources : footprint.Available available) :
    Nonempty (BoundedGeneratedQueryReply base commonCaps
      (applicationBodyDisplay initial domain body function argument result hu hv location graph)
      commonLeft commonRight profile
      (environmentCost
        (Closure.bundle (.close (argument.dependencyOrigin ordered) (realized.frame.dependencyEnvironment ordered))
          (.close (domain.dependencyOrigin ordered) (realized.frame.dependencyEnvironment ordered)) ::
          realized.frame.dependencyEnvironment ordered))) := by
  obtain ⟨next, generated, environment⟩ := emptyApplicationBodyFrame initial domain body function argument result hu hv
    location graph henv below formed realized capped
  have nextClosed : (available.push []).AtomClosed := by
    simpa only [List.flatMap_nil, List.nil_append] using Valuation.push_atomized_closed closed []
  have scheduled : richSchedule .expressionReindex
      ((Closure.close (result.dependencyOrigin ordered) (realized.frame.dependencyEnvironment ordered)).cost +
       (Closure.close (body.dependencyOrigin ordered) (next.frame.dependencyEnvironment ordered)).cost) <
      richSchedule .fundamental
        (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin ordered)
          (realized.frame.dependencyEnvironment ordered)).cost := by
    rw [environment ordered]
    exact richSchedule_strict (capturedApplication_comparison (domain.dependencyOrigin ordered)
      (body.dependencyOrigin ordered) (function.dependencyOrigin ordered) (argument.dependencyOrigin ordered)
      (result.dependencyOrigin ordered) (realized.frame.dependencyEnvironment ordered)) _ _
  obtain ⟨answer⟩ := bodyR realized capped closed next generated nextClosed scheduled (.code certificate) resources
  rw [environment ordered] at answer
  exact ⟨answer⟩

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
