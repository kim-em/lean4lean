import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientCapturedArgumentSupply
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedApplicationArguments

/-! The actual result query selects its captured codomain frame and all
original argument owners under the honest ambient-qualified lower bank. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option Elab.async false

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
theorem emptyAmbientApplicationBodyFrame
    {base : OriginalCaptureBase env U registry target}
    (henv : env.Ordered) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (realized : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (capped : AmbientCaptureGenerated base commonCaps commonLeft commonRight graph realized.frame.raw) :
    ∃ next : OriginalCaptureRealization
        (applicationBodyDisplay initial domain body function argument result hu hv location graph).graph
        env registry target (Locals.push locals) commonLeft commonRight (available.push []),
      AmbientCaptureGenerated base commonCaps commonLeft commonRight
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
  have nextCapped : AmbientCaptureGenerated base commonCaps commonLeft commonRight
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

/-- Only the actual result and body original occurrences are compared.
The selected reply retains positive generation for subsequent owner lookup. -/
theorem generatedAmbientApplicationBody
    {base : OriginalCaptureBase env U registry target}
    (henv : env.Ordered) (ordered : sourceEnv.Ordered)
    (formed : OnCtx target (env.IsType U))
    (realized : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (generated : AmbientCaptureGenerated base commonCaps commonLeft commonRight graph realized.frame.raw)
    (closed : available.AtomClosed)
    (bank : OriginalLowerCallBank env U registry limit)
    (budget : richSchedule .fundamental
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin ordered)
        (realized.frame.dependencyEnvironment ordered)).cost ≤ limit)
    (certificate : RichCert sourceEnv env U registry target result locals (raw.comp commonLeft)
      relevant (profile : Profile n) footprint)
    (resources : footprint.Available available) :
    Nonempty (AmbientBoundedGeneratedQueryReply base commonCaps
      (applicationBodyDisplay initial domain body function argument result hu hv location graph)
      commonLeft commonRight profile
      (environmentCost
        (Closure.bundle (.close (argument.dependencyOrigin ordered) (realized.frame.dependencyEnvironment ordered))
          (.close (domain.dependencyOrigin ordered) (realized.frame.dependencyEnvironment ordered)) ::
          realized.frame.dependencyEnvironment ordered))) := by
  obtain ⟨next, nextGenerated, environment⟩ := emptyAmbientApplicationBodyFrame initial domain body function argument result hu hv
    location graph henv generated.ambient.1.below formed realized generated
  have nextClosed : (available.push []).AtomClosed := by
    simpa only [List.flatMap_nil, List.nil_append] using Valuation.push_atomized_closed closed []
  have scheduled : richSchedule .expressionReindex
      ((Closure.close (result.dependencyOrigin ordered) (realized.frame.dependencyEnvironment ordered)).cost +
       (Closure.close (body.dependencyOrigin ordered) (next.frame.dependencyEnvironment ordered)).cost) < limit := by
    rw [environment ordered]
    exact Nat.lt_of_lt_of_le (richSchedule_strict (capturedApplication_comparison (domain.dependencyOrigin ordered)
      (body.dependencyOrigin ordered) (function.dependencyOrigin ordered) (argument.dependencyOrigin ordered)
      (result.dependencyOrigin ordered) (realized.frame.dependencyEnvironment ordered)) _ _) budget
  obtain ⟨answer⟩ := bank.observation base commonCaps
    (applicationResultDisplay initial domain body function argument result hu hv location graph)
    (applicationBodyDisplay initial domain body function argument result hu hv location graph)
    commonLeft commonRight ordered ordered realized generated closed next nextGenerated nextClosed scheduled
    (.code certificate) resources
  rw [environment ordered] at answer
  exact ⟨answer⟩

end

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
  (frame : OriginalRichFrame sourceEnv env U registry target (location.contextDerivation initial) locals σ τ available)
  (substitutions : Ctx.SubstEq env U target σ τ source)
  (ordered : sourceEnv.Ordered)

structure AmbientApplicationBackwardQueries (relevant : Bool) (profile : Profile n)
    extends ApplicationBackwardQueries initial domain body function argument result hu hv location frame substitutions ordered relevant profile where
  generation : AmbientCaptureGenerated (frame.captureBase substitutions) (frame.captureBase substitutions).initialCaps σ τ
    (applicationBodyDisplay initial domain body function argument result hu hv location (.identity _)).graph
    reply.answer.reply.realization.frame.raw
  queriesGenerated : queries.AmbientGenerated

/-- Result-to-body R and every selected owner R are supplied directly by the
bounded original bank; no completed argument ledger or alignment is input. -/
theorem generatedAmbientApplicationArguments
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (ambient : frame.Ambient)
    (bank : OriginalLowerCallBank env U registry limit)
    (budget : applicationReplayLimit initial domain body function argument result hu hv location frame ordered ≤ limit)
    (certificate : RichCert sourceEnv env U registry target result locals σ relevant (profile : Profile n) footprint)
    (resources : footprint.Available available) :
    ∃ packet : AmbientApplicationBackwardQueries initial domain body function argument result hu hv location frame substitutions ordered relevant profile,
      Nonempty (RichArgumentSupply sourceEnv env U registry target argument locals σ available packet.footprint.localNeeds) := by
  let base := frame.captureBase substitutions
  obtain ⟨reply⟩ := generatedAmbientApplicationBody initial domain body function argument result hu hv location (.identity _)
    henv ordered formed base.identityRealization (.identity ambient) closed bank budget certificate resources
  obtain ⟨bodyFootprint, ⟨bodyCode⟩, bodyResources⟩ := reply.answer.reply.query.code henv certificate.formed
  have used : ∀ need ∈ bodyFootprint.localNeeds, need ∈ reply.answer.reply.available 0 :=
    fun need member => bodyResources 0 need (Footprint.mem_localNeeds.mp member)
  have queriesExist : ∃ queries : CapturedArgumentQueries base base.initialCaps source σ τ a
      (applicationCaptureCapacity initial domain body function argument result hu hv location frame ordered)
      bodyFootprint.localNeeds, queries.AmbientGenerated := by
    have found := reply.generation.argumentQueries reply.answer.reply.realization.frame.valid
      reply.answer.reply.realization.substitutions ordered bodyFootprint.localNeeds used (reply.bounded ordered)
    rw [subst_id] at found
    exact found
  obtain ⟨queries, queriesGenerated⟩ := queriesExist
  let packet : AmbientApplicationBackwardQueries initial domain body function argument result hu hv location frame substitutions ordered relevant profile :=
    ⟨⟨reply.toBoundedGeneratedQueryReply, bodyFootprint, bodyCode, bodyResources, queries⟩, reply.generation, queriesGenerated⟩
  refine ⟨packet, ?_⟩
  apply queries.supplyAtAmbientBase (.ofLocation (.appArgument location) initial) henv hscoped formed ordered closed ambient queriesGenerated ?_ bank
  intro nonempty
  obtain ⟨need, member⟩ := List.exists_mem_of_ne_nil _ nonempty
  exact Nat.lt_of_lt_of_le (application_capture_cost_replay_schedule ordered domain body function argument result hu hv
    bodyCode (Footprint.mem_localNeeds.mp member) (frame.dependencyEnvironment ordered)
    (applicationCaptureCapacity initial domain body function argument result hu hv location frame ordered) (Nat.le_refl _)) budget

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
