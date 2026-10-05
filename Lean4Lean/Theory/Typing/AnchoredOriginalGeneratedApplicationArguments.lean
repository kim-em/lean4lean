import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationPackingData
import Lean4Lean.Theory.Typing.AnchoredOriginalCapturedArgumentSupply

/-! Backwards application replay computes the body query and the complete
finite argument-call ledger. All owner queries originate in the returned
captured frame; no argument observation supplier is assumed. -/
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
  (frame : OriginalRichFrame sourceEnv env U registry target (location.contextDerivation initial) locals σ τ available)
  (substitutions : Ctx.SubstEq env U target σ τ source)
  (ordered : sourceEnv.Ordered)

/-- Both stages are actual producers: original result-to-body R selects the
body's frame, and its precise footprint selects each original owner query.
The consumer accepts only the resulting finite, strictly smaller R ledger. -/
theorem generatedApplicationArguments
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (bodyR : GeneratedObservationCall (frame.captureBase substitutions) (frame.captureBase substitutions).initialCaps
      (applicationResultDisplay initial domain body function argument result hu hv location (.identity _))
      (applicationBodyDisplay initial domain body function argument result hu hv location (.identity _))
      σ τ ordered ordered
      (applicationReplayLimit initial domain body function argument result hu hv location frame ordered))
    (certificate : RichCert sourceEnv env U registry target result locals σ relevant (profile : Profile n) footprint)
    (resources : footprint.Available available) :
    ∃ packet : ApplicationBackwardQueries initial domain body function argument result hu hv location frame substitutions ordered relevant profile,
      packet.queries.Calls
        (OriginalNestedDisplay.identity (frame.captureBase substitutions) argument (.ofLocation (.appArgument location) initial))
        ordered (applicationReplayLimit initial domain body function argument result hu hv location frame ordered) →
      Nonempty (RichArgumentSupply sourceEnv env U registry target argument locals σ available packet.footprint.localNeeds) := by
  let base := frame.captureBase substitutions
  obtain ⟨reply⟩ := generatedApplicationBody initial domain body function argument result hu hv location (.identity _)
    henv below ordered formed base.identityRealization base.identityCapped closed bodyR certificate resources
  obtain ⟨bodyFootprint, ⟨bodyCode⟩, bodyResources⟩ := reply.answer.reply.query.code henv certificate.formed
  have used : ∀ need ∈ bodyFootprint.localNeeds, need ∈ reply.answer.reply.available 0 :=
    fun need member => bodyResources 0 need (Footprint.mem_localNeeds.mp member)
  obtain ⟨queries⟩ := reply.answer.capped.argumentQueries reply.answer.reply.realization.frame.valid
    reply.answer.reply.realization.substitutions ordered bodyFootprint.localNeeds used (reply.bounded ordered)
  simp only [subst_id] at queries
  let packet : ApplicationBackwardQueries initial domain body function argument result hu hv location frame substitutions ordered relevant profile :=
    ⟨reply, bodyFootprint, bodyCode, bodyResources, queries⟩
  refine ⟨packet, ?_⟩
  intro calls
  apply queries.supplyAtBase (.ofLocation (.appArgument location) initial) henv hscoped formed ordered closed _ calls
  intro nonempty
  have selected : ∃ need, need ∈ bodyFootprint.localNeeds := List.exists_mem_of_ne_nil _ nonempty
  obtain ⟨need, member⟩ := selected
  exact application_capture_cost_replay_schedule ordered domain body function argument result hu hv
    bodyCode (Footprint.mem_localNeeds.mp member) (frame.dependencyEnvironment ordered)
    (applicationCaptureCapacity initial domain body function argument result hu hv location frame ordered) (Nat.le_refl _)

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
