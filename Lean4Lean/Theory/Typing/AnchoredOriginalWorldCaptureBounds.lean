import Lean4Lean.Theory.Typing.AnchoredOriginalWorldGenerationFramePack
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedQueryBounds
import Lean4Lean.Theory.Typing.AnchoredOriginalCappedApplicationCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFrameHeadDepth

/-! The own-capture producer stores the exact certificate returned by the
bounded domain call. Both its world annotation and its masked fuel bound
refer to that same selected frame, without inferring fuel from capacity. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private raw_capture_comp from Lean4Lean.Theory.Typing.AnchoredOriginalCappedApplicationCapture
open private castFrameSubstitutions from Lean4Lean.Theory.Typing.AnchoredOriginalCappedApplicationCapture
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

private def world_castFrameSubstitutions
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : WorldGenerated strata P base caps left right graph frame.raw controls)
    (hl : σ = σ') (hr : τ = τ') :
    WorldGenerated strata P base caps left right graph (castFrameSubstitutions frame hl hr).raw controls := by
  cases hl; cases hr; exact generated

private theorem world_castFrameSubstitutions_retainedQueries
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : WorldGenerated strata P base caps left right graph frame.raw controls)
    (hl : σ = σ') (hr : τ = τ') :
    (world_castFrameSubstitutions generated hl hr).retainedQueries = generated.retainedQueries := by
  cases hl; cases hr; rfl

private theorem world_castFrameSubstitutions_worlds
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : WorldGenerated strata P base caps left right graph frame.raw controls)
    (hl : σ = σ') (hr : τ = τ') :
    (world_castFrameSubstitutions generated hl hr).worlds = generated.worlds := by
  cases hl; cases hr; rfl

private theorem world_castFrameSubstitutions_framePack
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : WorldGenerated strata P base caps left right graph frame.raw controls)
    (hl : σ = σ') (hr : τ = τ') :
    (world_castFrameSubstitutions generated hl hr).framePack = generated.framePack := by
  cases hl; cases hr; rfl

/-- Same-witness own-capture construction under one caller's cutoff and fuel.
This does not fund heterogeneous borrowed owners: their original controls and
query-owned sponsors must be retained separately by a stronger call contract. -/
theorem generatedOwnCaptureWorldReplyAt
    {base : OriginalCaptureBase env U registry target}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (argument : EndpointState sourceEnv U source a A)
    (location : Located root argument)
    {graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw}
    (realized : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (generated : WorldGenerated strata P base commonCaps commonLeft commonRight graph realized.frame.raw controls)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (realized.frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (variableNode : EndpointState sourceEnv U (A :: source) (.bvar 0) assigned)
    (variableProvenance : EndpointProvenance (.cons (location.contextDerivation initial) domain) variableNode)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (query : RichObs sourceEnv env U registry target argument locals (raw.comp commonLeft) (profile : Profile n) footprint)
    (resources : footprint.Available available)
    (answer : RichComputationalValue sourceEnv env U registry target argument locals
      (raw.comp commonLeft) (raw.comp commonRight) available profile)
    (aligned : RichCodeTransferResult env U registry target argument.typeFormation.node (.ref domain) locals
      (raw.comp commonLeft) (raw.comp commonLeft) available true answer.support) :
    ∃ reply : CappedGeneratedQueryReply base commonCaps
      (applicationCaptureVariableDisplay graph domain argument (.ofLocation location initial)
        variableNode variableProvenance) commonLeft commonRight profile,
      ∃ generatedReply : WorldGenerated strata P base commonCaps commonLeft commonRight
        (applicationCaptureVariableDisplay graph domain argument (.ofLocation location initial)
          variableNode variableProvenance).graph reply.reply.realization.frame.raw controls,
      generatedReply.retainedQueries =
        .observation query :: .certificate aligned.certificate :: generated.retainedQueries ∧
      generatedReply.worlds =
        (reservedCaptureWorldEnvironment controls domain argument baseline generated.environment).worlds ∧
      ∃ annotation : WorldObsProvenance strata reply.reply.query.observation,
        annotation.worlds = [] ∧ (∀ policy, reply.reply.query.observation.headDepth policy = 0) ∧
        reply.reply.query.rank = n ∧ HEq reply.reply.query.raw profile ∧
        reply.reply.query.footprint = [(0, Need.mk n profile)] ∧
        generatedReply.framePack = (WorldGenerated.capture generated baseline capacity domain initial argument location rfl
          query resources (Nat.le_refl _) (by rw [raiseProfile_self]; exact .refl _)
          aligned.certificate aligned.resources answer.typed
          (answer.related.convert henv answer.typed aligned.related) (captureNeeds profile)
          (fun need member => (captureNeeds_covered profile need member).1)
          (fun need member => (captureNeeds_covered profile need member).2)).framePack := by
  have related := answer.related.convert henv answer.typed aligned.related
  let activeFrame := realized.frame.capture domain initial argument location rfl query resources
    aligned.certificate aligned.resources answer.typed related (captureNeeds profile)
    (fun need member => (captureNeeds_covered profile need member).1)
    (fun need member => (captureNeeds_covered profile need member).2)
  let reserve := [Closure.bundle
    (.close (argument.dependencyOrigin controls.ordered) baselineEnvironment)
    (.close (domain.dependencyOrigin controls.ordered) baselineEnvironment)]
  let frame := activeFrame.reserve reserve
  let nextGenerated : WorldGenerated strata P base commonCaps commonLeft commonRight
      (.capture graph domain graph argument (.ofLocation location initial)) frame.raw controls :=
    .capture generated baseline capacity domain initial argument location rfl query resources
      (Nat.le_refl _) (by rw [raiseProfile_self]; exact .refl _) aligned.certificate aligned.resources answer.typed related (captureNeeds profile)
      (fun need member => (captureNeeds_covered profile need member).1)
      (fun need member => (captureNeeds_covered profile need member).2)
  have rawPair := (argument.sound.defeq.mono below).substDF henv realized.substitutions.wf formed realized.substitutions
  have nextSubstitutions : Ctx.SubstEq env U target
      ((raw.comp commonLeft).cons (a.subst (raw.comp commonLeft)))
      ((raw.comp commonRight).cons (a.subst (raw.comp commonRight))) (A :: source) := Ctx.SubstEq.cons realized.substitutions (domain.sound.defeq.mono below) rawPair
  let captureGraph := OriginalCaptureMap.capture graph domain graph argument (.ofLocation location initial)
  let captureRealization : OriginalCaptureRealization captureGraph env registry target (Locals.push locals)
      commonLeft commonRight (available.push (captureNeeds profile)) := {
    frame := castFrameSubstitutions frame (raw_capture_comp raw commonLeft a).symm
      (raw_capture_comp raw commonRight a).symm
    substitutions := by simpa only [raw_capture_comp] using nextSubstitutions }
  let generatedNext : WorldGenerated strata P base commonCaps commonLeft commonRight captureGraph captureRealization.frame.raw controls := by
    exact world_castFrameSubstitutions nextGenerated _ _
  refine ⟨⟨{
    locals := Locals.push locals, available := available.push (captureNeeds profile),
    realization := captureRealization, generated := generatedNext.erase.capped.generated,
    query := ?_, closed := Valuation.push_atomized_closed closed [⟨n, profile⟩] }, generatedNext.erase.capped⟩, generatedNext, ?_, ?_, ?_⟩
  · refine {
      rank := n, bound := Nat.le_refl _, raw := profile, footprint := [(0, Need.mk n profile)]
      observation := .legacy (.legacy (.var _ _ 0 profile))
      adapter := by rw [raiseProfile_self]; exact .refl _
      resources := ?_, live := answer.related.live henv hscoped formed }
    intro i need member
    cases List.mem_singleton.mp member
    exact List.mem_append_left _ (List.mem_singleton_self _)
  · change generatedNext.retainedQueries = _
    simp only [generatedNext, world_castFrameSubstitutions_retainedQueries]
    rfl
  · change generatedNext.worlds = _
    simp only [generatedNext, world_castFrameSubstitutions_worlds]
    rfl
  · refine ⟨.var, rfl, ?_, rfl, HEq.rfl, rfl, ?_⟩
    · intro policy
      simp only [RichObs.headDepth, SortableObs.headDepth, Obs.headDepth]
    · exact world_castFrameSubstitutions_framePack nextGenerated _ _

theorem generatedOwnCaptureWorldBounded
    {base : OriginalCaptureBase env U registry target}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (argument : EndpointState sourceEnv U source a A)
    (location : Located root argument)
    {graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw}
    (realized : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (generated : WorldGenerated strata P base commonCaps commonLeft commonRight graph realized.frame.raw controls)
    (variableNode : EndpointState sourceEnv U (A :: source) (.bvar 0) assigned)
    (variableProvenance : EndpointProvenance (.cons (location.contextDerivation initial) domain) variableNode)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (query : RichObs sourceEnv env U registry target argument locals (raw.comp commonLeft) (profile : Profile n) footprint)
    (resources : footprint.Available available)
    (queryBound : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => query.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (tailBound : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => generated.retainedDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (argumentF :
      (Closure.close (argument.dependencyOrigin controls.ordered) (realized.frame.dependencyEnvironment controls.ordered)).cost <
        (Closure.close (variableNode.dependencyOrigin controls.ordered)
        (Closure.bundle (.close (argument.dependencyOrigin controls.ordered) (realized.frame.dependencyEnvironment controls.ordered))
          (.close (domain.dependencyOrigin controls.ordered) (realized.frame.dependencyEnvironment controls.ordered)) ::
          realized.frame.dependencyEnvironment controls.ordered)).cost →
      ∀ incoming : RichObs sourceEnv env U registry target argument locals (raw.comp commonLeft) profile footprint,
      footprint.Available available →
      EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
        (fun control => incoming.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)) →
      ∃ answer : RichComputationalValue sourceEnv env U registry target argument locals
          (raw.comp commonLeft) (raw.comp commonRight) available profile,
        EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => answer.certificate.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (domainR :
      richSchedule .expressionReindex
        ((Closure.close (argument.typeFormation.node.dependencyOrigin controls.ordered) (realized.frame.dependencyEnvironment controls.ordered)).cost +
         (Closure.close (domain.dependencyOrigin controls.ordered) (realized.frame.dependencyEnvironment controls.ordered)).cost) <
      richSchedule .fundamental (Closure.close (variableNode.dependencyOrigin controls.ordered)
        (Closure.bundle (.close (argument.dependencyOrigin controls.ordered) (realized.frame.dependencyEnvironment controls.ordered))
          (.close (domain.dependencyOrigin controls.ordered) (realized.frame.dependencyEnvironment controls.ordered)) ::
          realized.frame.dependencyEnvironment controls.ordered)).cost →
      ∀ {q : Profile n} {fp}
        (certificate : RichCert sourceEnv env U registry target argument.typeFormation.node locals
          (raw.comp commonLeft) true q fp),
      fp.Available available →
      EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => certificate.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)) →
      ∃ aligned : RichCodeTransferResult env U registry target argument.typeFormation.node (.ref domain) locals
          (raw.comp commonLeft) (raw.comp commonLeft) available true q,
        EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => aligned.certificate.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control))) :
    ∃ reply : CappedGeneratedQueryReply base commonCaps
      (applicationCaptureVariableDisplay graph domain argument (.ofLocation location initial)
        variableNode variableProvenance) commonLeft commonRight profile,
      ∃ generatedReply : WorldGenerated strata P base commonCaps commonLeft commonRight
        (applicationCaptureVariableDisplay graph domain argument (.ofLocation location initial)
          variableNode variableProvenance).graph reply.reply.realization.frame.raw controls,
      EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => generatedReply.retainedDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)) := by
  have bundleBound := capturedVariable_bundle_lt (variableNode.dependencyOrigin controls.ordered)
    (argument.dependencyOrigin controls.ordered) (domain.dependencyOrigin controls.ordered) (realized.frame.dependencyEnvironment controls.ordered)
  have argumentBound := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) bundleBound
  obtain ⟨answer, answerBound⟩ := argumentF argumentBound query resources queryBound
  obtain ⟨aligned, alignedBound⟩ := domainR
    (richSchedule_strict (Nat.lt_of_le_of_lt
      (Nat.add_le_add_right (argument.typeFormation_dependency_cost_le controls.ordered (realized.frame.dependencyEnvironment controls.ordered)) _) bundleBound) _ _)
    answer.certificate answer.resources answerBound
  obtain ⟨reply, generatedReply, retained, _, _⟩ := generatedOwnCaptureWorldReplyAt
    initial henv hscoped below controls domain argument location realized generated generated.environment (Nat.le_refl _)
    variableNode variableProvenance closed formed query resources answer aligned
  refine ⟨reply, generatedReply, ?_⟩
  intro control active
  change generatedReply.retainedDepth
    (stratifiedHeadPolicy (strata.headOrdinal registry) control) ≤ controls.fuel control
  rw [← generatedReply.retainedQueries_depth, retained]
  simp only [StoredOriginalQuery.maximumDepth_cons, StoredOriginalQuery.headDepth,
    generated.retainedQueries_depth]
  exact Nat.max_le.mpr ⟨queryBound control active,
    Nat.max_le.mpr ⟨alignedBound control active, tailBound control active⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
