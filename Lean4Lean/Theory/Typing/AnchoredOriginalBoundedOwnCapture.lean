import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedApplicationCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalBoundedGeneratedReply
import Lean4Lean.Theory.Typing.AnchoredOriginalCappedCaptureRealization
import Lean4Lean.Theory.Typing.AnchoredOriginalParameterCaptureStep

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- The declared-domain reindex chooses its actual destination resources.
The old argument query and the returned domain certificate are retained in
separate branches of a merged tail. Both branches have the original tail's
capacity, so the actual argument/domain bundle cannot grow. -/
theorem boundedGeneratedOwnCapture
    {base : OriginalCaptureBase env U registry target}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (ordered : sourceEnv.Ordered)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (argument : EndpointState sourceEnv U source a A)
    (location : Located root argument)
    {graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw}
    (realized : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (capped : CappedCaptureGenerated base commonCaps commonLeft commonRight graph realized.frame.raw)
    (variableNode : EndpointState sourceEnv U (A :: source) (.bvar 0) assigned)
    (variableProvenance : EndpointProvenance (.cons (location.contextDerivation initial) domain) variableNode)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (argumentF : OriginalComputationalInductionAt env registry ordered initial location
      (Closure.close (variableNode.dependencyOrigin ordered)
        (Closure.bundle (.close (argument.dependencyOrigin ordered) (realized.frame.dependencyEnvironment ordered))
          (.close (domain.dependencyOrigin ordered) (realized.frame.dependencyEnvironment ordered)) ::
          realized.frame.dependencyEnvironment ordered)).cost)
    (domainR : richSchedule .expressionReindex
        ((Closure.close (argument.typeFormation.node.dependencyOrigin ordered) (realized.frame.dependencyEnvironment ordered)).cost +
         (Closure.close (domain.dependencyOrigin ordered) (realized.frame.dependencyEnvironment ordered)).cost) <
      richSchedule .fundamental
        (Closure.close (variableNode.dependencyOrigin ordered)
        (Closure.bundle (.close (argument.dependencyOrigin ordered) (realized.frame.dependencyEnvironment ordered))
          (.close (domain.dependencyOrigin ordered) (realized.frame.dependencyEnvironment ordered)) ::
          realized.frame.dependencyEnvironment ordered)).cost →
      ∀ {n : Nat} {support : Profile n} {footprint : Footprint},
        RichCert sourceEnv env U registry target argument.typeFormation.node locals (raw.comp commonLeft)
          true support footprint → footprint.Available available →
        Nonempty (BoundedGeneratedQueryReply base commonCaps
          (graph.parameterCellDisplay domain (.ofLocation .here (location.contextDerivation initial)))
          commonLeft commonRight support (environmentCost (realized.frame.dependencyEnvironment ordered))))
    (query : RichObs sourceEnv env U registry target argument locals (raw.comp commonLeft) (profile : Profile n) footprint)
    (resources : footprint.Available available) :
    Nonempty (BoundedGeneratedQueryReply base commonCaps
      (applicationCaptureVariableDisplay graph domain argument (.ofLocation location initial)
        variableNode variableProvenance) commonLeft commonRight profile
      (environmentCost (Closure.bundle
        (.close (argument.dependencyOrigin ordered) (realized.frame.dependencyEnvironment ordered))
        (.close (domain.dependencyOrigin ordered) (realized.frame.dependencyEnvironment ordered)) ::
        realized.frame.dependencyEnvironment ordered))) := by
  have bundleBound := capturedVariable_bundle_lt (variableNode.dependencyOrigin ordered)
    (argument.dependencyOrigin ordered) (domain.dependencyOrigin ordered) (realized.frame.dependencyEnvironment ordered)
  obtain ⟨value⟩ := argumentF target locals _ _ available realized.frame
    (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) bundleBound) closed formed realized.substitutions query resources
  obtain ⟨domainReply⟩ := domainR
    (richSchedule_strict (Nat.lt_of_le_of_lt
      (Nat.add_le_add_right (argument.typeFormation_dependency_cost_le ordered (realized.frame.dependencyEnvironment ordered)) _) bundleBound) _ _)
    value.certificate value.resources
  rcases domainReply with ⟨⟨⟨nextLocals, nextAvailable, nextFrame, nextGenerated,
    nextQuery, nextClosed⟩, nextCapped⟩, nextBound⟩
  have localsEq : locals = nextLocals := capped.generated.locals_eq.trans nextGenerated.locals_eq.symm
  cases localsEq
  obtain ⟨codeFootprint, ⟨certificate⟩, codeResources⟩ := nextQuery.code henv value.certificate.formed
  let combined := realized.frame.merge nextFrame.frame
  let combinedAvailable := available.append nextAvailable
  have firstIncluded : ∀ index need, need ∈ available index → need ∈ combinedAvailable index :=
    fun _ _ member => List.mem_append_left _ member
  have secondIncluded : ∀ index need, need ∈ nextAvailable index → need ∈ combinedAvailable index :=
    fun _ _ member => List.mem_append_right _ member
  have queryAvailable : footprint.Available combinedAvailable :=
    fun index need member => firstIncluded index need (resources index need member)
  have certificateAvailable : codeFootprint.Available combinedAvailable :=
    fun index need member => secondIncluded index need (codeResources index need member)
  have combinedClosed : combinedAvailable.AtomClosed := by
    intro index need member selected present
    rcases List.mem_append.mp member with member | member
    · exact List.mem_append_left _ (closed index need member selected present)
    · exact List.mem_append_right _ (nextClosed index need member selected present)
  let frame := combined.capture domain initial argument location rfl query queryAvailable
    certificate certificateAvailable value.typed value.related (captureNeeds profile)
    (fun need member => (captureNeeds_covered profile need member).1)
    (fun need member => (captureNeeds_covered profile need member).2)
  have generated : CappedCaptureGenerated base commonCaps commonLeft commonRight
      (.capture graph domain graph argument (.ofLocation location initial)) frame.raw :=
    .capture (.merge capped nextCapped) domain initial argument location rfl query queryAvailable
      (Nat.le_refl _) (by rw [raiseProfile_self]; exact .refl _) certificate certificateAvailable value.typed value.related (captureNeeds profile)
      (fun need member => (captureNeeds_covered profile need member).1)
      (fun need member => (captureNeeds_covered profile need member).2)
  have rawPair := (argument.sound.defeq.mono below).substDF henv realized.substitutions.wf formed realized.substitutions
  have substitutions : Ctx.SubstEq env U target
      ((raw.comp commonLeft).cons (a.subst (raw.comp commonLeft)))
      ((raw.comp commonRight).cons (a.subst (raw.comp commonRight))) (A :: source) :=
    .cons realized.substitutions (domain.sound.defeq.mono below) rawPair
  obtain ⟨output, outputCapped, environmentEq⟩ := generated.realize frame substitutions
  refine ⟨⟨⟨{
    locals := Locals.push locals
    available := combinedAvailable.push (captureNeeds profile)
    realization := output
    generated := outputCapped.generated
    query := ?_
    closed := Valuation.push_atomized_closed combinedClosed [⟨n, profile⟩] }, outputCapped⟩, ?_⟩⟩
  · refine {
      rank := n, bound := Nat.le_refl _, raw := profile, footprint := [(0, Need.mk n profile)]
      observation := .legacy (.legacy (.var _ _ 0 profile))
      adapter := by rw [raiseProfile_self]; exact .refl _
      resources := ?_, live := value.related.live henv hscoped formed }
    intro index need member
    cases List.mem_singleton.mp member
    exact List.mem_append_left _ (List.mem_singleton_self _)
  · intro actualOrdered
    rw [environmentEq]
    have tailBound : environmentCost (combined.dependencyEnvironment actualOrdered) ≤
        environmentCost (realized.frame.dependencyEnvironment ordered) := by
      rw [OriginalRichFrame.merge_environmentCost]
      exact Nat.max_le.mpr ⟨Nat.le_refl _, nextBound actualOrdered⟩
    change max ((Closure.close (argument.dependencyOrigin actualOrdered) (combined.dependencyEnvironment actualOrdered)).cost +
        (Closure.close (domain.dependencyOrigin actualOrdered) (combined.dependencyEnvironment actualOrdered)).cost)
      (environmentCost (combined.dependencyEnvironment actualOrdered)) ≤ _
    apply Nat.max_le.mpr
    constructor
    · exact Nat.le_trans (Nat.add_le_add
        (Nat.mul_le_mul_left _ (Nat.add_le_add_left tailBound 1))
        (Nat.mul_le_mul_left _ (Nat.add_le_add_left tailBound 1))) (Nat.le_max_left _ _)
    · exact Nat.le_trans tailBound (Nat.le_max_right _ _)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
