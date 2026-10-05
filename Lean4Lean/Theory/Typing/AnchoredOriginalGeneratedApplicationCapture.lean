import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedCaptureReindex
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyArgumentAlignment

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

private theorem raw_capture_comp (raw common : Subst) (a : VExpr) :
    (raw.cons (a.subst raw)).comp common = (raw.comp common).cons (a.subst (raw.comp common)) := by
  funext index
  cases index with
  | zero => exact subst_subst
  | succ index => rfl

private def castFrameSubstitutions
    {context : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (left : σ = σ') (right : τ = τ') :
    OriginalRichFrame sourceEnv env U registry target context locals σ' τ' available :=
  left ▸ right ▸ frame

private theorem generated_castFrameSubstitutions
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : ScopedCaptureGenerated base commonLeft commonRight graph frame.raw)
    (left : σ = σ') (right : τ = τ') :
    ScopedCaptureGenerated base commonLeft commonRight graph (castFrameSubstitutions frame left right).raw := by
  cases left
  cases right
  exact generated

/-- The destination is the actual original variableNode occurrence under the
application's own captured argument. It is not a synthesized typing of that
argument at a declaration-header type. -/
def applicationCaptureVariableDisplay
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (argument : EndpointState sourceEnv U source a A)
    (argumentProvenance : EndpointProvenance context argument)
    (variableNode : EndpointState sourceEnv U (A :: source) (.bvar 0) assigned)
    (variableProvenance : EndpointProvenance (.cons context domain) variableNode) :
    OriginalNestedDisplay U common (a.subst raw) (assigned.subst (raw.cons (a.subst raw))) := {
  sourceEnv := sourceEnv, source := A :: source, sourceExpression := .bvar 0, sourceType := assigned
  context := .cons context domain, node := variableNode, provenance := variableProvenance
  raw := raw.cons (a.subst raw)
  graph := .capture graph domain graph argument argumentProvenance
  expression_eq := rfl, type_eq := rfl }

/-- An arbitrary incoming original argument query chooses its destination
capture frame. Argument F and own-domain R are both strictly below the actual
original application; there is no prechosen head valuation or alignment
supplier. Native projected metadata in the query is retained by argument F. -/
theorem generatedApplicationCapture
    {base : OriginalCaptureBase env U registry target}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (ordered : sourceEnv.Ordered)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (function : EndpointState sourceEnv U source f (.forallE A B))
    (argument : EndpointState sourceEnv U source a A)
    (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (location : Located root (.app hu hv (.ref domain) body function argument result))
    {graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw}
    (realized : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (generated : ScopedCaptureGenerated base commonLeft commonRight graph realized.frame.raw)
    (variableNode : EndpointState sourceEnv U (A :: source) (.bvar 0) assigned)
    (variableProvenance : EndpointProvenance (.cons (location.contextDerivation initial) domain) variableNode)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (argumentF : OriginalComputationalInductionAt env registry ordered initial (.appArgument location)
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin ordered)
        (realized.frame.dependencyEnvironment ordered)).cost)
    (domainR : richSchedule .expressionReindex
        ((Closure.close (argument.typeFormation.node.dependencyOrigin ordered) (realized.frame.dependencyEnvironment ordered)).cost +
         (Closure.close (domain.dependencyOrigin ordered) (realized.frame.dependencyEnvironment ordered)).cost) <
      richSchedule .fundamental
        (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin ordered)
          (realized.frame.dependencyEnvironment ordered)).cost →
      RichCodeTransfer env U registry target argument.typeFormation.node (.ref domain) locals locals
        (raw.comp commonLeft) (raw.comp commonLeft) available available)
    (query : RichObs sourceEnv env U registry target argument locals (raw.comp commonLeft) (profile : Profile n) footprint)
    (resources : footprint.Available available) :
    Nonempty (GeneratedQueryReply base
      (applicationCaptureVariableDisplay graph domain argument (.ofLocation (.appArgument location) initial)
        variableNode variableProvenance) commonLeft commonRight profile) := by
  have argumentBound : (Closure.close (argument.dependencyOrigin ordered) (realized.frame.dependencyEnvironment ordered)).cost <
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin ordered)
        (realized.frame.dependencyEnvironment ordered)).cost :=
    Nat.lt_of_lt_of_le (binder_other_cost (domain := domain.dependencyOrigin ordered)
      (bodies := [body.dependencyOrigin ordered])
      (children := [function.dependencyOrigin ordered, argument.dependencyOrigin ordered, result.dependencyOrigin ordered])
      (by simp) _)
      (application_cost_le_captured _ _ _ _ _ _)
  obtain ⟨answer⟩ := argumentF target locals _ _ available realized.frame argumentBound closed formed
    realized.substitutions query resources
  obtain ⟨aligned⟩ := domainR
    (EndpointState.application_argument_type_reindex_schedule ordered hu hv (.ref domain) body function argument result _)
    answer.certificate answer.resources
  have related := answer.related.convert henv answer.typed aligned.related
  let frame := realized.frame.capture domain initial argument (.appArgument location) rfl query resources
    aligned.certificate aligned.resources answer.typed related (captureNeeds profile)
    (fun need member => (captureNeeds_covered profile need member).1)
    (fun need member => (captureNeeds_covered profile need member).2)
  have nextGenerated : ScopedCaptureGenerated base commonLeft commonRight
      (.capture graph domain graph argument (.ofLocation (.appArgument location) initial)) frame.raw :=
    .capture generated domain initial argument (.appArgument location) rfl query resources
      aligned.certificate aligned.resources answer.typed related (captureNeeds profile)
      (fun need member => (captureNeeds_covered profile need member).1)
      (fun need member => (captureNeeds_covered profile need member).2)
  have rawPair := (argument.sound.defeq.mono below).substDF henv realized.substitutions.wf formed realized.substitutions
  have nextSubstitutions : Ctx.SubstEq env U target
      ((raw.comp commonLeft).cons (a.subst (raw.comp commonLeft)))
      ((raw.comp commonRight).cons (a.subst (raw.comp commonRight))) (A :: source) := Ctx.SubstEq.cons realized.substitutions (domain.sound.defeq.mono below) rawPair
  let captureGraph := OriginalCaptureMap.capture graph domain graph argument (.ofLocation (.appArgument location) initial)
  let captureRealization : OriginalCaptureRealization captureGraph env registry target (Locals.push locals)
      commonLeft commonRight (available.push (captureNeeds profile)) := {
    frame := castFrameSubstitutions frame (raw_capture_comp raw commonLeft a).symm
      (raw_capture_comp raw commonRight a).symm
    substitutions := by simpa only [raw_capture_comp] using nextSubstitutions }
  have generatedNext : ScopedCaptureGenerated base commonLeft commonRight captureGraph captureRealization.frame.raw := by
    exact generated_castFrameSubstitutions nextGenerated _ _
  refine ⟨{
    locals := Locals.push locals, available := available.push (captureNeeds profile),
    realization := captureRealization, generated := generatedNext,
    query := ?_, closed := Valuation.push_atomized_closed closed [⟨n, profile⟩] }⟩
  refine {
    rank := n, bound := Nat.le_refl _, raw := profile, footprint := [(0, Need.mk n profile)]
    observation := .legacy (.legacy (.var _ _ 0 profile))
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := ?_, live := answer.related.live henv hscoped formed }
  intro i need member
  cases List.mem_singleton.mp member
  exact List.mem_append_left _ (List.mem_singleton_self _)

/-- The captured variable itself pays its owner and domain. This reserve
is independent of the incoming query and of any surrounding application. -/
theorem capturedVariable_bundle_lt (variableOrigin argumentOrigin domainOrigin : Origin)
    (previous : List Closure) :
    (Closure.close argumentOrigin previous).cost + (Closure.close domainOrigin previous).cost <
      (Closure.close variableOrigin
        (Closure.bundle (.close argumentOrigin previous) (.close domainOrigin previous) :: previous)).cost := by
  have positive := variableOrigin.weight_pos
  have covered : 1 + environmentCost
      (Closure.bundle (.close argumentOrigin previous) (.close domainOrigin previous) :: previous) ≤
      (Closure.close variableOrigin
        (Closure.bundle (.close argumentOrigin previous) (.close domainOrigin previous) :: previous)).cost := by
    exact Nat.le_mul_of_pos_left _ positive
  change _ < variableOrigin.weight * _
  change 1 + max ((Closure.close argumentOrigin previous).cost + (Closure.close domainOrigin previous).cost)
    (environmentCost previous) ≤ variableOrigin.weight * _ at covered
  have bound := Nat.le_max_left ((Closure.close argumentOrigin previous).cost +
    (Closure.close domainOrigin previous).cost) (environmentCost previous)
  omega

/-- Query-selected right capture under its OWN variable closure budget.
The two recursive calls are legal in a global R pair containing this
captured endpoint; no enclosing application-parent budget is assumed. -/
theorem generatedOwnCapture
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
    (generated : ScopedCaptureGenerated base commonLeft commonRight graph realized.frame.raw)
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
      RichCodeTransfer env U registry target argument.typeFormation.node (.ref domain) locals locals
        (raw.comp commonLeft) (raw.comp commonLeft) available available)
    (query : RichObs sourceEnv env U registry target argument locals (raw.comp commonLeft) (profile : Profile n) footprint)
    (resources : footprint.Available available) :
    Nonempty (GeneratedQueryReply base
      (applicationCaptureVariableDisplay graph domain argument (.ofLocation location initial)
        variableNode variableProvenance) commonLeft commonRight profile) := by
  have bundleBound := capturedVariable_bundle_lt (variableNode.dependencyOrigin ordered)
    (argument.dependencyOrigin ordered) (domain.dependencyOrigin ordered) (realized.frame.dependencyEnvironment ordered)
  have argumentBound := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) bundleBound
  obtain ⟨answer⟩ := argumentF target locals _ _ available realized.frame argumentBound closed formed
    realized.substitutions query resources
  obtain ⟨aligned⟩ := domainR
    (richSchedule_strict (Nat.lt_of_le_of_lt
      (Nat.add_le_add_right (argument.typeFormation_dependency_cost_le ordered (realized.frame.dependencyEnvironment ordered)) _) bundleBound) _ _)
    answer.certificate answer.resources
  have related := answer.related.convert henv answer.typed aligned.related
  let frame := realized.frame.capture domain initial argument location rfl query resources
    aligned.certificate aligned.resources answer.typed related (captureNeeds profile)
    (fun need member => (captureNeeds_covered profile need member).1)
    (fun need member => (captureNeeds_covered profile need member).2)
  have nextGenerated : ScopedCaptureGenerated base commonLeft commonRight
      (.capture graph domain graph argument (.ofLocation location initial)) frame.raw :=
    .capture generated domain initial argument location rfl query resources
      aligned.certificate aligned.resources answer.typed related (captureNeeds profile)
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
  have generatedNext : ScopedCaptureGenerated base commonLeft commonRight captureGraph captureRealization.frame.raw := by
    exact generated_castFrameSubstitutions nextGenerated _ _
  refine ⟨{
    locals := Locals.push locals, available := available.push (captureNeeds profile),
    realization := captureRealization, generated := generatedNext,
    query := ?_, closed := Valuation.push_atomized_closed closed [⟨n, profile⟩] }⟩
  refine {
    rank := n, bound := Nat.le_refl _, raw := profile, footprint := [(0, Need.mk n profile)]
    observation := .legacy (.legacy (.var _ _ 0 profile))
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := ?_, live := answer.related.live henv hscoped formed }
  intro i need member
  cases List.mem_singleton.mp member
  exact List.mem_append_left _ (List.mem_singleton_self _)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
