import Lean4Lean.Theory.Typing.AnchoredOriginalLowerCallBank
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFrameAmbientDiagonal

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option Elab.async false

structure AmbientParameterReplyFrame
    (base : OriginalCaptureBase env U registry target) (commonCaps : CaptureCaps)
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (commonLeft commonRight : Subst)
    extends ParameterReplyFrame base commonCaps graph commonLeft commonRight where
  generation : AmbientCaptureGenerated base commonCaps commonLeft commonRight graph realization.frame.raw

theorem AmbientBoundedParameterReply.reindexAt
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {base : OriginalCaptureBase env U registry target}
    {left : OriginalNestedDisplay U common expression leftType}
    {right : OriginalNestedDisplay U common expression rightType}
    (henv : env.Ordered) (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered)
    (answer : AmbientBoundedParameterReply base commonCaps start left commonLeft commonRight (profile : Profile n) capacity)
    (sorted : profile.HasType (.sort relevant))
    (rightFrame : OriginalCaptureRealization right.graph env registry target rightLocals commonLeft commonRight rightAvailable)
    (rightCapped : AmbientCaptureGenerated base commonCaps commonLeft commonRight right.graph rightFrame.frame.raw)
    (rightClosed : rightAvailable.AtomClosed)
    (reserve : richSchedule .expressionReindex
      ((left.node.dependencyOrigin lf).weight * (1 + capacity) +
        (Closure.close (right.node.dependencyOrigin rf) (rightFrame.frame.dependencyEnvironment rf)).cost) < limit)
    (bank : OriginalLowerCallBank env U registry limit) :
    Nonempty (AmbientBoundedParameterReply base commonCaps start right commonLeft commonRight profile
      (environmentCost (rightFrame.frame.dependencyEnvironment rf))) := by
  let prior := answer.reply.answer.reply
  obtain ⟨footprint, ⟨certificate⟩, resources⟩ := prior.query.code henv sorted
  have scheduled : richSchedule .expressionReindex
      ((Closure.close (left.node.dependencyOrigin lf) (prior.realization.frame.dependencyEnvironment lf)).cost +
        (Closure.close (right.node.dependencyOrigin rf) (rightFrame.frame.dependencyEnvironment rf)).cost) < limit := by
    have bound := Nat.mul_le_mul_left (left.node.dependencyOrigin lf).weight
      (Nat.add_le_add_left (answer.reply.bounded lf) 1)
    exact Nat.lt_of_le_of_lt (by
      change 3 * (_ + _) + 2 ≤ 3 * (_ + _) + 2
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 3 (Nat.add_le_add_right bound _)) 2) reserve
  obtain ⟨replayed⟩ := bank.observation base commonCaps left right commonLeft commonRight lf rf prior.realization answer.generation prior.closed
    rightFrame rightCapped rightClosed scheduled (.code certificate) resources
  exact ⟨{ toBoundedParameterReply := ⟨replayed.toBoundedGeneratedQueryReply, answer.related, answer.path⟩
           generation := replayed.generation }⟩
theorem AmbientBoundedParameterReply.assignedAt
    {base : OriginalCaptureBase env U registry target}
    {left : OriginalNestedDisplay U common expression leftAssigned}
    {right : OriginalNestedDisplay U common expression rightAssigned}
    (henv : env.Ordered) (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered)
    (answer : AmbientBoundedParameterReply base commonCaps start left.formationDisplay
      commonLeft commonRight (profile : Profile n) capacity)
    (sorted : profile.HasType (.sort relevant))
    (rightFrame : AmbientParameterReplyFrame base commonCaps right.graph commonLeft commonRight)
    (reserve : richSchedule .assignedComparison
      ((left.node.dependencyOrigin lf).weight * (1 + capacity) +
        (Closure.close (right.node.dependencyOrigin rf)
          (rightFrame.realization.frame.dependencyEnvironment rf)).cost) < limit)
    (bank : OriginalLowerCallBank env U registry limit) :
    Nonempty (AmbientBoundedParameterReply base commonCaps start right.formationDisplay
      commonLeft commonRight profile (rightFrame.capacity rf)) := by
  let prior := answer.reply.answer.reply
  obtain ⟨footprint, ⟨certificate⟩, resources⟩ := prior.query.code henv sorted
  have scheduled : richSchedule .assignedComparison
      ((Closure.close (left.node.dependencyOrigin lf) (prior.realization.frame.dependencyEnvironment lf)).cost +
        (Closure.close (right.node.dependencyOrigin rf)
          (rightFrame.realization.frame.dependencyEnvironment rf)).cost) < limit := by
    have bound := Nat.mul_le_mul_left (left.node.dependencyOrigin lf).weight
      (Nat.add_le_add_left (answer.reply.bounded lf) 1)
    exact Nat.lt_of_le_of_lt (by
      change 3 * (_ + _) + 1 ≤ 3 * (_ + _) + 1
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 3 (Nat.add_le_add_right bound _)) 1) reserve
  obtain ⟨changed⟩ := bank.assigned base commonCaps left right commonLeft commonRight lf rf prior.realization answer.generation prior.closed
    rightFrame.realization rightFrame.generation rightFrame.closed scheduled certificate resources
  exact ⟨{ toBoundedParameterReply := ⟨changed.reply, answer.related.trans henv changed.related, answer.path.trans changed.path⟩
           generation := changed.generation }⟩

theorem AmbientBoundedParameterReply.typedEquality
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (original : Derivation sourceEnv U source A B assigned)
    (left : OriginalNestedDisplay U common expression (.sort level))
    (same : expression = A.subst raw)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (lf : left.sourceEnv.Ordered) (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (frame : AmbientParameterReplyFrame base commonCaps graph commonLeft commonRight)
    (answer : AmbientBoundedParameterReply base commonCaps start left commonLeft commonRight
      (profile : Profile n) capacity)
    (sorted : profile.HasType (.sort true))
    (pairScheduled : richSchedule .expressionReindex
      ((left.node.dependencyOrigin lf).weight * (1 + capacity) +
        (Closure.close (original.dependencyOrigin ordered)
          (frame.realization.frame.dependencyEnvironment ordered)).cost) < limit)
    (equalityScheduled : richSchedule .fundamental
      (Closure.close (original.dependencyOrigin ordered)
        (frame.realization.frame.dependencyEnvironment ordered)).cost < limit)
    (bank : OriginalLowerCallBank env U registry limit) :
    Nonempty (AmbientBoundedParameterReply base commonCaps start (graph.typeEqualityDisplay original false)
      commonLeft commonRight profile (frame.capacity ordered)) := by
  cases same
  let prior := answer.reply.answer.reply
  have compareScheduled : richSchedule .assignedComparison
      ((Closure.close (left.node.dependencyOrigin lf)
          (prior.realization.frame.dependencyEnvironment lf)).cost +
        (Closure.close (original.dependencyOrigin ordered)
          (frame.realization.frame.dependencyEnvironment ordered)).cost) < limit := by
    have bounded := Nat.mul_le_mul_left (left.node.dependencyOrigin lf).weight
      (Nat.add_le_add_left (answer.reply.bounded lf) 1)
    simp only [prior, Closure.cost, richSchedule, RichPhase.code] at pairScheduled bounded ⊢
    omega
  let empty : RichCert left.sourceEnv env U registry target left.node.typeFormation.node
      prior.locals (left.raw.comp commonLeft) true (Profile.empty : Profile 0) [] :=
    .legacy (.seed .empty (Profile.HasType.empty (Profile.WF.sort true)))
  obtain ⟨typeChanged⟩ := bank.assigned base commonCaps left (graph.typeEqualityDisplay original true)
    commonLeft commonRight lf ordered prior.realization answer.generation prior.closed
    frame.realization frame.generation frame.closed compareScheduled empty (by intro _ _ member; cases member)
  have typePath : TypeConversion env U target (.sort level) (assigned.subst (raw.comp commonLeft)) := by
    simpa only [OriginalNestedDisplay.formationDisplay, OriginalCaptureMap.typeEqualityDisplay,
      subst_subst, subst] using typeChanged.path
  obtain ⟨input⟩ := answer.reindexAt (right := graph.typeEqualityDisplay original true) henv lf ordered sorted frame.realization frame.generation frame.closed
    pairScheduled bank
  let selected := input.reply.answer.reply
  obtain ⟨footprint, ⟨certificate⟩, resources⟩ := selected.query.code henv sorted
  have actualScheduled : richSchedule .fundamental
      (Closure.close (original.dependencyOrigin ordered)
        (selected.realization.frame.leftDiagonal.dependencyEnvironment ordered)).cost < limit := by
    rw [OriginalRichFrame.dependencyEnvironment_leftDiagonal]
    have bounded := Nat.mul_le_mul_left (original.dependencyOrigin ordered).weight
      (Nat.add_le_add_left (input.reply.bounded ordered) 1)
    exact Nat.lt_of_le_of_lt (by
      change 3 * _ + 0 ≤ 3 * _ + 0
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 3 bounded) 0) equalityScheduled
  obtain ⟨changed⟩ := bank.equalityAt ordered below context original target selected.locals (raw.comp commonLeft) selected.available
    selected.realization.frame.leftDiagonal (input.ambient.leftDiagonal _) actualScheduled selected.closed formed
    selected.realization.substitutions.left (.code certificate) resources
  obtain ⟨outFootprint, ⟨outCertificate⟩, outResources, related⟩ := changed.code henv hscoped formed sorted
  let query : RichGradedResult sourceEnv env U registry target (.ref (.right original))
      selected.locals (raw.comp commonLeft) selected.available profile := {
    rank := n, bound := Nat.le_refl _, raw := profile
    footprint := outFootprint, observation := .code outCertificate
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := outResources
    live := Profile.HasType.sortable_live sorted }
  have rawEquality := (original.forget.defeq.mono below).substDF henv
    selected.realization.substitutions.left.wf formed selected.realization.substitutions.left
  have path := TypeConversion.single (typePath.symm.cast rawEquality)
  refine ⟨{
    reply := {
      answer := {
        reply := { selected with query := query }
        capped := input.reply.answer.capped }
      bounded := input.reply.bounded }
    related := ?_
    path := ?_
    generation := input.generation }⟩
  · apply input.related.trans henv
    simpa only [OriginalCaptureMap.typeEqualityDisplay, Bool.false_eq_true, reduceIte, subst_subst] using related
  · apply input.path.trans
    simpa only [OriginalCaptureMap.typeEqualityDisplay, Bool.false_eq_true, reduceIte, subst_subst] using path
theorem AmbientBoundedParameterReply.equality
    {sourceEnv env : VEnv} {U : Nat}
    {registry : CanonicalHead.Registry} {target common : List VExpr}
    {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
    {commonLeft commonRight : Subst} {start : VExpr}
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (original : Derivation sourceEnv U source A B (.sort level)) (forward : Bool)
    (henv : env.Ordered) (hscoped : registry.Scoped) (ordered : sourceEnv.Ordered)
    (formed : OnCtx target (env.IsType U))
    (answer : AmbientBoundedParameterReply base commonCaps start (parameterEqualityDisplay graph original forward)
      commonLeft commonRight (profile : Profile n) capacity)
    (sorted : profile.HasType (.sort relevant))
    (reserve : richSchedule .fundamental
      ((original.dependencyOrigin ordered).weight * (1 + capacity)) < limit)
    (bank : OriginalLowerCallBank env U registry limit) :
    ∃ result : AmbientBoundedParameterReply base commonCaps start (parameterEqualityDisplay graph original (!forward))
        commonLeft commonRight profile capacity,
      result.reply.answer.reply.available = answer.reply.answer.reply.available ∧
      result.reply.answer.reply.locals = answer.reply.answer.reply.locals := by
  let prior := answer.reply.answer.reply
  obtain ⟨footprint, ⟨certificate⟩, resources⟩ := prior.query.code henv sorted
  have environmentBound := answer.reply.bounded ordered
  have scheduled : richSchedule .fundamental
      (Closure.close (original.dependencyOrigin ordered)
        (prior.realization.frame.leftDiagonal.dependencyEnvironment ordered)).cost < limit := by
    rw [OriginalRichFrame.dependencyEnvironment_leftDiagonal]
    have bound := Nat.mul_le_mul_left (original.dependencyOrigin ordered).weight
      (Nat.add_le_add_left environmentBound 1)
    exact Nat.lt_of_le_of_lt (by
      change 3 * _ + 0 ≤ 3 * _ + 0
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 3 bound) 0) reserve
  obtain ⟨changed⟩ := bank.parameterEqualityAt henv hscoped ordered answer.ambient.below context original forward target prior.locals (raw.comp commonLeft) prior.available
    prior.realization.frame.leftDiagonal (OriginalRichFrame.Ambient.leftDiagonal _ answer.ambient) scheduled prior.closed formed prior.realization.substitutions.left
    certificate resources
  let query : RichGradedResult sourceEnv env U registry target
      (.ref (parameterEqualitySide original (!forward))) prior.locals (raw.comp commonLeft) prior.available profile := {
    rank := n, bound := Nat.le_refl _, raw := profile
    footprint := changed.footprint, observation := .code changed.certificate
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := changed.resources
    live := Profile.HasType.sortable_live sorted }
  let next : BoundedGeneratedQueryReply base commonCaps (parameterEqualityDisplay graph original (!forward))
      commonLeft commonRight profile capacity := {
    answer := {
      reply := {
        locals := prior.locals, available := prior.available, realization := prior.realization
        generated := prior.generated, query := query, closed := prior.closed }
      capped := answer.reply.answer.capped }
    bounded := answer.reply.bounded }
  have related : TypeRelated env U registry target
      (((if forward then A else B).subst raw).subst commonLeft)
      (((if !forward then A else B).subst raw).subst commonLeft) profile := by
    simpa only [subst_subst] using changed.related
  have rawEquality := (original.forget.defeq.mono answer.ambient.below).substDF henv
    prior.realization.substitutions.left.wf formed prior.realization.substitutions.left
  have path : TypeConversion env U target
      (((if forward then A else B).subst raw).subst commonLeft)
      (((if !forward then A else B).subst raw).subst commonLeft) := by
    cases forward
    · simpa only [Bool.not_false, Bool.false_eq_true, reduceIte, subst_subst, parameterEqualityDisplay, OriginalCaptureMap.parameterCellDisplay] using
        (TypeConversion.single rawEquality.symm)
    · simpa only [Bool.not_true, Bool.false_eq_true, reduceIte, subst_subst, parameterEqualityDisplay, OriginalCaptureMap.parameterCellDisplay] using
        (TypeConversion.single rawEquality)
  exact ⟨{ toBoundedParameterReply := ⟨next, answer.related.trans henv related, answer.path.trans path⟩
           generation := answer.generation }, rfl, rfl⟩
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
