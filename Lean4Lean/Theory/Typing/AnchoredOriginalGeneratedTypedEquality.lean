import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedAssignedComparison
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyNormalization
import Lean4Lean.Theory.Typing.AnchoredOriginalRawTypeRoute

/-! An original normalization may have a non-sort assigned type. Retain an
actual sorted source header and use original assigned comparison to cast the
original equality. Empty code support does not stand in for that raw path. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- The original equality F clause at its actual assigned type. -/
def OriginalEqualityInductionAt
    (env : VEnv) (registry : CanonicalHead.Registry) (ordered : sourceEnv.Ordered)
    (context : ContextDerivation sourceEnv U source)
    (original : Derivation sourceEnv U source A B assigned) (limit : Nat) : Prop :=
  ∀ target locals σ available,
    ∀ frame : OriginalRichFrame sourceEnv env U registry target context locals σ σ available,
    richSchedule .fundamental
      (Closure.close (original.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost < limit →
    available.AtomClosed → OnCtx target (env.IsType U) → Ctx.SubstEq env U target σ σ source →
    ∀ {n : Nat} {profile : Profile n} {footprint : Footprint},
      RichObs sourceEnv env U registry target (.ref (.left original)) locals σ profile footprint →
      footprint.Available available →
      Nonempty (OriginalEqualityQueryResult original env registry target locals σ σ available profile)

/-- Both the query and the raw type conversion come from actual original
calls. The auxiliary empty comparison only aligns the assigned types; a
separate R call transports the full requested source query. -/
theorem BoundedParameterReply.typedEquality
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (original : Derivation sourceEnv U source A B assigned)
    (left : OriginalNestedDisplay U common expression (.sort level))
    (same : expression = A.subst raw)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (lf : left.sourceEnv.Ordered) (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (frame : ParameterReplyFrame base commonCaps graph commonLeft commonRight)
    (answer : BoundedParameterReply base commonCaps start left commonLeft commonRight
      (profile : Profile n) capacity)
    (sorted : profile.HasType (.sort true))
    (pairScheduled : richSchedule .expressionReindex
      ((left.node.dependencyOrigin lf).weight * (1 + capacity) +
        (Closure.close (original.dependencyOrigin ordered)
          (frame.realization.frame.dependencyEnvironment ordered)).cost) < limit)
    (equalityScheduled : richSchedule .fundamental
      (Closure.close (original.dependencyOrigin ordered)
        (frame.realization.frame.dependencyEnvironment ordered)).cost < limit)
    (reindex : GeneratedObservationCall base commonCaps (same ▸ left) (graph.typeEqualityDisplay original true)
      commonLeft commonRight (by cases same; exact lf) ordered limit)
    (compare : GeneratedAssignedCall base commonCaps (same ▸ left) (graph.typeEqualityDisplay original true)
      commonLeft commonRight (by cases same; exact lf) ordered limit)
    (equalityF : OriginalEqualityInductionAt env registry ordered context original limit) :
    Nonempty (BoundedParameterReply base commonCaps start (graph.typeEqualityDisplay original false)
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
  obtain ⟨typeChanged⟩ := compare prior.realization answer.reply.answer.capped prior.closed
    frame.realization frame.capped frame.closed compareScheduled empty (by intro _ _ member; cases member)
  have typePath : TypeConversion env U target (.sort level) (assigned.subst (raw.comp commonLeft)) := by
    simpa only [OriginalNestedDisplay.formationDisplay, OriginalCaptureMap.typeEqualityDisplay,
      subst_subst, subst] using typeChanged.path
  obtain ⟨input⟩ := answer.reindexAt henv lf ordered sorted frame.realization frame.capped frame.closed
    pairScheduled reindex
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
  obtain ⟨changed⟩ := equalityF target selected.locals (raw.comp commonLeft) selected.available
    selected.realization.frame.leftDiagonal actualScheduled selected.closed formed
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
    path := ?_ }⟩
  · apply input.related.trans henv
    simpa only [OriginalCaptureMap.typeEqualityDisplay, Bool.false_eq_true, reduceIte, subst_subst] using related
  · apply input.path.trans
    simpa only [OriginalCaptureMap.typeEqualityDisplay, Bool.false_eq_true, reduceIte, subst_subst] using path

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
