import Lean4Lean.Theory.Typing.AnchoredOriginalParameterEqualityData
import Lean4Lean.Theory.Typing.AnchoredOriginalBoundedGeneratedReply
import Lean4Lean.Theory.Typing.AnchoredOriginalParameterCaptureStep
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichFrameDiagonal
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedNativePiReindex

/-! A query-selected parameter frame crosses an actual original equality
without changing its graph or valuation. Frame selection belongs to the
source-reindex edges; equality F is invoked on the exact chosen frame. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- The fixed original equality clause of mutual F. The source context and
original equality are fixed; the selected frame and query are quantified. -/
def ParameterEqualityInductionAt
    (env : VEnv) (registry : CanonicalHead.Registry) (ordered : sourceEnv.Ordered)
    (context : ContextDerivation sourceEnv U source)
    (original : Derivation sourceEnv U source A B (.sort level)) (forward : Bool)
    (limit : Nat) : Prop :=
  ∀ target locals σ available,
    ∀ frame : OriginalRichFrame sourceEnv env U registry target context locals σ σ available,
    richSchedule .fundamental
      (Closure.close (original.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost < limit →
    available.AtomClosed → OnCtx target (env.IsType U) → Ctx.SubstEq env U target σ σ source →
    RichCodeTransfer env U registry target (.ref (parameterEqualitySide original forward))
      (.ref (parameterEqualitySide original (!forward))) locals locals σ σ available available

/-- Only the exact output of the fixed original equality F is used. Its
query is placed back in the incoming generated frame, whose paired source
realization and hereditary caps are unchanged. -/
theorem BoundedParameterReply.equality
    {sourceEnv env : VEnv} {U : Nat}
    {registry : CanonicalHead.Registry} {target common : List VExpr}
    {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
    {commonLeft commonRight : Subst} {start : VExpr}
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (original : Derivation sourceEnv U source A B (.sort level)) (forward : Bool)
    (henv : env.Ordered) (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (answer : BoundedParameterReply base commonCaps start (parameterEqualityDisplay graph original forward)
      commonLeft commonRight (profile : Profile n) capacity)
    (sorted : profile.HasType (.sort relevant))
    (reserve : richSchedule .fundamental
      ((original.dependencyOrigin ordered).weight * (1 + capacity)) < limit)
    (induction : ParameterEqualityInductionAt env registry ordered context original forward limit) :
    ∃ result : BoundedParameterReply base commonCaps start (parameterEqualityDisplay graph original (!forward))
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
  obtain ⟨changed⟩ := induction target prior.locals (raw.comp commonLeft) prior.available
    prior.realization.frame.leftDiagonal scheduled prior.closed formed prior.realization.substitutions.left
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
  have rawEquality := (original.forget.defeq.mono below).substDF henv
    prior.realization.substitutions.left.wf formed prior.realization.substitutions.left
  have path : TypeConversion env U target
      (((if forward then A else B).subst raw).subst commonLeft)
      (((if !forward then A else B).subst raw).subst commonLeft) := by
    cases forward
    · simpa only [Bool.not_false, Bool.false_eq_true, reduceIte, subst_subst, parameterEqualityDisplay, OriginalCaptureMap.parameterCellDisplay] using
        (TypeConversion.single rawEquality.symm)
    · simpa only [Bool.not_true, Bool.false_eq_true, reduceIte, subst_subst, parameterEqualityDisplay, OriginalCaptureMap.parameterCellDisplay] using
        (TypeConversion.single rawEquality)
  exact ⟨⟨next, answer.related.trans henv related, answer.path.trans path⟩, rfl, rfl⟩


/-- Invoke the existing query-selected R contract on an exact code query.
The result's resources are taken from the returned frame, never from the
input frame. Only the pre-answer capacity is used in the call bound. -/
theorem BoundedParameterReply.reindexAt
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {base : OriginalCaptureBase env U registry target}
    {left : OriginalNestedDisplay U common expression leftType}
    {right : OriginalNestedDisplay U common expression rightType}
    (henv : env.Ordered) (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered)
    (answer : BoundedParameterReply base commonCaps start left commonLeft commonRight (profile : Profile n) capacity)
    (sorted : profile.HasType (.sort relevant))
    (rightFrame : OriginalCaptureRealization right.graph env registry target rightLocals commonLeft commonRight rightAvailable)
    (rightCapped : CappedCaptureGenerated base commonCaps commonLeft commonRight right.graph rightFrame.frame.raw)
    (rightClosed : rightAvailable.AtomClosed)
    (reserve : richSchedule .expressionReindex
      ((left.node.dependencyOrigin lf).weight * (1 + capacity) +
        (Closure.close (right.node.dependencyOrigin rf) (rightFrame.frame.dependencyEnvironment rf)).cost) < limit)
    (induction : GeneratedObservationCall base commonCaps left right commonLeft commonRight lf rf limit) :
    Nonempty (BoundedParameterReply base commonCaps start right commonLeft commonRight profile
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
  obtain ⟨replayed⟩ := induction prior.realization answer.reply.answer.capped prior.closed
    rightFrame rightCapped rightClosed scheduled (.code certificate) resources
  exact ⟨answer.reindex replayed⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
