import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedParameterCells
import Lean4Lean.Theory.Typing.AnchoredOriginalNestedFormation

/-! Assigned-type comparison is a separate original induction clause.
Equal displayed terms need not have literally equal displayed assigned
types. Its query-selected reply retains the actual right formation and
returns both the same-profile relation and the raw conversion path. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

def GeneratedAssignedCall
    (base : OriginalCaptureBase env U registry target) (commonCaps : CaptureCaps)
    (left : OriginalNestedDisplay U common expression leftAssigned)
    (right : OriginalNestedDisplay U common expression rightAssigned)
    (commonLeft commonRight : Subst) (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered)
    (limit : Nat) : Prop :=
  ∀ {leftLocals leftAvailable}
    (leftFrame : OriginalCaptureRealization left.graph env registry target leftLocals commonLeft commonRight leftAvailable),
    CappedCaptureGenerated base commonCaps commonLeft commonRight left.graph leftFrame.frame.raw →
    leftAvailable.AtomClosed →
    ∀ {rightLocals rightAvailable}
    (rightFrame : OriginalCaptureRealization right.graph env registry target rightLocals commonLeft commonRight rightAvailable),
    CappedCaptureGenerated base commonCaps commonLeft commonRight right.graph rightFrame.frame.raw →
    rightAvailable.AtomClosed →
    richSchedule .assignedComparison
      ((Closure.close (left.node.dependencyOrigin lf) (leftFrame.frame.dependencyEnvironment lf)).cost +
       (Closure.close (right.node.dependencyOrigin rf) (rightFrame.frame.dependencyEnvironment rf)).cost) < limit →
    ∀ {n : Nat} {profile : Profile n} {footprint : Footprint} {relevant : Bool},
    RichCert left.sourceEnv env U registry target left.node.typeFormation.node leftLocals
      (left.raw.comp commonLeft) relevant profile footprint →
    footprint.Available leftAvailable →
    Nonempty (BoundedParameterReply base commonCaps (leftAssigned.subst commonLeft)
      right.formationDisplay commonLeft commonRight profile
      (environmentCost (rightFrame.frame.dependencyEnvironment rf)))

/-- The C edge uses the actual term-pair budget, not the smaller formation
pair. Only the already computed capacity bounds the selected left frame. -/
theorem BoundedParameterReply.assignedAt
    {base : OriginalCaptureBase env U registry target}
    {left : OriginalNestedDisplay U common expression leftAssigned}
    {right : OriginalNestedDisplay U common expression rightAssigned}
    (henv : env.Ordered) (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered)
    (answer : BoundedParameterReply base commonCaps start left.formationDisplay
      commonLeft commonRight (profile : Profile n) capacity)
    (sorted : profile.HasType (.sort relevant))
    (rightFrame : ParameterReplyFrame base commonCaps right.graph commonLeft commonRight)
    (reserve : richSchedule .assignedComparison
      ((left.node.dependencyOrigin lf).weight * (1 + capacity) +
        (Closure.close (right.node.dependencyOrigin rf)
          (rightFrame.realization.frame.dependencyEnvironment rf)).cost) < limit)
    (induction : GeneratedAssignedCall base commonCaps left right commonLeft commonRight lf rf limit) :
    Nonempty (BoundedParameterReply base commonCaps start right.formationDisplay
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
  obtain ⟨changed⟩ := induction prior.realization answer.reply.answer.capped prior.closed
    rightFrame.realization rightFrame.capped rightFrame.closed scheduled certificate resources
  exact ⟨⟨changed.reply, answer.related.trans henv changed.related, answer.path.trans changed.path⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
