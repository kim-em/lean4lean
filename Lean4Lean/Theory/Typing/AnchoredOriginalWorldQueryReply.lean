import Lean4Lean.Theory.Typing.AnchoredOriginalBoundedGeneratedReply
import Lean4Lean.Theory.Typing.AnchoredOriginalRichSchedule
import Lean4Lean.Theory.Typing.EquationWorldClosureOrder

/-! The R-to-F continuation keeps the selected reply's actual frame and its
existing numerical capacity bound. Query-owned foreign children use a separate
source sponsor. Hereditary world coverage must be proved by the reconstruction
producer; numerical capacity alone does not supply it. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

theorem BoundedGeneratedQueryReply.sponsoredFundamentalDecrease
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    (ordered : display.sourceEnv.Ordered)
    (prior : OriginalCaptureRealization display.graph env registry target
      locals commonLeft commonRight available)
    (reply : BoundedGeneratedQueryReply base caps display commonLeft commonRight profile
      (environmentCost (prior.frame.dependencyEnvironment ordered)))
    (count cutoff : Nat) (fuel : Nat → Nat)
    (source : EquationWorldClosureOrder.World count)
    (priorCaptures nextCaptures foreignUses : List (EquationWorldClosureOrder.World count))
    (covered : EquationWorldClosureOrder.Covered (@EquationControlMeasure.Less count)
      nextCaptures priorCaptures)
    (foreignBound : ∀ child ∈ foreignUses, EquationWorldClosureOrder.WorldBelow count child source) :
    let previous := EquationWorldClosureOrder.Closure.node
      (EquationControlMeasure.key count cutoff fuel ordered.constantCount
        (richSchedule .expressionReindex
          (Closure.close (display.node.dependencyOrigin ordered)
            (prior.frame.dependencyEnvironment ordered)).cost)) priorCaptures
    let next := EquationWorldClosureOrder.Closure.node
      (EquationControlMeasure.key count cutoff fuel ordered.constantCount
        (richSchedule .fundamental
          (Closure.close (display.node.dependencyOrigin ordered)
            (reply.answer.reply.realization.frame.dependencyEnvironment ordered)).cost)) nextCaptures
    EquationWorldClosureOrder.CallBelow count [source, next] [source, previous] ∧
      EquationWorldClosureOrder.Sponsored [source, next] (foreignUses ++ nextCaptures) := by
  have frameBound := reply.bounded ordered
  have costBound :
      (Closure.close (display.node.dependencyOrigin ordered)
        (reply.answer.reply.realization.frame.dependencyEnvironment ordered)).cost ≤
      (Closure.close (display.node.dependencyOrigin ordered)
        (prior.frame.dependencyEnvironment ordered)).cost :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_left frameBound 1)
  have smaller :
      richSchedule .fundamental
        (Closure.close (display.node.dependencyOrigin ordered)
          (reply.answer.reply.realization.frame.dependencyEnvironment ordered)).cost <
      richSchedule .expressionReindex
        (Closure.close (display.node.dependencyOrigin ordered)
          (prior.frame.dependencyEnvironment ordered)).cost := by
    simp only [richSchedule, RichPhase.code]
    omega
  exact EquationWorldClosureOrder.sponsored_continuation source cutoff fuel ordered.constantCount
    smaller priorCaptures nextCaptures foreignUses covered foreignBound

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
