import Lean4Lean.Theory.Typing.AnchoredOriginalBoundedGeneratedReply
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericComputational

/-! The semantic code channel uses the very frame returned by bounded
source-query reconstruction. One smaller original unary F supplies the
relation; no destination semantics or equality after substitution is assumed. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem boundedGeneratedCodeReindex
    {base : OriginalCaptureBase env U registry target}
    {leftRoot : EndpointRef leftEnv U leftRootSource leftRootExpression leftRootType}
    {left : EndpointState leftEnv U leftSource leftExpression (.sort leftLevel)}
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (leftOrdered : leftEnv.Ordered)
    (initial : ContextDerivation leftEnv U leftRootSource)
    (location : Located leftRoot left)
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
    (leftFrame : OriginalCaptureRealization graph env registry target leftLocals realization realization leftAvailable)
    (closed : leftAvailable.AtomClosed)
    (right : OriginalNestedDisplay U common expression rightAssigned)
    (rightOrdered : right.sourceEnv.Ordered)
    (rightFrame : OriginalCaptureRealization right.graph env registry target rightLocals realization realization rightAvailable)
    (rightSort : right.sourceType = .sort rightLevel)
    (sourceEqual : leftExpression.subst raw = right.sourceExpression.subst right.raw)
    (sourceF : OriginalCodeInductionAt env registry leftOrdered initial location
      ((Closure.close (left.dependencyOrigin leftOrdered) (leftFrame.frame.dependencyEnvironment leftOrdered)).cost +
        (Closure.close (right.node.dependencyOrigin rightOrdered)
          (rightFrame.frame.dependencyEnvironment rightOrdered)).cost))
    (query : RichCert leftEnv env U registry target left leftLocals (raw.comp realization)
      relevant (profile : Profile n) footprint)
    (resources : footprint.Available leftAvailable)
    (reply : BoundedGeneratedQueryReply base commonCaps right realization realization profile
      (environmentCost (rightFrame.frame.dependencyEnvironment rightOrdered))) :
    Nonempty (RichCodeTransferResult env U registry target left (right.node.cast rfl rightSort)
      reply.answer.reply.locals (raw.comp realization) (right.raw.comp realization)
      reply.answer.reply.available relevant profile) := by
  rcases right with ⟨rightEnv, rightSource, rightExpression, rightType, rightContext,
    rightNode, rightProvenance, rightRaw, rightGraph, rightExpressionEq, rightTypeEq⟩
  dsimp only at rightSort
  cases rightSort
  obtain ⟨required, ⟨certificate⟩, outputResources⟩ := reply.answer.reply.query.code henv query.formed
  have positive := (Closure.close (rightNode.dependencyOrigin rightOrdered)
    (rightFrame.frame.dependencyEnvironment rightOrdered)).cost_pos
  obtain ⟨semantics⟩ := sourceF target leftLocals _ _ leftAvailable leftFrame.frame
    (Nat.lt_add_of_pos_right positive) closed formed leftFrame.substitutions query resources
  have equal := congrArg (fun e : VExpr => e.subst realization) sourceEqual
  simp only [subst_subst] at equal
  exact ⟨⟨required, certificate, outputResources, by simpa only [← equal] using semantics.related⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
