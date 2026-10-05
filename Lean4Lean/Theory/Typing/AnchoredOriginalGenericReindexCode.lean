import Lean4Lean.Theory.Typing.AnchoredOriginalGenericComputational
import Lean4Lean.Theory.Typing.AnchoredOriginalRichCodeAction

/-! The formation-code channel of source reindexing. Once the actual
observation tree has been rebuilt, one strictly smaller unary F supplies its
semantics. Original source equality is retained before target substitution. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem OriginalRichFrame.codeReindexOfObservation
    {leftRoot : EndpointRef leftEnv U leftRootSource leftRootExpression leftRootType}
    {rightRoot : EndpointRef rightEnv U rightRootSource rightRootExpression rightRootType}
    {left : EndpointState leftEnv U leftSource leftExpression (.sort leftLevel)}
    {right : EndpointState rightEnv U rightSource rightExpression (.sort rightLevel)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (lf : leftEnv.Ordered) (rf : rightEnv.Ordered)
    (leftInitial : ContextDerivation leftEnv U leftRootSource)
    (rightInitial : ContextDerivation rightEnv U rightRootSource)
    (leftLocation : Located leftRoot left) (rightLocation : Located rightRoot right)
    (leftInsertion : Ctx.Lift' leftMap leftSource displayed)
    (rightInsertion : Ctx.Lift' rightMap rightSource displayed)
    (sourceEqual : leftExpression.lift' leftMap = rightExpression.lift' rightMap)
    (common : Subst)
    (leftFrame : OriginalRichFrame leftEnv env U registry target
      (leftLocation.contextDerivation leftInitial) leftLocals
      (Subst.lift_l leftMap common) (Subst.lift_l leftMap common) leftAvailable)
    (rightFrame : OriginalRichFrame rightEnv env U registry target
      (rightLocation.contextDerivation rightInitial) rightLocals
      (Subst.lift_l rightMap common) (Subst.lift_l rightMap common) rightAvailable)
    (closed : leftAvailable.AtomClosed)
    (substitutions : Ctx.SubstEq env U target (Subst.lift_l leftMap common)
      (Subst.lift_l leftMap common) leftSource)
    (sourceF : OriginalCodeInductionAt env registry lf leftInitial leftLocation
      ((Closure.close (left.dependencyOrigin lf) (leftFrame.dependencyEnvironment lf)).cost +
       (Closure.close (right.dependencyOrigin rf) (rightFrame.dependencyEnvironment rf)).cost))
    (observationR : ∀ {n : Nat} {profile : Profile n} {footprint : Footprint},
      RichObs leftEnv env U registry target left leftLocals (Subst.lift_l leftMap common) profile footprint →
      footprint.Available leftAvailable →
      Nonempty (RichGradedResult rightEnv env U registry target right rightLocals
        (Subst.lift_l rightMap common) rightAvailable profile)) :
    RichCodeTransfer env U registry target left right leftLocals rightLocals
      (Subst.lift_l leftMap common) (Subst.lift_l rightMap common) leftAvailable rightAvailable := by
  intro relevant n profile footprint query resources
  obtain ⟨destination⟩ := observationR (.code query) resources
  obtain ⟨required, ⟨certificate⟩, available⟩ := destination.code henv query.formed
  have positive := (Closure.close (right.dependencyOrigin rf) (rightFrame.dependencyEnvironment rf)).cost_pos
  obtain ⟨semantics⟩ := sourceF target leftLocals _ _ leftAvailable leftFrame
    (Nat.lt_add_of_pos_right positive) closed formed substitutions query resources
  have equal := congrArg (fun expression => expression.subst common) sourceEqual
  simp only [subst_lift'] at equal
  exact ⟨⟨required, certificate, available, by simpa only [← equal] using semantics.related⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
