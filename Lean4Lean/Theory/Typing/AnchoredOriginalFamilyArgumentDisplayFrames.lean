import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyArgumentPair
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericDisplay
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichFrameDiagonal

/-! The ordinary C frames at an actual queried owner and the independently
checked family parameter. Source-tail equations determine both realizations;
no source certificate is moved or reflected to manufacture these frames. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

noncomputable def OriginalRichDisplayFrame.ofFrame
    (display : EndpointDisplay sourceEnv U displayed expression assigned)
    (common : Subst)
    (frame : OriginalRichFrame sourceEnv env U registry target display.context locals σ σ available)
    (substitutions : Ctx.SubstEq env U target σ σ display.source)
    (realization : display.sourceSubst common = σ) :
    OriginalRichDisplayFrame env registry target display common locals available := by
  cases realization
  exact ⟨frame, substitutions⟩

theorem OriginalRichDisplayFrame.ofFrame_cost
    (display : EndpointDisplay sourceEnv U displayed expression assigned)
    (common : Subst)
    (frame : OriginalRichFrame sourceEnv env U registry target display.context locals σ σ available)
    (substitutions : Ctx.SubstEq env U target σ σ display.source)
    (realization : display.sourceSubst common = σ) (ordered : sourceEnv.Ordered) :
    (ofFrame display common frame substitutions realization).cost ordered =
      (Closure.close (display.node.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost := by
  cases realization
  rfl

noncomputable def RichQueryOccurrence.sourceDisplayFrame
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (entry : RichQueryOccurrence root initialContext env registry target ordered initialEnvironment rootLeft rootRight) :
    OriginalRichDisplayFrame env registry target entry.sourceDisplay entry.left entry.locals entry.available :=
  .ofFrame entry.sourceDisplay entry.left entry.occurrence.frame.leftDiagonal entry.occurrence.substitutions.left
    (by simp [EndpointDisplay.sourceSubst, RichQueryOccurrence.sourceDisplay, EndpointDisplay.identity])

theorem RichQueryOccurrence.sourceDisplayFrame_cost
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (entry : RichQueryOccurrence root initialContext env registry target ordered initialEnvironment rootLeft rootRight) :
    entry.sourceDisplayFrame.cost ordered =
      (Closure.close (entry.node.dependencyOrigin ordered)
        (entry.occurrence.frame.dependencyEnvironment ordered)).cost := by
  rw [sourceDisplayFrame, OriginalRichDisplayFrame.ofFrame_cost, OriginalRichFrame.dependencyEnvironment_leftDiagonal]
  rfl

noncomputable def RichQueryOccurrence.argumentDisplayFrame
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (entry : RichQueryOccurrence root initialContext env registry target ordered initialEnvironment rootLeft rootRight)
    (major : EndpointRef sourceEnv U source majorExpression (mkApps (.const name levels) arguments))
    (index : Nat) (selected : arguments[index]? = some argument)
    (expressionEq : entry.expression = argument.lift' (.skipN .refl entry.location.binderPrefix.length))
    (frame : OriginalRichFrame sourceEnv env U registry target
      ((assignedFamilyApplication major index selected).argument.location.contextDerivation initialContext)
      argumentLocals rootLeft rootRight argumentAvailable)
    (substitutions : Ctx.SubstEq env U target rootLeft rootRight source) :
    OriginalRichDisplayFrame env registry target (entry.familyArgumentDisplay major index selected expressionEq)
      entry.left argumentLocals argumentAvailable :=
  .ofFrame (entry.familyArgumentDisplay major index selected expressionEq) entry.left frame.leftDiagonal
    substitutions.left entry.sourceTail.left

theorem RichQueryOccurrence.argumentDisplayFrame_cost
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (entry : RichQueryOccurrence root initialContext env registry target ordered initialEnvironment rootLeft rootRight)
    (major : EndpointRef sourceEnv U source majorExpression (mkApps (.const name levels) arguments))
    (index : Nat) (selected : arguments[index]? = some argument)
    (expressionEq : entry.expression = argument.lift' (.skipN .refl entry.location.binderPrefix.length))
    (frame : OriginalRichFrame sourceEnv env U registry target
      ((assignedFamilyApplication major index selected).argument.location.contextDerivation initialContext)
      argumentLocals rootLeft rootRight argumentAvailable)
    (substitutions : Ctx.SubstEq env U target rootLeft rootRight source) :
    (entry.argumentDisplayFrame major index selected expressionEq frame substitutions).cost ordered =
      (Closure.close ((assignedFamilyApplication major index selected).view.argument.dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost := by
  rw [argumentDisplayFrame, OriginalRichDisplayFrame.ofFrame_cost, OriginalRichFrame.dependencyEnvironment_leftDiagonal]
  rfl

/-- Feed an actual ordinary-display C answer directly to the fixed query
call in `compareFamilyParameter`. The destination stays at the original
unweakened argument formation, with its existing source resources. -/
theorem RichQueryOccurrence.argumentCoherenceTransfer
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (entry : RichQueryOccurrence root initialContext env registry target ordered initialEnvironment rootLeft rootRight)
    (major : EndpointRef sourceEnv U source majorExpression (mkApps (.const name levels) arguments))
    (index : Nat) (selected : arguments[index]? = some argument)
    (expressionEq : entry.expression = argument.lift' (.skipN .refl entry.location.binderPrefix.length))
    (frame : OriginalRichFrame sourceEnv env U registry target
      ((assignedFamilyApplication major index selected).argument.location.contextDerivation initialContext)
      argumentLocals rootLeft rootRight argumentAvailable)
    (substitutions : Ctx.SubstEq env U target rootLeft rootRight source)
    (answer : OriginalRichDisplayCoherence entry.sourceDisplayFrame
      (entry.argumentDisplayFrame major index selected expressionEq frame substitutions)) :
    TypeConversion env U target (entry.assigned.subst entry.left)
      ((assignedFamilyApplication major index selected).view.domainExpression.subst rootLeft) ∧
    RichCodeTransfer env U registry target entry.node.typeFormation.node
      (assignedFamilyApplication major index selected).view.argument.typeFormation.node
      entry.locals argumentLocals entry.left rootLeft entry.available argumentAvailable := by
  constructor
  · have path := answer.path
    change TypeConversion env U target (entry.assigned.subst entry.left)
      (((assignedFamilyApplication major index selected).view.domainExpression.lift'
        (.skipN .refl entry.location.binderPrefix.length)).subst entry.left) at path
    simpa only [subst_lift', entry.sourceTail.left] using path
  · have transfer : RichCodeTransfer env U registry target entry.node.typeFormation.node
        (assignedFamilyApplication major index selected).view.argument.typeFormation.node entry.locals argumentLocals
        (entry.sourceDisplay.sourceSubst entry.left)
        ((entry.familyArgumentDisplay major index selected expressionEq).sourceSubst entry.left)
        entry.available argumentAvailable := answer.queries
    have leftEq : entry.sourceDisplay.sourceSubst entry.left = entry.left := by
      simp [EndpointDisplay.sourceSubst, RichQueryOccurrence.sourceDisplay, EndpointDisplay.identity]
    have rightEq : (entry.familyArgumentDisplay major index selected expressionEq).sourceSubst entry.left = rootLeft :=
      entry.sourceTail.left
    rw [leftEq, rightEq] at transfer
    exact @transfer

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
