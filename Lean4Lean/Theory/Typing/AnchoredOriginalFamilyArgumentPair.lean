import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyApplicationLineage
import Lean4Lean.Theory.Typing.AnchoredOriginalRichQueryCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalDisplay

/-! A queried parameter occurrence and the independently checked parameter
in an actual assigned-family formation have the same displayed expression.
Their assigned types remain separate. The second occurrence retains its
enclosing application, original context, and actual semantic source frame. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

noncomputable def assignedFamilyApplication
    (major : EndpointRef sourceEnv U source majorExpression
      (mkApps (.const name levels) arguments))
    (index : Nat) (selected : arguments[index]? = some argument) :
    SpineApplication major source [] argument :=
  familyApplication (.assignedFormation .here) index selected

theorem assignedFamilyApplication_context
    (major : EndpointRef sourceEnv U source majorExpression
      (mkApps (.const name levels) arguments))
    (index : Nat) (selected : arguments[index]? = some argument)
    (initial : ContextDerivation sourceEnv U source) :
    (assignedFamilyApplication major index selected).argument.location.contextDerivation initial = initial := by
  exact spineApplication_context arguments (.assignedFormation (.here (root := major))) index selected initial

private theorem Located.dependencyEnvironment_of_prefix_nil
    (ordered : sourceEnv.Ordered)
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U context expression assigned}
    (location : Located root node) (empty : location.binderPrefix = [])
    (initial : List Closure) : location.dependencyEnvironment ordered initial = initial := by
  induction location with
  | here => rfl
  | expose parent ih | convertTerm parent ih | appFunction parent ih | appArgument parent ih
  | appDomain parent ih | appResult parent ih | lamDomain parent ih | piDomain parent ih
  | projField parent ih | projMajor parent ih | assignedFormation parent ih | appPiFormation parent ih => exact ih empty
  | lamBody parent _ | lamCodomain parent _ | appCodomain parent _ | piBody parent _ => cases empty

theorem assignedFamilyApplication_dependencyEnvironment
    (ordered : sourceEnv.Ordered)
    (major : EndpointRef sourceEnv U source majorExpression
      (mkApps (.const name levels) arguments))
    (index : Nat) (selected : arguments[index]? = some argument) (initial : List Closure) :
    (assignedFamilyApplication major index selected).argument.location.dependencyEnvironment ordered initial =
      initial :=
  (assignedFamilyApplication major index selected).argument.location.dependencyEnvironment_of_prefix_nil
    ordered (assignedFamilyApplication major index selected).argument.prefix_eq initial

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

private theorem OriginalRichFrame.cast_environment
    {first second : ContextDerivation sourceEnv U source}
    (equal : first = second)
    (frame : OriginalRichFrame sourceEnv env U registry target first locals σ τ available)
    (ordered : sourceEnv.Ordered) :
    (equal ▸ frame : OriginalRichFrame sourceEnv env U registry target second locals σ τ available).dependencyEnvironment ordered =
      frame.dependencyEnvironment ordered := by
  cases equal
  rfl

/-- Select the second actual occurrence using the major's existing frame.
Only equality of the original context derivations is used to transport it. -/
noncomputable def OriginalRichFrame.assignedFamilyArgument
    (ordered : sourceEnv.Ordered)
    (major : EndpointRef sourceEnv U source majorExpression
      (mkApps (.const name levels) arguments))
    (index : Nat) (selected : arguments[index]? = some argument)
    {initial : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target initial locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source) :
    OriginalRichOccurrenceFrame (assignedFamilyApplication major index selected).argument.location
      initial env registry target locals σ τ available ordered (frame.dependencyEnvironment ordered) := by
  have same := assignedFamilyApplication_context major index selected initial
  refine ⟨same.symm ▸ frame, substitutions, ?_⟩
  rw [assignedFamilyApplication_dependencyEnvironment, OriginalRichFrame.cast_environment]
  exact Nat.le_refl _

/-- The cut's own assigned type and original source frame are retained. -/
noncomputable def RichQueryOccurrence.sourceDisplay
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (entry : RichQueryOccurrence root initialContext env registry target ordered initialEnvironment rootLeft rootRight) :
    EndpointDisplay sourceEnv U entry.context entry.expression entry.assigned :=
  .identity (entry.location.contextDerivation initialContext) entry.node
    (.ofLocation entry.location initialContext)

/-- Display the independently checked parameter under exactly the binders
of the discovered query. This is delayed weakening of an actual occurrence,
not a reconstructed source typing derivation. -/
noncomputable def RichQueryOccurrence.familyArgumentDisplay
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (entry : RichQueryOccurrence root initialContext env registry target ordered initialEnvironment rootLeft rootRight)
    (major : EndpointRef sourceEnv U source majorExpression
      (mkApps (.const name levels) arguments))
    (index : Nat) (selected : arguments[index]? = some argument)
    (expressionEq : entry.expression = argument.lift' (.skipN .refl entry.location.binderPrefix.length)) :
    EndpointDisplay sourceEnv U entry.context entry.expression
      ((assignedFamilyApplication major index selected).view.domainExpression.lift'
        (.skipN .refl entry.location.binderPrefix.length)) where
  source := source
  sourceExpression := argument
  sourceType := (assignedFamilyApplication major index selected).view.domainExpression
  context := (assignedFamilyApplication major index selected).argument.location.contextDerivation initialContext
  node := (assignedFamilyApplication major index selected).view.argument
  provenance := .ofLocation (assignedFamilyApplication major index selected).argument.location initialContext
  map := .skipN .refl entry.location.binderPrefix.length
  insertion := by
    have insertion : Ctx.Lift' (.skipN .refl entry.location.binderPrefix.length)
        source (entry.location.binderPrefix ++ source) :=
      Ctx.liftN_iff_lift'.mp (.zero entry.location.binderPrefix)
    exact Eq.mpr (congrArg (fun context =>
      Ctx.Lift' (.skipN .refl entry.location.binderPrefix.length) source context)
      entry.location.context_eq) insertion
  expression_eq := expressionEq
  type_eq := rfl

/-- The comparison has identical displayed terms on both sides even when
the two actual source derivations assigned different types to the parameter. -/
theorem RichQueryOccurrence.familyArgument_typings
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (sourceOrdered : sourceEnv.Ordered)
    (entry : RichQueryOccurrence root initialContext env registry target ordered initialEnvironment rootLeft rootRight)
    (major : EndpointRef sourceEnv U source majorExpression
      (mkApps (.const name levels) arguments))
    (index : Nat) (selected : arguments[index]? = some argument)
    (expressionEq : entry.expression = argument.lift' (.skipN .refl entry.location.binderPrefix.length)) :
    sourceEnv.HasType U entry.context entry.expression entry.assigned ∧
    sourceEnv.HasType U entry.context entry.expression
      ((assignedFamilyApplication major index selected).view.domainExpression.lift'
        (.skipN .refl entry.location.binderPrefix.length)) :=
  ⟨entry.sourceDisplay.sound sourceOrdered,
    (entry.familyArgumentDisplay major index selected expressionEq).sound sourceOrdered⟩

/-- Both target values agree with the independently selected original
parameter using the stored source-substitution tails, before type alignment. -/
theorem RichQueryOccurrence.familyArgument_realizations
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (entry : RichQueryOccurrence root initialContext env registry target ordered initialEnvironment rootLeft rootRight)
    (_major : EndpointRef sourceEnv U source majorExpression
      (mkApps (.const name levels) arguments))
    (_index : Nat) (_selected : arguments[_index]? = some argument)
    (expressionEq : entry.expression = argument.lift' (.skipN .refl entry.location.binderPrefix.length)) :
    entry.expression.subst entry.left = argument.subst rootLeft ∧
      entry.expression.subst entry.right = argument.subst rootRight :=
  entry.capture_realizations expressionEq

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
