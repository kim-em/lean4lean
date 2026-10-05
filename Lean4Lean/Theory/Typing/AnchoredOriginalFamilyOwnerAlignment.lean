import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyArgumentAlignment
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyArgumentSchedule

/-! Composition at the same requested support. Interpreting a queried owner
does not require a second fundamental call on the family parameter to guess
a matching support. The actual two-occurrence comparison supplies its exact
assigned certificate, and the retained target values agree by source tails. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

noncomputable def RichQueryOccurrence.fieldOwner
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (entry : RichQueryOccurrence field initialContext env registry target ordered initialEnvironment rootLeft rootRight) :
    HeaderOwner field major :=
  .inl ⟨entry.context, entry.expression, entry.assigned, entry.node, entry.location⟩

/-- Reuse the owner's paired value at the second original occurrence. The
support is definitionally unchanged; only its actual assigned certificate is
the output of the smaller same-expression comparison. -/
noncomputable def RichQueryOccurrence.familyArgumentValue
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (henv : env.Ordered)
    (entry : RichQueryOccurrence root initialContext env registry target ordered initialEnvironment rootLeft rootRight)
    (major : EndpointRef sourceEnv U source majorExpression
      (mkApps (.const name levels) arguments))
    (index : Nat) (selected : arguments[index]? = some argument)
    (expressionEq : entry.expression = argument.lift' (.skipN .refl entry.location.binderPrefix.length))
    (value : RichBinderValue sourceEnv env U registry target entry.node entry.locals entry.left entry.right
      entry.available entry.profile)
    (comparison : RichCodeTransferResult env U registry target entry.node.typeFormation.node
      (assignedFamilyApplication major index selected).view.argument.typeFormation.node argumentLocals
      entry.left rootLeft argumentAvailable true value.support) :
    RichBinderValue sourceEnv env U registry target (assignedFamilyApplication major index selected).view.argument
      argumentLocals rootLeft rootRight argumentAvailable entry.profile where
  support := value.support
  footprint := comparison.footprint
  certificate := comparison.certificate
  resources := comparison.resources
  typed := value.typed
  related := by
    have related := value.related.convert henv value.typed comparison.related
    rw [(entry.capture_realizations expressionEq).1,
      (entry.capture_realizations expressionEq).2] at related
    exact related

/-- Compose actual comparison outputs, preserving the original owner's
query, support and source occurrence. The second alignment's exact-value
equation prevents a different natural support from entering this chain. -/
noncomputable def RichQueryOccurrence.familyHeaderAlignment
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    (henv : env.Ordered)
    (entry : RichQueryOccurrence field initialContext env registry target ordered initialEnvironment rootLeft rootRight)
    (major : EndpointRef sourceEnv U source majorExpression
      (mkApps (.const name levels) arguments))
    (index : Nat) (selected : arguments[index]? = some argument)
    (expressionEq : entry.expression = argument.lift' (.skipN .refl entry.location.binderPrefix.length))
    (value : RichBinderValue sourceEnv env U registry target entry.node entry.locals entry.left entry.right
      entry.available entry.profile)
    (comparison : RichCodeTransferResult env U registry target entry.node.typeFormation.node
      (assignedFamilyApplication major index selected).view.argument.typeFormation.node argumentLocals
      entry.left rootLeft argumentAvailable true value.support)
    (comparisonPath : TypeConversion env U target (entry.assigned.subst entry.left)
      ((assignedFamilyApplication major index selected).view.domainExpression.subst rootLeft))
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    (declared : HeaderValueAlignment
      ((assignedFamilyApplication major index selected).headerOwner (field := field)) domain env registry target
      argumentLocals headerLocals rootLeft rootRight declaredLeft argumentAvailable headerAvailable entry.profile)
    (exactValue : declared.value = entry.familyArgumentValue henv major index selected expressionEq value comparison) :
    HeaderValueAlignment (entry.fieldOwner (major := major)) domain env registry target
      entry.locals headerLocals entry.left entry.right declaredLeft entry.available headerAvailable entry.profile := by
  have supportEq : declared.value.support = value.support := congrArg RichBinderValue.support exactValue
  exact {
    value := value
    aligned := {
      footprint := declared.aligned.footprint
      certificate := supportEq ▸ declared.aligned.certificate
      resources := declared.aligned.resources
      related := comparison.related.trans henv (supportEq ▸ declared.aligned.related) }
    path := comparisonPath.trans declared.path }

/-- The exact assigned-type induction call used by the parameter bridge.
Both displayed endpoints and frames are already computed from original
locations. Its strict bound is proved from the original projection, not
supplied by the caller. The global two-typing induction remains the source
of this fixed-pair clause. -/
theorem RichQueryOccurrence.compareFamilyParameter
    (sourceOrdered : sourceEnv.Ordered)
    (registered : sourceEnv.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (parameterCount : params.length = info.nparams)
    (indexCount : indices.length = info.nindices)
    (selected : info.fieldType name levels params index sourceMajor = some fieldType)
    (fieldWF : fieldLevel.WF U)
    (field : EndpointRef sourceEnv U source fieldType (.sort fieldLevel))
    (major : Derivation sourceEnv U source sourceMajor majorExpression
      (mkApps (.const name levels) (params ++ indices)))
    (closed : info.ctorType.Closed)
    (allowed : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero)
    (initialContext : ContextDerivation sourceEnv U source)
    (frame : OriginalRichFrame sourceEnv env U registry target initialContext argumentLocals
      rootLeft rootRight argumentAvailable)
    (substitutions : Ctx.SubstEq env U target rootLeft rootRight source)
    (entry : RichQueryOccurrence field initialContext env registry target sourceOrdered
      (frame.dependencyEnvironment sourceOrdered) rootLeft rootRight)
    (argumentIndex : Nat) (argumentSelected : (params ++ indices)[argumentIndex]? = some argument)
    (expressionEq : entry.expression = argument.lift' (.skipN .refl entry.location.binderPrefix.length))
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    (headerLocals : List Nat) (declaredLeft : Subst) (headerAvailable : Valuation)
    (value : RichBinderValue sourceEnv env U registry target entry.node entry.locals entry.left entry.right
      entry.available entry.profile)
    (coherence :
      richSchedule .assignedComparison
        ((Closure.close (entry.node.dependencyOrigin sourceOrdered)
          (entry.occurrence.frame.dependencyEnvironment sourceOrdered)).cost +
         (Closure.close ((assignedFamilyApplication (.left major) argumentIndex argumentSelected).view.argument.dependencyOrigin sourceOrdered)
          ((frame.assignedFamilyArgument sourceOrdered (.left major) argumentIndex argumentSelected substitutions).frame.dependencyEnvironment sourceOrdered)).cost) <
      richSchedule .fundamental
        (Closure.close ((EndpointState.proj registered levelsWF levelCount parameterCount indexCount selected
          fieldWF (.ref field) major closed allowed).dependencyOrigin sourceOrdered)
          (frame.dependencyEnvironment sourceOrdered)).cost →
      TypeConversion env U target (entry.assigned.subst entry.left)
        ((assignedFamilyApplication (.left major) argumentIndex argumentSelected).view.domainExpression.subst rootLeft) ∧
      RichCodeTransfer env U registry target entry.node.typeFormation.node
        (assignedFamilyApplication (.left major) argumentIndex argumentSelected).view.argument.typeFormation.node
        entry.locals argumentLocals entry.left rootLeft entry.available argumentAvailable) :
    ∃ comparison : RichCodeTransferResult env U registry target entry.node.typeFormation.node
        (assignedFamilyApplication (.left major) argumentIndex argumentSelected).view.argument.typeFormation.node
        argumentLocals entry.left rootLeft argumentAvailable true value.support,
      TypeConversion env U target (entry.assigned.subst entry.left)
        ((assignedFamilyApplication (.left major) argumentIndex argumentSelected).view.domainExpression.subst rootLeft) := by
  let pending := entry.pendingField (major := .left major) domain headerLocals declaredLeft headerAvailable expressionEq
  have bound := pending.projection_argument_coherence_schedule sourceOrdered registered levelsWF levelCount
    parameterCount indexCount selected fieldWF field major closed allowed initialContext argumentIndex argumentSelected
    (frame.assignedFamilyArgument sourceOrdered (.left major) argumentIndex argumentSelected substitutions)
  obtain ⟨path, transfer⟩ := coherence bound
  obtain ⟨comparison⟩ := transfer value.certificate value.resources
  exact ⟨comparison, path⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
