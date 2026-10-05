import Lean4Lean.Theory.Typing.AnchoredOriginalRichQueryOccurrence
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPendingCapture

/-! A discovered whole query becomes a pending capture before its value or
declared-domain alignment is known. Both realized values follow from its
original source match and the exact root substitution tails. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem RichQueryOccurrence.capture_realizations
    {rawCapture : VExpr}
    (entry : RichQueryOccurrence root initialContext env registry target ordered initialEnvironment rootLeft rootRight)
    (expressionEq : entry.expression = rawCapture.lift' (.skipN .refl entry.location.binderPrefix.length)) :
    entry.expression.subst entry.left = rawCapture.subst rootLeft ∧
      entry.expression.subst entry.right = rawCapture.subst rootRight := by
  constructor
  · rw [expressionEq, subst_lift', entry.sourceTail.left]
  · rw [expressionEq, subst_lift', entry.sourceTail.right]

noncomputable def RichQueryOccurrence.pendingField
    {rawCapture : VExpr}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (entry : RichQueryOccurrence field initialContext env registry target ordered initialEnvironment rootLeft rootRight)
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    (headerLocals : List Nat) (declaredLeft : Subst) (headerAvailable : Valuation)
    (expressionEq : entry.expression = rawCapture.lift' (.skipN .refl entry.location.binderPrefix.length)) :
    PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable initialEnvironment rawCapture
      (rawCapture.subst rootLeft) (rawCapture.subst rootRight) where
  owner := .inl ⟨_, _, _, entry.node, entry.location⟩
  ownerLocals := entry.locals
  ownerLeft := entry.left
  ownerRight := entry.right
  ownerAvailable := entry.available
  ownerClosed := entry.closed
  initialContext := initialContext
  frame := entry.occurrence.frame
  substitutions := entry.occurrence.substitutions
  frame_environment_le := fun _ => entry.occurrence.environment_le
  depth := entry.location.binderPrefix.length
  sourcePrefix := entry.location.binderPrefix
  source_eq := entry.location.context_eq
  depth_eq := rfl
  expression_eq := expressionEq
  left_eq := (entry.capture_realizations expressionEq).1
  right_eq := (entry.capture_realizations expressionEq).2
  rank := entry.rank
  input := entry.profile
  footprint := entry.footprint
  query := entry.query
  queryAvailable := entry.resources

noncomputable def RichQueryOccurrence.pendingMajor
    {rawCapture : VExpr}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (entry : RichQueryOccurrence major initialContext env registry target ordered initialEnvironment rootLeft rootRight)
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    (headerLocals : List Nat) (declaredLeft : Subst) (headerAvailable : Valuation)
    (expressionEq : entry.expression = rawCapture.lift' (.skipN .refl entry.location.binderPrefix.length)) :
    PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable initialEnvironment rawCapture
      (rawCapture.subst rootLeft) (rawCapture.subst rootRight) where
  owner := .inr ⟨_, _, _, entry.node, entry.location⟩
  ownerLocals := entry.locals
  ownerLeft := entry.left
  ownerRight := entry.right
  ownerAvailable := entry.available
  ownerClosed := entry.closed
  initialContext := initialContext
  frame := entry.occurrence.frame
  substitutions := entry.occurrence.substitutions
  frame_environment_le := fun _ => entry.occurrence.environment_le
  depth := entry.location.binderPrefix.length
  sourcePrefix := entry.location.binderPrefix
  source_eq := entry.location.context_eq
  depth_eq := rfl
  expression_eq := expressionEq
  left_eq := (entry.capture_realizations expressionEq).1
  right_eq := (entry.capture_realizations expressionEq).2
  rank := entry.rank
  input := entry.profile
  footprint := entry.footprint
  query := entry.query
  queryAvailable := entry.resources

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
