import Lean4Lean.Theory.Typing.AnchoredOriginalRichValueInduction
import Lean4Lean.Theory.Typing.AnchoredOriginalRichTypeFormationMeasure

/-! Restore the assigned support of an explicit original conversion. The
source type formation, original equality source, and original equality target
remain distinct occurrences. Exactly one smaller same-expression R and one
smaller original equality F produce the output certificate. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

private theorem formation_equality_bound
    (ordered : sourceEnv.Ordered)
    (term : EndpointState sourceEnv U source expression A)
    (equality : Derivation sourceEnv U source left right (.sort level))
    (captured : List Closure) :
    (Closure.close (term.typeFormation.node.dependencyOrigin ordered) captured).cost +
      (Closure.close (equality.dependencyOrigin ordered) captured).cost <
    (Closure.close (.rule [term.dependencyOrigin ordered, equality.dependencyOrigin ordered]) captured).cost := by
  apply Nat.lt_of_le_of_lt (Nat.add_le_add_right (term.typeFormation_dependency_cost_le ordered captured) _)
  exact original_two_children _ _ [] captured

/-- The supplied F channel is the actual retained equality derivation, not
a conversion callback for an arbitrary pair of raw source types. -/
theorem RichSupportedValue.convertForward
    (henv : env.Ordered) (ordered : sourceEnv.Ordered) (captured : List Closure)
    (levelWF : level.WF U)
    (equality : Derivation sourceEnv U source A B (.sort level))
    {term : EndpointState sourceEnv U source expression A}
    (answer : RichSupportedValue sourceEnv env U registry target term locals σ τ available profile)
    (typeR : richSchedule .expressionReindex
        ((Closure.close (term.typeFormation.node.dependencyOrigin ordered) captured).cost +
         (Closure.close (equality.dependencyOrigin ordered) captured).cost) <
      richSchedule .fundamental
        (Closure.close ((EndpointState.convert (.forward levelWF equality) term).dependencyOrigin ordered) captured).cost →
      RichCodeTransfer env U registry target term.typeFormation.node (.ref (.left equality))
        locals locals σ σ available available)
    (equalityF : richSchedule .fundamental
        (Closure.close (equality.dependencyOrigin ordered) captured).cost <
      richSchedule .fundamental
        (Closure.close ((EndpointState.convert (.forward levelWF equality) term).dependencyOrigin ordered) captured).cost →
      RichCodeTransfer env U registry target (.ref (.left equality)) (.ref (.right equality))
        locals locals σ σ available available) :
    Nonempty (RichSupportedValue sourceEnv env U registry target
      (.convert (.forward levelWF equality) term) locals σ τ available profile) := by
  obtain ⟨input⟩ := typeR (richSchedule_strict (formation_equality_bound ordered term equality captured) _ _)
    answer.certificate answer.resources
  obtain ⟨output⟩ := equalityF
    (richSchedule_strict (original_child_same_environment (Origin.rule_child (by simp [EndpointConversion.dependencyOrigin])) captured) _ _)
    input.certificate input.resources
  have bridge := input.related.trans henv output.related
  exact ⟨{
    support := answer.support
    footprint := output.footprint
    certificate := output.certificate
    resources := output.resources
    typed := answer.typed
    related := Related.convert henv answer.typed bridge answer.related
    typeCode := TypeRelated.left_diagonal (TypeRelated.symm henv answer.typed.wf_type bridge) }⟩

/-- Backward original equalities use their retained right source endpoint
and left destination endpoint, with the same checked two-child reserve. -/
theorem RichSupportedValue.convertBackward
    (henv : env.Ordered) (ordered : sourceEnv.Ordered) (captured : List Closure)
    (levelWF : level.WF U)
    (equality : Derivation sourceEnv U source A B (.sort level))
    {term : EndpointState sourceEnv U source expression B}
    (answer : RichSupportedValue sourceEnv env U registry target term locals σ τ available profile)
    (typeR : richSchedule .expressionReindex
        ((Closure.close (term.typeFormation.node.dependencyOrigin ordered) captured).cost +
         (Closure.close (equality.dependencyOrigin ordered) captured).cost) <
      richSchedule .fundamental
        (Closure.close ((EndpointState.convert (.backward levelWF equality) term).dependencyOrigin ordered) captured).cost →
      RichCodeTransfer env U registry target term.typeFormation.node (.ref (.right equality))
        locals locals σ σ available available)
    (equalityF : richSchedule .fundamental
        (Closure.close (equality.dependencyOrigin ordered) captured).cost <
      richSchedule .fundamental
        (Closure.close ((EndpointState.convert (.backward levelWF equality) term).dependencyOrigin ordered) captured).cost →
      RichCodeTransfer env U registry target (.ref (.right equality)) (.ref (.left equality))
        locals locals σ σ available available) :
    Nonempty (RichSupportedValue sourceEnv env U registry target
      (.convert (.backward levelWF equality) term) locals σ τ available profile) := by
  obtain ⟨input⟩ := typeR (richSchedule_strict (formation_equality_bound ordered term equality captured) _ _)
    answer.certificate answer.resources
  obtain ⟨output⟩ := equalityF
    (richSchedule_strict (original_child_same_environment (Origin.rule_child (by simp [EndpointConversion.dependencyOrigin])) captured) _ _)
    input.certificate input.resources
  have bridge := input.related.trans henv output.related
  exact ⟨{
    support := answer.support
    footprint := output.footprint
    certificate := output.certificate
    resources := output.resources
    typed := answer.typed
    related := Related.convert henv answer.typed bridge answer.related
    typeCode := TypeRelated.left_diagonal (TypeRelated.symm henv answer.typed.wf_type bridge) }⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
