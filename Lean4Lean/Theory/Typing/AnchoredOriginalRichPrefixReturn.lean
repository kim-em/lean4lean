import Lean4Lean.Theory.Typing.AnchoredOriginalRichConstantPrefix

/-! Restore rich assigned-code answers along an actual original prefix.
The left endpoint and realization may belong to another source environment.
Only retained equality children and exact formation reindex calls are used. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.DirectPrefixRoute
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalRecordSource OriginalTail
set_option backward.isDefEq.respectTransparency false

private theorem conversion_pair
    (ordered : sourceEnv.Ordered) (captured : List Closure)
    (original : Derivation sourceEnv U source A B (.sort level))
    (term : EndpointState sourceEnv U source expression assigned) :
    (Closure.close (term.typeFormation.node.dependencyOrigin ordered) captured).cost +
      (Closure.close (original.dependencyOrigin ordered) captured).cost <
    (Closure.close (.rule [term.dependencyOrigin ordered, original.dependencyOrigin ordered]) captured).cost := by
  apply Nat.lt_of_le_of_lt (Nat.add_le_add_right (term.typeFormation_dependency_cost_le ordered captured) _)
  exact original_two_children _ _ [] captured

theorem restoreCode
    (henv : env.Ordered) (ordered : sourceEnv.Ordered) (captured : List Closure)
    {first : EndpointState sourceEnv U source expression assigned}
    {last : EndpointState sourceEnv U source expression natural}
    (route : DirectPrefixRoute sourceEnv U source expression first last)
    (calls : route.RestoreCalls env registry target ordered captured locals τ available)
    {left : EndpointState leftEnv U leftSource leftExpression (.sort leftLevel)}
    (answer : RichCodeTransferResult env U registry target left last.typeFormation.node
      locals σ τ available relevant profile) :
    Nonempty (RichCodeTransferResult env U registry target left first.typeFormation.node
      locals σ τ available relevant profile) := by
  induction route with
  | done node => exact ⟨answer⟩
  | expose reference rest ih =>
    obtain ⟨tail⟩ := ih calls.2 answer
    rcases reference.exposure_formation_cost_reserve ordered captured with same | smaller
    · exact ⟨{
        footprint := tail.footprint
        certificate := by
          change RichCert sourceEnv env U registry target reference.typeFormation.node locals τ relevant profile tail.footprint
          exact same ▸ tail.certificate
        resources := tail.resources
        related := tail.related }⟩
    · obtain ⟨changed⟩ := calls.1 (richSchedule_strict smaller _ _) tail.certificate tail.resources
      exact ⟨{ changed with related := tail.related.trans henv changed.related }⟩
  | forward wf original term rest ih =>
    obtain ⟨tail⟩ := ih calls.2.2 answer
    obtain ⟨input⟩ := calls.1 (richSchedule_strict (conversion_pair ordered captured original term) _ _)
      tail.certificate tail.resources
    have child := richSchedule_strict
      (original_child_same_environment
        (show (original.dependencyOrigin ordered).weight <
          (Origin.rule [term.dependencyOrigin ordered, original.dependencyOrigin ordered]).weight from
          Origin.rule_child (by simp)) captured) RichPhase.fundamental RichPhase.fundamental
    obtain ⟨output⟩ := calls.2.1 child input.certificate input.resources
    exact ⟨{ output with related := tail.related.trans henv (input.related.trans henv output.related) }⟩
  | backward wf original term rest ih =>
    obtain ⟨tail⟩ := ih calls.2.2 answer
    obtain ⟨input⟩ := calls.1 (richSchedule_strict (conversion_pair ordered captured original term) _ _)
      tail.certificate tail.resources
    have child := richSchedule_strict
      (original_child_same_environment
        (show (original.dependencyOrigin ordered).weight <
          (Origin.rule [term.dependencyOrigin ordered, original.dependencyOrigin ordered]).weight from
          Origin.rule_child (by simp)) captured) RichPhase.fundamental RichPhase.fundamental
    obtain ⟨output⟩ := calls.2.1 child input.certificate input.resources
    exact ⟨{ output with related := tail.related.trans henv (input.related.trans henv output.related) }⟩

/-- Compose both concrete prefix ledgers around a fixed natural-head code
comparison. Neither source context, realization, nor available valuation is
identified with the other one. -/
theorem compareCode
    (henv : env.Ordered) (lf : leftEnv.Ordered) (rf : rightEnv.Ordered)
    (leftCaptured rightCaptured : List Closure)
    {left : EndpointState leftEnv U leftSource leftExpression leftAssigned}
    {leftHead : EndpointState leftEnv U leftSource leftExpression leftNatural}
    {right : EndpointState rightEnv U rightSource rightExpression rightAssigned}
    {rightHead : EndpointState rightEnv U rightSource rightExpression rightNatural}
    (leftRoute : DirectPrefixRoute leftEnv U leftSource leftExpression left leftHead)
    (rightRoute : DirectPrefixRoute rightEnv U rightSource rightExpression right rightHead)
    (leftCalls : leftRoute.PeelCalls env registry target lf leftCaptured leftLocals σ leftAvailable)
    (rightCalls : rightRoute.RestoreCalls env registry target rf rightCaptured rightLocals τ rightAvailable)
    (natural : RichCodeTransfer env U registry target leftHead.typeFormation.node rightHead.typeFormation.node
      leftLocals rightLocals σ τ leftAvailable rightAvailable) :
    RichCodeTransfer env U registry target left.typeFormation.node right.typeFormation.node
      leftLocals rightLocals σ τ leftAvailable rightAvailable := by
  apply leftRoute.peelCode henv lf leftCaptured leftCalls
  intro relevant n profile footprint certificate resources
  obtain ⟨answer⟩ := natural certificate resources
  exact rightRoute.restoreCode henv rf rightCaptured rightCalls answer

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.DirectPrefixRoute
