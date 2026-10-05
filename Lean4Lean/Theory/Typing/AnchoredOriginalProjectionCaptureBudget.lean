import Lean4Lean.Theory.Typing.AnchoredOriginalEndpointFactor

/-! A boundary of the current application schedule. Retaining an original
codomain with its actual argument is sound provenance, but its product cost
cannot generally be charged to the existing ordinary application reserve.
This is an arithmetic obstruction, not a counterexample to typed coherence.
-/
namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure

private def smallOrigin : Origin := .rule []
private def tripleOrigin : Origin := .rule [smallOrigin, smallOrigin]

/-- Even one suspended codomain can exceed an ordinary application's entire
budget. A proof must avoid this recursive call or provide a stronger global
measure; the known-beta product reserve cannot be reused at `appDF`. -/
theorem application_capture_budget_counterexample :
    let domain := smallOrigin
    let codomain := tripleOrigin
    let argument := tripleOrigin
    let function := smallOrigin
    let result := smallOrigin
    (Closure.close (applicationOrigin domain codomain function argument result) []).cost <
      (Closure.close result []).cost +
      (Closure.close codomain
        [.bundle (.close argument []) (.close domain [])]).cost := by
  simp [smallOrigin, tripleOrigin, applicationOrigin, Closure.cost, environmentCost, Origin.weight]

/-- There is no unconditional strengthening of the existing ordinary-app
schedule to the result/captured-codomain coherence pair. -/
theorem no_uniform_application_capture_budget :
    ¬ (∀ domain codomain function argument result : Origin,
      (Closure.close result []).cost +
        (Closure.close codomain [.bundle (.close argument []) (.close domain [])]).cost <
      (Closure.close (applicationOrigin domain codomain function argument result) []).cost) := by
  intro bound
  have h := bound smallOrigin tripleOrigin smallOrigin tripleOrigin smallOrigin
  have reverse := application_capture_budget_counterexample
  exact Nat.lt_asymm h reverse

/-- An isolated candidate reserve, using the already verified typed capture
arithmetic. Production application origins are unchanged. -/
def capturedApplicationOrigin (domain codomain function argument result : Origin) : Origin :=
  .typedBeta domain codomain argument result [function]

theorem capturedApplication_comparison (domain codomain function argument result : Origin)
    (environment : List Closure) :
    (Closure.close result environment).cost +
      (Closure.close codomain
        (.bundle (.close argument environment) (.close domain environment) :: environment)).cost <
      (Closure.close (capturedApplicationOrigin domain codomain function argument result) environment).cost :=
  typed_beta_comparison domain codomain argument result [function] environment

/-- Every pre-existing strict bound below the old application remains strict
below this proposed reserve, including structural F and result/argument C. -/
theorem application_cost_le_captured (domain codomain function argument result : Origin)
    (environment : List Closure) :
    (Closure.close (applicationOrigin domain codomain function argument result) environment).cost ≤
      (Closure.close (capturedApplicationOrigin domain codomain function argument result) environment).cost := by
  have argumentCovered : argument.weight ≤ codomain.weight * argument.weight := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right argument.weight codomain.weight_pos
  apply Nat.mul_le_mul_right
  simp only [applicationOrigin, capturedApplicationOrigin, Origin.weight,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.mul_add, Nat.mul_one, Nat.add_zero]
  omega

/-- Descending into either retained original closure preserves the pair
reserve; no numerical bound is supplied by a caller of the source factor. -/
theorem capturedApplication_descendant_comparison
    (domain codomain function argument result : Origin) (environment : List Closure)
    (selectedResult selectedCodomain : Closure)
    (resultBound : selectedResult.cost ≤ (Closure.close result environment).cost)
    (codomainBound : selectedCodomain.cost ≤
      (Closure.close codomain
        (.bundle (.close argument environment) (.close domain environment) :: environment)).cost) :
    selectedResult.cost + selectedCodomain.cost <
      (Closure.close (capturedApplicationOrigin domain codomain function argument result) environment).cost :=
  Nat.lt_of_le_of_lt (Nat.add_le_add resultBound codomainBound)
    (capturedApplication_comparison domain codomain function argument result environment)

/-- The actual two-tree residual comparison uses original locations on
both sides. Capturing the argument changes only the closure environment;
it never constructs a typing derivation for the residual expression. -/
theorem located_application_capture_comparison
    (domain : EndpointRef env U source A (.sort u))
    (codomain : EndpointRef env U (A :: source) B (.sort v))
    (function : EndpointRef env U source f (.forallE A B))
    (argument : EndpointRef env U source a A)
    (result : EndpointRef env U source (B.inst a) (.sort v))
    {resultNode : EndpointState env U resultContext resultExpression resultType}
    {bodyNode : EndpointState env U bodyContext bodyExpression bodyType}
    (resultLocation : Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.Located result resultNode)
    (bodyLocation : Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.Located codomain bodyNode)
    (environment : List Closure) :
    schedule .coherence
      ((Closure.close resultNode.origin (resultLocation.environment environment)).cost +
       (Closure.close bodyNode.origin (bodyLocation.environment
          (.bundle (.close argument.origin environment) (.close domain.origin environment) :: environment))).cost) <
    schedule .fundamental
      (Closure.close (capturedApplicationOrigin domain.origin codomain.origin function.origin
        argument.origin result.origin) environment).cost := by
  apply schedule_strict
  exact capturedApplication_descendant_comparison domain.origin codomain.origin function.origin
    argument.origin result.origin environment _ _ (resultLocation.cost_le environment)
    (bodyLocation.cost_le _)

end Lean4Lean.AnchoredSource.OriginalClosureMeasure
