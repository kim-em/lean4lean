import Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilySourceSpine
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls

/-! Actual family source parsing with the finite argument liveness calls
paid by their proper original application descendants. These are qualified
unary original F clauses. A complete controlled bank must additionally keep
the query-owned world sponsors on those same answers. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

/-- The argument is a proper actual application child; its location can
cross conversion wrappers but does not replace its original proof. -/
theorem RichAppOrigin.argumentWorldBelow
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (origin : RichAppOrigin root env registry target source locals σ f a)
    (controls : OriginalWorldControls strata sourceEnv)
    (captured : WorldEnvironmentProvenance strata U environment) (phase : RichPhase) :
    CallBelow strata.rules.length
      [originalCallWorld controls .fundamental origin.argumentNode captured]
      [originalCallWorld controls phase (.ref root) captured] := by
  have child :
      (Closure.close (origin.argumentNode.dependencyOrigin controls.ordered) environment).cost <
      (Closure.close ((EndpointState.app origin.hu origin.hv origin.domain origin.codomain
        origin.functionNode origin.argumentNode origin.result).dependencyOrigin controls.ordered) environment).cost := by
    apply Nat.lt_of_lt_of_le _ (application_cost_le_captured _ _ _ _ _ _)
    exact binder_other_cost (by simp) environment
  have parent := Nat.mul_le_mul_right (1 + environmentCost environment)
    (origin.location.dependency_weight_le controls.ordered)
  have strict := Nat.lt_of_lt_of_le child parent
  apply split_call
  intro world member
  cases List.mem_singleton.mp member
  exact original_child (richSchedule_strict strict _ _) _ _ _ _ _

/-- Only the actual original argument observation is submitted to F. There
is no family-domain or consumed-header result in this lower-call clause. -/
def RichFamilySourceArgumentCalls
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (controls : OriginalWorldControls strata sourceEnv)
    (captured : WorldEnvironmentProvenance strata U environment) (phase : RichPhase)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation) : Prop :=
  ∀ {f a} (origin : RichAppOrigin root env registry target source locals σ f a),
    CallBelow strata.rules.length
      [originalCallWorld controls .fundamental origin.argumentNode captured]
      [originalCallWorld controls phase (.ref root) captured] →
    origin.argumentFootprint.Available available →
    Nonempty (RichComputationalValue sourceEnv env U registry target origin.argumentNode
      locals σ σ available origin.rawInput)

theorem RetainedRichFamilySpine.argumentsLiveOfCalls
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (controls : OriginalWorldControls strata sourceEnv)
    (captured : WorldEnvironmentProvenance strata U environment) (phase : RichPhase)
    (spine : RetainedRichFamilySpine root env registry target locals σ name levels expression atom footprint)
    (resources : footprint.Available available)
    (calls : RichFamilySourceArgumentCalls (root := root) controls captured phase env registry target locals σ available) :
    spine.ArgumentsLive := by
  induction spine with
  | constant => trivial
  | app origin function path included ih =>
    have all : (origin.functionFootprint ++ origin.argumentFootprint).Available available :=
      fun i need member => resources i need (included member)
    obtain ⟨answer⟩ := calls origin (origin.argumentWorldBelow controls captured phase)
      (fun i need member => all i need (List.mem_append_right _ member))
    exact ⟨ih (fun i need member => all i need (List.mem_append_left _ member)),
      answer.related.live henv hscoped formed⟩

/-- Parsing and consumption use the SAME original query and seed packet.
No liveness premise or family alignment answer is supplied by the caller. -/
theorem RichObs.consumeRetainedFamily
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (controls : OriginalWorldControls strata sourceEnv) (below : sourceEnv ≤ env)
    (captured : WorldEnvironmentProvenance strata U environment) (phase : RichPhase)
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned}
    {demand : Profile n}
    (query : RichObs sourceEnv env U registry target node locals σ demand footprint)
    (location : Located root node)
    (head : expression.getAppFnArgs.1 = .const name levels)
    (member : atom ∈ demand.atoms) (ends : FamilyEndDemand atom)
    (resources : footprint.Available available)
    (calls : RichFamilySourceArgumentCalls (root := root) controls captured phase env registry target locals σ available) :
    Nonempty (RetainedRichFamilyConsumption root env registry target locals σ available
      name levels expression.getAppFnArgs.2 atom) := by
  obtain ⟨spine⟩ := query.familySourceSpine henv hscoped formed controls.ordered below
    notDefinition notNative location head member ends
  obtain ⟨result, _⟩ := spine.consume henv hscoped below formed resources
    (spine.argumentsLiveOfCalls henv hscoped formed controls captured phase resources calls)
  exact ⟨result⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
