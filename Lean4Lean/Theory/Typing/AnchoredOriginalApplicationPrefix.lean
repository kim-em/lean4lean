import Lean4Lean.Theory.Typing.AnchoredOriginalLambdaPrefix
import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationNatural

/-! Computed application prefixes retain the actual function/argument source
occurrences and each endpoint's own original conversion route. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

structure ApplicationPrefix
    {node : EndpointState sourceEnv U source (.app function argument) assigned} (start : Located root node) where
  view : AppView start
  route : PrefixRoute sourceEnv U source (.app function argument) node
    (.app view.domainWF view.bodyWF view.domain view.codomain view.function view.argument view.result)
  location_eq : route.locate start = view.location

noncomputable def applicationPrefix
    {node : EndpointState sourceEnv U source (.app function argument) assigned}
    (start : Located root node) : ApplicationPrefix start := by
  obtain ⟨type, head, route, normal⟩ := prefixHead node
  cases head with
  | ref reference => exact (reference.primitive_atomic normal).elim
  | convert plan term => exact normal.elim
  | app hu hv domain codomain function argument result =>
    let location := route.locate start
    have cost : ∀ initial,
        (Closure.close (EndpointState.app hu hv domain codomain function argument result).origin
          (location.environment initial)).cost ≤
        (Closure.close node.origin (start.environment initial)).cost := by
      intro initial
      rw [show location.environment initial = start.environment initial from
        route.locate_environment start initial]
      exact Nat.mul_le_mul_right _ route.weight_le
    exact ⟨⟨_, _, _, _, hu, hv, domain, codomain, function, argument, result, location,
      route.locate_binderPrefix start, cost⟩, route, rfl⟩

structure ApplicationDisplayPrefix
    (display : EndpointDisplay env U displayed (.app function argument) assigned) where
  sourceFunction : VExpr
  sourceArgument : VExpr
  source_eq : display.sourceExpression = .app sourceFunction sourceArgument
  function_eq : function = sourceFunction.lift' display.map
  argument_eq : argument = sourceArgument.lift' display.map
  selected : ApplicationPrefix (display.provenance.location.castExpression source_eq)

noncomputable def EndpointDisplay.applicationPrefix
    (display : EndpointDisplay env U displayed (.app function argument) assigned) :
    ApplicationDisplayPrefix display := by
  have shape : ∃ f a, display.sourceExpression = .app f a ∧
      function = f.lift' display.map ∧ argument = a.lift' display.map := by
    have equal := display.expression_eq
    cases h : display.sourceExpression <;> simp only [h, VExpr.lift'] at equal
    all_goals try cases equal
    case app f a =>
      exact ⟨f, a, rfl, (VExpr.app.inj equal).1, (VExpr.app.inj equal).2⟩
  let f := Classical.choose shape
  let a := Classical.choose (Classical.choose_spec shape)
  have equal := (Classical.choose_spec (Classical.choose_spec shape)).1
  have components := (Classical.choose_spec (Classical.choose_spec shape)).2
  exact ⟨f, a, equal, components.1, components.2,
    OriginalEndpointFactor.applicationPrefix (display.provenance.location.castExpression equal)⟩

noncomputable def ApplicationDisplayPrefix.functionDisplay
    {display : EndpointDisplay env U displayed (.app function argument) assigned}
    (packet : ApplicationDisplayPrefix display) :
    EndpointDisplay env U displayed function
      ((VExpr.forallE packet.selected.view.domainExpression packet.selected.view.codomainExpression).lift' display.map) :=
  packet.selected.view.functionDisplayAs display.provenance.initial display.insertion packet.function_eq

theorem ApplicationDisplayPrefix.context_eq
    {display : EndpointDisplay env U displayed (.app function argument) assigned}
    (packet : ApplicationDisplayPrefix display) :
    packet.selected.view.location.contextDerivation display.provenance.initial = display.context := by
  rw [← packet.selected.location_eq, PrefixRoute.locate_contextDerivation,
    Located.castExpression_contextDerivation, ← display.provenance.context_eq]

theorem ApplicationDisplayPrefix.input_cost
    {display : EndpointDisplay env U displayed (.app function argument) assigned}
    (packet : ApplicationDisplayPrefix display) :
    (Closure.close (display.node.cast packet.source_eq rfl).origin
      ((display.provenance.location.castExpression packet.source_eq).environment display.provenance.initial.closures)).cost =
      display.cost := by
  rw [Located.castExpression_environment, EndpointState.origin_cast,
    ← display.provenance.location.contextDerivation_closures, ← display.provenance.context_eq]
  rfl

theorem ApplicationDisplayPrefix.functionDisplay_cost_lt
    {display : EndpointDisplay env U displayed (.app function argument) assigned}
    (packet : ApplicationDisplayPrefix display) : packet.functionDisplay.cost < display.cost := by
  have smaller := (OriginalFactorCut.app_children_cost_lt packet.selected.view
    display.provenance.initial.closures).1
  rw [packet.input_cost] at smaller
  change (Closure.close packet.selected.view.function.origin
    ((Located.appFunction packet.selected.view.location).contextDerivation display.provenance.initial).closures).cost < _
  rw [Located.contextDerivation_closures]
  exact smaller

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
