import Lean4Lean.Theory.Typing.AnchoredOriginalLambdaNatural
import Lean4Lean.Theory.Typing.AnchoredOriginalTailPrefix

/-! A lambda's actual conversion prefix and natural children share one
original path. Exposure changes neither its binder prefix nor captured tail. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem PrefixRoute.locate_binderPrefix
    (route : PrefixRoute sourceEnv U source expression first last) (start : Located root first) :
    (route.locate start).binderPrefix = start.binderPrefix := by
  induction route with
  | done => rfl
  | expose reference rest ih => exact ih (.expose start)
  | convert plan term rest ih => exact ih (.convertTerm start)

theorem PrefixRoute.locate_environment
    (route : PrefixRoute sourceEnv U source expression first last) (start : Located root first)
    (initial : List Closure) :
    (route.locate start).environment initial = start.environment initial := by
  induction route with
  | done => rfl
  | expose reference rest ih => exact ih (.expose start)
  | convert plan term rest ih => exact ih (.convertTerm start)

theorem PrefixRoute.locate_contextDerivation
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (route : PrefixRoute sourceEnv U source expression first last) (start : Located root first)
    (initial : ContextDerivation sourceEnv U rootSource) :
    (route.locate start).contextDerivation initial = start.contextDerivation initial := by
  induction route with
  | done => rfl
  | expose reference rest ih => exact ih (.expose start)
  | convert plan term rest ih => exact ih (.convertTerm start)

structure LambdaPrefix
    {node : EndpointState sourceEnv U source (.lam A expression) assigned} (start : Located root node) where
  view : LamView start
  route : PrefixRoute sourceEnv U source (.lam A expression) node
    (.lam view.domainWF view.bodyWF view.domain view.codomain view.body)
  location_eq : route.locate start = view.location

noncomputable def lambdaPrefix
    {node : EndpointState sourceEnv U source (.lam A expression) assigned}
    (start : Located root node) : LambdaPrefix start := by
  obtain ⟨type, head, route, normal⟩ := prefixHead node
  cases head with
  | ref reference => exact (reference.primitive_atomic normal).elim
  | convert plan term => exact normal.elim
  | lam hu hv domain codomain body =>
    let location := route.locate start
    have cost : ∀ initial,
        (Closure.close (EndpointState.lam hu hv domain codomain body).origin
          (location.environment initial)).cost ≤
        (Closure.close node.origin (start.environment initial)).cost := by
      intro initial
      rw [show location.environment initial = start.environment initial from
        route.locate_environment start initial]
      exact Nat.mul_le_mul_right _ route.weight_le
    exact ⟨⟨_, _, _, hu, hv, domain, codomain, body, location,
      route.locate_binderPrefix start, cost⟩, route, rfl⟩

def Located.castExpression
    {node : EndpointState env U source expression type}
    (location : Located root node) (equal : expression = expression') :
    Located root (node.cast equal rfl) := by
  cases equal; exact location

theorem Located.castExpression_contextDerivation
    {root : EndpointRef env U rootSource rootExpression rootType}
    {node : EndpointState env U source expression type}
    (location : Located root node) (equal : expression = expression')
    (initial : ContextDerivation env U rootSource) :
    (location.castExpression equal).contextDerivation initial = location.contextDerivation initial := by
  cases equal; rfl

theorem Located.castExpression_environment
    {node : EndpointState env U source expression type}
    (location : Located root node) (equal : expression = expression') (initial : List Closure) :
    (location.castExpression equal).environment initial = location.environment initial := by
  cases equal; rfl

structure LambdaDisplayPrefix
    (display : EndpointDisplay env U displayed (.lam annotation body) assigned) where
  sourceDomain : VExpr
  sourceBody : VExpr
  source_eq : display.sourceExpression = .lam sourceDomain sourceBody
  annotation_eq : annotation = sourceDomain.lift' display.map
  body_eq : body = sourceBody.lift' display.map.cons
  selected : LambdaPrefix (display.provenance.location.castExpression source_eq)

noncomputable def EndpointDisplay.lambdaPrefix
    (display : EndpointDisplay env U displayed (.lam annotation body) assigned) :
    LambdaDisplayPrefix display := by
  have shape : ∃ A e, display.sourceExpression = .lam A e ∧
      annotation = A.lift' display.map ∧ body = e.lift' display.map.cons := by
    have equal := display.expression_eq
    cases h : display.sourceExpression <;> simp only [h, VExpr.lift'] at equal
    all_goals try cases equal
    case lam A e =>
      exact ⟨A, e, rfl, (VExpr.lam.inj equal).1, (VExpr.lam.inj equal).2⟩
  let A := Classical.choose shape
  let e := Classical.choose (Classical.choose_spec shape)
  have equal := (Classical.choose_spec (Classical.choose_spec shape)).1
  have components := (Classical.choose_spec (Classical.choose_spec shape)).2
  exact ⟨A, e, equal, components.1, components.2,
    OriginalEndpointFactor.lambdaPrefix (display.provenance.location.castExpression equal)⟩

noncomputable def LambdaDisplayPrefix.bodyDisplay
    {display : EndpointDisplay env U displayed (.lam annotation body) assigned}
    (packet : LambdaDisplayPrefix display) :
    EndpointDisplay env U (annotation :: displayed) body
      (packet.selected.view.bodyType.lift' display.map.cons) :=
  packet.selected.view.bodyDisplayAs display.provenance.initial display.insertion
    packet.annotation_eq packet.body_eq

theorem LambdaDisplayPrefix.context_eq
    {display : EndpointDisplay env U displayed (.lam annotation body) assigned}
    (packet : LambdaDisplayPrefix display) :
    packet.selected.view.location.contextDerivation display.provenance.initial = display.context := by
  rw [← packet.selected.location_eq, PrefixRoute.locate_contextDerivation,
    Located.castExpression_contextDerivation, ← display.provenance.context_eq]

theorem LambdaDisplayPrefix.bodyDisplay_cost_lt
    {display : EndpointDisplay env U displayed (.lam annotation body) assigned}
    (packet : LambdaDisplayPrefix display) : packet.bodyDisplay.cost < display.cost := by
  have smaller := packet.selected.view.bodyDisplay_cost_lt display.provenance.initial display.insertion
  change packet.bodyDisplay.cost < _ at smaller
  rw [Located.castExpression_environment] at smaller
  rw [← display.provenance.location.contextDerivation_closures,
    ← display.provenance.context_eq] at smaller
  have originEq : (display.node.cast packet.source_eq rfl).origin = display.node.origin := by
    exact EndpointState.origin_cast _ _ _
  rw [originEq] at smaller
  exact smaller

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
