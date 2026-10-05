import Lean4Lean.Theory.Typing.AnchoredOriginalLambdaPrefix
import Lean4Lean.Theory.Typing.AnchoredOriginalPiFrames

/-! Computed Pi prefixes and their original domain/body child displays. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

structure PiPrefix
    {node : EndpointState sourceEnv U source (.forallE A expression) assigned} (start : Located root node) where
  view : PiView start
  route : PrefixRoute sourceEnv U source (.forallE A expression) node
    (.pi view.domainWF view.bodyWF view.domain view.body)
  location_eq : route.locate start = view.location

noncomputable def piPrefix
    {node : EndpointState sourceEnv U source (.forallE A expression) assigned}
    (start : Located root node) : PiPrefix start := by
  obtain ⟨type, head, route, normal⟩ := prefixHead node
  cases head with
  | ref reference => exact (reference.primitive_atomic normal).elim
  | convert plan term => exact normal.elim
  | pi hu hv domain body =>
    let location := route.locate start
    have cost : ∀ initial,
        (Closure.close (EndpointState.pi hu hv domain body).origin
          (location.environment initial)).cost ≤
        (Closure.close node.origin (start.environment initial)).cost := by
      intro initial
      rw [show location.environment initial = start.environment initial from
        route.locate_environment start initial]
      exact Nat.mul_le_mul_right _ route.weight_le
    exact ⟨⟨_, _, hu, hv, domain, body, location,
      route.locate_binderPrefix start, cost⟩, route, rfl⟩

structure PiDisplayPrefix
    (display : EndpointDisplay env U displayed (.forallE annotation body) assigned) where
  sourceDomain : VExpr
  sourceBody : VExpr
  source_eq : display.sourceExpression = .forallE sourceDomain sourceBody
  annotation_eq : annotation = sourceDomain.lift' display.map
  body_eq : body = sourceBody.lift' display.map.cons
  selected : PiPrefix (display.provenance.location.castExpression source_eq)

noncomputable def EndpointDisplay.piPrefix
    (display : EndpointDisplay env U displayed (.forallE annotation body) assigned) :
    PiDisplayPrefix display := by
  have shape : ∃ A e, display.sourceExpression = .forallE A e ∧
      annotation = A.lift' display.map ∧ body = e.lift' display.map.cons := by
    have equal := display.expression_eq
    cases h : display.sourceExpression <;> simp only [h, VExpr.lift'] at equal
    all_goals try cases equal
    case forallE A e =>
      exact ⟨A, e, rfl, (VExpr.forallE.inj equal).1, (VExpr.forallE.inj equal).2⟩
  let A := Classical.choose shape
  let e := Classical.choose (Classical.choose_spec shape)
  have equal := (Classical.choose_spec (Classical.choose_spec shape)).1
  have components := (Classical.choose_spec (Classical.choose_spec shape)).2
  exact ⟨A, e, equal, components.1, components.2,
    OriginalEndpointFactor.piPrefix (display.provenance.location.castExpression equal)⟩

noncomputable def PiDisplayPrefix.bodyDisplay
    {display : EndpointDisplay env U displayed (.forallE annotation body) assigned}
    (packet : PiDisplayPrefix display) :
    EndpointDisplay env U (annotation :: displayed) body
      (.sort packet.selected.view.bodyLevel) :=
  packet.selected.view.bodyDisplayAs display.provenance.initial display.insertion
    packet.annotation_eq packet.body_eq

theorem PiDisplayPrefix.context_eq
    {display : EndpointDisplay env U displayed (.forallE annotation body) assigned}
    (packet : PiDisplayPrefix display) :
    packet.selected.view.location.contextDerivation display.provenance.initial = display.context := by
  rw [← packet.selected.location_eq, PrefixRoute.locate_contextDerivation,
    Located.castExpression_contextDerivation, ← display.provenance.context_eq]


noncomputable def PiDisplayPrefix.domainDisplay
    {display : EndpointDisplay env U displayed (.forallE annotation body) assigned}
    (packet : PiDisplayPrefix display) :
    EndpointDisplay env U displayed annotation (.sort packet.selected.view.domainLevel) where
  source := display.source
  sourceExpression := packet.sourceDomain
  sourceType := .sort packet.selected.view.domainLevel
  context := (Located.piDomain packet.selected.view.location).contextDerivation display.provenance.initial
  node := packet.selected.view.domain
  provenance := .ofLocation (.piDomain packet.selected.view.location) display.provenance.initial
  map := display.map
  insertion := display.insertion
  expression_eq := packet.annotation_eq
  type_eq := rfl

noncomputable def PiDisplayPrefix.domainFrame
    {display : EndpointDisplay sourceEnv U displayed (.forallE annotation body) assigned}
    (packet : PiDisplayPrefix display)
    (frame : DisplayFits env registry target display common available locals) :
    DisplayFits env registry target packet.domainDisplay common available locals where
  fits := frame.fits.reorigin packet.domainDisplay.context
  original := frame.fits.reorigin_contextDerivation _
  substitutions := frame.substitutions

theorem PiDisplayPrefix.input_cost
    {display : EndpointDisplay env U displayed (.forallE annotation body) assigned}
    (packet : PiDisplayPrefix display) :
    (Closure.close (display.node.cast packet.source_eq rfl).origin
      ((display.provenance.location.castExpression packet.source_eq).environment display.provenance.initial.closures)).cost =
      display.cost := by
  rw [Located.castExpression_environment, EndpointState.origin_cast,
    ← display.provenance.location.contextDerivation_closures, ← display.provenance.context_eq]
  rfl

theorem PiDisplayPrefix.children_cost_lt
    {display : EndpointDisplay env U displayed (.forallE annotation body) assigned}
    (packet : PiDisplayPrefix display) :
    packet.domainDisplay.cost < display.cost ∧ packet.bodyDisplay.cost < display.cost := by
  have domainBound := binder_domain_cost packet.selected.view.domain.origin
    [packet.selected.view.body.origin] []
    (packet.selected.view.location.environment display.provenance.initial.closures)
  have bodyBound := binder_body_cost (domain := packet.selected.view.domain.origin)
    (bodies := [packet.selected.view.body.origin]) (children := [])
    (body := packet.selected.view.body.origin) (by simp)
    (packet.selected.view.location.environment display.provenance.initial.closures)
  have parentBound := packet.selected.view.cost_le display.provenance.initial.closures
  rw [packet.input_cost] at parentBound
  constructor
  · change (Closure.close packet.selected.view.domain.origin
      ((Located.piDomain packet.selected.view.location).contextDerivation display.provenance.initial).closures).cost < _
    rw [Located.contextDerivation_closures]
    exact Nat.lt_of_lt_of_le domainBound parentBound
  · change (Closure.close packet.selected.view.body.origin
      ((Located.piBody packet.selected.view.location).contextDerivation display.provenance.initial).closures).cost < _
    rw [Located.contextDerivation_closures]
    exact Nat.lt_of_lt_of_le bodyBound parentBound

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
