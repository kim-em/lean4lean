import Lean4Lean.Theory.Typing.AnchoredOriginalVariableCoherence
import Lean4Lean.Theory.Typing.AnchoredOriginalLambdaPrefix

/-! The complete displayed variable branch. Natural types agree by context
lookup; their code semantics comes from the actual left formation child.
Both assigned-type conversion routes use only smaller original equalities. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

structure VariablePrefix
    {node : EndpointState sourceEnv U source (.bvar index) assigned} (start : Located root node) where
  view : BVarView start
  route : PrefixRoute sourceEnv U source (.bvar index) node
    (.bvar view.lookup view.levelWF view.formation)
  location_eq : route.locate start = view.location

noncomputable def variablePrefix
    {node : EndpointState sourceEnv U source (.bvar index) assigned}
    (start : Located root node) : VariablePrefix start := by
  obtain ⟨type, head, route, normal⟩ := prefixHead node
  cases head with
  | ref reference => exact (reference.primitive_atomic normal).elim
  | convert plan term => exact normal.elim
  | bvar lookup levelWF formation =>
    let location := route.locate start
    have cost : ∀ initial,
        (Closure.close (EndpointState.bvar lookup levelWF formation).origin
          (location.environment initial)).cost ≤
        (Closure.close node.origin (start.environment initial)).cost := by
      intro initial
      rw [show location.environment initial = start.environment initial from
        route.locate_environment start initial]
      exact Nat.mul_le_mul_right _ route.weight_le
    exact ⟨⟨_, _, lookup, levelWF, formation, location,
      route.locate_binderPrefix start, cost⟩, route, rfl⟩

structure VariableDisplayPrefix
    (display : EndpointDisplay env U displayed (.bvar index) assigned) where
  sourceIndex : Nat
  source_eq : display.sourceExpression = .bvar sourceIndex
  expression_eq : VExpr.bvar index = (VExpr.bvar sourceIndex).lift' display.map
  selected : VariablePrefix (display.provenance.location.castExpression source_eq)

noncomputable def EndpointDisplay.variablePrefix
    (display : EndpointDisplay env U displayed (.bvar index) assigned) :
    VariableDisplayPrefix display := by
  have shape : ∃ i, display.sourceExpression = .bvar i := by
    have equal := display.expression_eq
    cases h : display.sourceExpression <;> simp only [h, VExpr.lift'] at equal
    all_goals try cases equal
    case bvar i => exact ⟨i, rfl⟩
  let i := Classical.choose shape
  have equal := Classical.choose_spec shape
  exact ⟨i, equal, display.expression_eq.trans (congrArg (fun e => e.lift' display.map) equal),
    OriginalEndpointFactor.variablePrefix (display.provenance.location.castExpression equal)⟩

structure VariableDisplayPrefix.Fundamentals (env : VEnv) (registry : CanonicalHead.Registry)
    {display : EndpointDisplay sourceEnv U displayed (.bvar index) assigned}
    (packet : VariableDisplayPrefix display) : Prop where
  conversions : PrefixCall.Fundamentals env registry packet.selected.route display.context
  formation : StateFundamental env registry
    (packet.selected.view.location.contextDerivation display.provenance.initial) packet.selected.view.formation

theorem VariableDisplayPrefix.formation_schedule
    {display : EndpointDisplay sourceEnv U displayed (.bvar index) assigned}
    (packet : VariableDisplayPrefix display) (otherCost : Nat) :
    schedule .fundamental (Closure.close packet.selected.view.formation.origin
      (packet.selected.view.location.contextDerivation display.provenance.initial).closures).cost <
      schedule .coherence (display.cost + otherCost) := by
  apply schedule_strict
  rw [Located.contextDerivation_closures]
  have smaller := packet.selected.view.formation_cost_lt display.provenance.initial.closures
  rw [Located.castExpression_environment,
    ← display.provenance.location.contextDerivation_closures,
    ← display.provenance.context_eq, EndpointState.origin_cast] at smaller
  exact Nat.lt_of_lt_of_le smaller (Nat.le_add_right _ _)

theorem VariableDisplayPrefix.conversion_schedule
    {display : EndpointDisplay sourceEnv U displayed (.bvar index) assigned}
    (packet : VariableDisplayPrefix display)
    (call : PrefixCall packet.selected.route original) (otherCost : Nat) :
    schedule .fundamental
      (Closure.close original.origin (call.contextDerivation display.context).closures).cost <
    schedule .coherence (display.cost + otherCost) := by
  apply schedule_strict
  rw [PrefixCall.contextDerivation_closures]
  have smaller := call.cost_lt display.context.closures
  simp only [EndpointState.origin_cast] at smaller
  exact Nat.lt_of_lt_of_le smaller (Nat.le_add_right _ _)

theorem VariableDisplayPrefix.compare
    {left : EndpointDisplay leftEnv U displayed (.bvar index) leftAssigned}
    {right : EndpointDisplay rightEnv U displayed (.bvar index) rightAssigned}
    (leftPacket : VariableDisplayPrefix left) (rightPacket : VariableDisplayPrefix right)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (leftF : leftPacket.Fundamentals env registry)
    (rightConversions : PrefixCall.Fundamentals env registry rightPacket.selected.route right.context) :
    DisplayCoherence env U registry left right := by
  intro target common available leftLocals rightLocals closed hTarget leftFrame rightFrame
  have leftClosed := left.sourceValuation_closed closed
  have rightClosed := right.sourceValuation_closed closed
  have same := leftPacket.expression_eq.symm.trans rightPacket.expression_eq
  have naturalPath := displayedLookupTypes_path (env := env) (U := U) (target := target)
    leftPacket.selected.view.lookup rightPacket.selected.view.lookup left.insertion right.insertion same
    (common := common) rfl rfl
  have path := PrefixRoute.comparePath henv leftBelow rightBelow hTarget
    leftFrame.substitutions rightFrame.substitutions
    leftPacket.selected.route rightPacket.selected.route naturalPath
  refine ⟨?_, ?_⟩
  · simpa only [left.realizedType common, right.realizedType common] using path
  · intro n profile footprint certificate resources
    apply PrefixRoute.compareHeadsOriginal henv hscoped leftBelow rightBelow
      left.context right.context leftClosed rightClosed hTarget
      leftFrame.substitutions rightFrame.substitutions leftFrame.fits rightFrame.fits
      leftPacket.selected.route rightPacket.selected.route leftF.conversions rightConversions
      (certificate := certificate) (resources := resources)
    intro required natural incoming
    have formation : GradedTransfer env U registry target leftLocals (left.sourceSubst common)
        (left.sourceSubst common) (left.sourceValuation available)
        leftPacket.selected.view.sourceType leftPacket.selected.view.sourceType
        (.sort leftPacket.selected.view.level) :=
      (leftF.formation target leftLocals _ _ _ leftClosed hTarget leftFrame.substitutions
        (TailPairedFits.diagonal
          (leftPacket.selected.view.location.contextDerivation left.provenance.initial) leftFrame.fits)).1
    obtain ⟨answer⟩ := natural.transfer_graded henv hscoped hTarget leftClosed formation incoming
    exact leftPacket.selected.view.compareNatural rightPacket.selected.view
      left.insertion right.insertion same rfl rfl (fun _ => rfl) (fun _ => rfl) [] rightLocals answer

theorem EndpointDisplay.variableCoherence
    (left : EndpointDisplay leftEnv U displayed (.bvar index) leftAssigned)
    (right : EndpointDisplay rightEnv U displayed (.bvar index) rightAssigned)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (leftF : left.variablePrefix.Fundamentals env registry)
    (rightConversions : PrefixCall.Fundamentals env registry right.variablePrefix.selected.route right.context) :
    DisplayCoherence env U registry left right :=
  left.variablePrefix.compare right.variablePrefix henv hscoped leftBelow rightBelow leftF rightConversions

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
