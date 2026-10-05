import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationPrefix
import Lean4Lean.Theory.Typing.AnchoredOriginalPrefixReturn

/-! Complete displayed application coherence, with both original conversion
prefixes restored. All semantic premises name fixed smaller original calls. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

structure ApplicationComparisonCalls (env : VEnv) (registry : CanonicalHead.Registry)
    {left : EndpointDisplay leftEnv U displayed (.app function argument) leftAssigned}
    {right : EndpointDisplay rightEnv U displayed (.app function argument) rightAssigned}
    (leftPacket : ApplicationDisplayPrefix left) (rightPacket : ApplicationDisplayPrefix right) : Prop where
  leftConversions : PrefixCall.Fundamentals env registry leftPacket.selected.route left.context
  rightConversions : PrefixCall.Fundamentals env registry rightPacket.selected.route right.context
  argument : StateFundamental env registry
    ((Located.appArgument leftPacket.selected.view.location).contextDerivation left.provenance.initial)
    leftPacket.selected.view.argument
  rightDomain : StateFundamental env registry
    (rightPacket.selected.view.location.contextDerivation right.provenance.initial) rightPacket.selected.view.domain
  rightCodomain : StateFundamental env registry
    ((Located.appCodomain rightPacket.selected.view.location).contextDerivation right.provenance.initial)
    rightPacket.selected.view.codomain
  functionTypes : DisplayCoherence env U registry leftPacket.functionDisplay rightPacket.functionDisplay

theorem ApplicationDisplayPrefix.function_pair_schedule
    {left : EndpointDisplay leftEnv U displayed (.app function argument) leftAssigned}
    {right : EndpointDisplay rightEnv U displayed (.app function argument) rightAssigned}
    (leftPacket : ApplicationDisplayPrefix left) (rightPacket : ApplicationDisplayPrefix right) :
    schedule .coherence (leftPacket.functionDisplay.cost + rightPacket.functionDisplay.cost) <
      schedule .coherence (left.cost + right.cost) := by
  apply schedule_strict
  exact Nat.add_lt_add leftPacket.functionDisplay_cost_lt rightPacket.functionDisplay_cost_lt

theorem ApplicationDisplayPrefix.conversion_schedule
    {display : EndpointDisplay sourceEnv U displayed (.app function argument) assigned}
    (packet : ApplicationDisplayPrefix display)
    (call : PrefixCall packet.selected.route original) (otherCost : Nat) :
    schedule .fundamental
      (Closure.close original.origin (call.contextDerivation display.context).closures).cost <
    schedule .coherence (display.cost + otherCost) := by
  apply schedule_strict
  rw [PrefixCall.contextDerivation_closures]
  have smaller := call.cost_lt display.context.closures
  simp only [EndpointState.origin_cast] at smaller
  exact Nat.lt_of_lt_of_le smaller (Nat.le_add_right _ _)

theorem ApplicationDisplayPrefix.argument_schedule
    {display : EndpointDisplay sourceEnv U displayed (.app function argument) assigned}
    (packet : ApplicationDisplayPrefix display) (otherCost : Nat) :
    schedule .fundamental (Closure.close packet.selected.view.argument.origin
      ((Located.appArgument packet.selected.view.location).contextDerivation display.provenance.initial).closures).cost <
      schedule .coherence (display.cost + otherCost) := by
  apply schedule_strict
  rw [Located.contextDerivation_closures]
  have child := binder_other_cost (domain := packet.selected.view.domain.origin)
    (bodies := [packet.selected.view.codomain.origin])
    (children := [packet.selected.view.function.origin, packet.selected.view.argument.origin,
      packet.selected.view.result.origin])
    (child := packet.selected.view.argument.origin) (by simp)
    (packet.selected.view.location.environment display.provenance.initial.closures)
  have smaller := Nat.lt_of_lt_of_le child (packet.selected.view.cost_le display.provenance.initial.closures)
  rw [packet.input_cost] at smaller
  exact Nat.lt_of_lt_of_le smaller (Nat.le_add_right _ _)

theorem ApplicationDisplayPrefix.formation_schedule
    {display : EndpointDisplay sourceEnv U displayed (.app function argument) assigned}
    (packet : ApplicationDisplayPrefix display) (otherCost : Nat) :
    schedule .fundamental (Closure.close packet.selected.view.domain.origin
      (packet.selected.view.location.contextDerivation display.provenance.initial).closures).cost <
      schedule .coherence (display.cost + otherCost) ∧
    schedule .fundamental (Closure.close packet.selected.view.codomain.origin
      ((Located.appCodomain packet.selected.view.location).contextDerivation display.provenance.initial).closures).cost <
      schedule .coherence (display.cost + otherCost) := by
  rw [Located.contextDerivation_closures, Located.contextDerivation_closures]
  obtain ⟨_, domainBound, bodyBound⟩ := OriginalFactorCut.app_children_cost_lt packet.selected.view
    display.provenance.initial.closures
  rw [packet.input_cost] at domainBound bodyBound
  constructor <;> apply schedule_strict
  · exact Nat.lt_of_lt_of_le domainBound (Nat.le_add_right _ _)
  · exact Nat.lt_of_lt_of_le bodyBound (Nat.le_add_right _ _)

/-- Actual left prefix replay, natural application comparison, and actual
right restoration form the full displayed application C branch. -/
theorem ApplicationDisplayPrefix.compare
    {left : EndpointDisplay leftEnv U displayed (.app function argument) leftAssigned}
    {right : EndpointDisplay rightEnv U displayed (.app function argument) rightAssigned}
    (leftPacket : ApplicationDisplayPrefix left) (rightPacket : ApplicationDisplayPrefix right)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (calls : ApplicationComparisonCalls env registry leftPacket rightPacket) :
    DisplayCoherence env U registry left right := by
  intro target common available leftLocals rightLocals closed hTarget leftFrame rightFrame
  have leftClosed := left.sourceValuation_closed closed
  have rightClosed := right.sourceValuation_closed closed
  have sameArgument := leftPacket.argument_eq.symm.trans rightPacket.argument_eq
  have naturalPath := AppView.naturalPath leftPacket.selected.view rightPacket.selected.view
    left.provenance.initial right.provenance.initial left.insertion right.insertion
    leftPacket.function_eq rightPacket.function_eq sameArgument henv hscoped leftBelow rightBelow
    calls.argument calls.functionTypes calls.rightDomain calls.rightCodomain closed hTarget
    leftFrame.fits rightFrame.fits leftFrame.substitutions rightFrame.substitutions
  have path := PrefixRoute.comparePath henv leftBelow rightBelow hTarget
    leftFrame.substitutions rightFrame.substitutions
    leftPacket.selected.route rightPacket.selected.route naturalPath
  refine ⟨?_, ?_⟩
  · simpa only [left.realizedType common, right.realizedType common] using path
  · intro n profile footprint certificate resources
    apply PrefixRoute.compareHeadsOriginal henv hscoped leftBelow rightBelow
      left.context right.context leftClosed rightClosed hTarget
      leftFrame.substitutions rightFrame.substitutions leftFrame.fits rightFrame.fits
      leftPacket.selected.route rightPacket.selected.route calls.leftConversions calls.rightConversions
      (certificate := certificate) (resources := resources)
    intro required natural incoming
    exact (AppView.naturalComparison leftPacket.selected.view rightPacket.selected.view
      left.provenance.initial right.provenance.initial left.insertion right.insertion
      leftPacket.function_eq rightPacket.function_eq sameArgument henv hscoped leftBelow rightBelow
      calls.argument calls.functionTypes calls.rightDomain calls.rightCodomain closed hTarget
      leftFrame.fits rightFrame.fits leftFrame.substitutions rightFrame.substitutions natural incoming).2

theorem EndpointDisplay.applicationCoherence
    (left : EndpointDisplay leftEnv U displayed (.app function argument) leftAssigned)
    (right : EndpointDisplay rightEnv U displayed (.app function argument) rightAssigned)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (calls : ApplicationComparisonCalls env registry left.applicationPrefix right.applicationPrefix) :
    DisplayCoherence env U registry left right :=
  left.applicationPrefix.compare right.applicationPrefix henv hscoped leftBelow rightBelow calls

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
