import Lean4Lean.Theory.Typing.AnchoredOriginalConstantCoherence
import Lean4Lean.Theory.Typing.AnchoredOriginalCoherenceContract

/-! The displayed constant branch computes both original source constants
and their finite conversion prefixes. All semantic calls are actual smaller
original header equalities with their retained context formation spines. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

structure ConstantDisplayPrefix
    (display : EndpointDisplay env U displayed (.const name levels) assigned) where
  source_eq : display.sourceExpression = .const name levels
  selected : ConstantPrefix (display.node.cast source_eq rfl)

noncomputable def EndpointDisplay.constantPrefix
    (display : EndpointDisplay env U displayed (.const name levels) assigned) :
    ConstantDisplayPrefix display := by
  have same : display.sourceExpression = .const name levels :=
    VExpr.lift'_inj.mp display.expression_eq.symm
  exact ⟨same, OriginalEndpointFactor.constantPrefix (display.node.cast same rfl)⟩

abbrev ConstantDisplayPrefix.Fundamentals (env : VEnv) (registry : CanonicalHead.Registry)
    {display : EndpointDisplay sourceEnv U displayed (.const name levels) assigned}
    (packet : ConstantDisplayPrefix display) : Prop :=
  ConstantPrefixCall.Fundamentals env registry packet.selected display.context

/-- Context provenance identifies each call's original closure with the
finite reserve already charged to the displayed endpoint. -/
theorem ConstantDisplayPrefix.call_schedule
    {display : EndpointDisplay sourceEnv U displayed (.const name levels) assigned}
    (packet : ConstantDisplayPrefix display)
    (call : ConstantPrefixCall packet.selected original) (otherCost : Nat) :
    schedule .fundamental
      (Closure.close original.origin (call.contextDerivation display.context).closures).cost <
      schedule .coherence (display.cost + otherCost) := by
  apply schedule_strict
  rw [ConstantPrefixCall.contextDerivation_closures]
  have smaller := call.cost_lt display.context.closures
  simp only [EndpointState.origin_cast] at smaller
  exact Nat.lt_of_lt_of_le smaller (Nat.le_add_right _ _)

/-- Both displayed constants pass through the same literal declaration
header. Empty queries still retain the independent raw conversion path. -/
theorem ConstantDisplayPrefix.compare
    {left : EndpointDisplay leftEnv U displayed (.const name levels) leftAssigned}
    {right : EndpointDisplay rightEnv U displayed (.const name levels) rightAssigned}
    (leftPacket : ConstantDisplayPrefix left) (rightPacket : ConstantDisplayPrefix right)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (leftCalls : leftPacket.Fundamentals env registry)
    (rightCalls : rightPacket.Fundamentals env registry) :
    DisplayCoherence env U registry left right := by
  intro target common available leftLocals rightLocals closed hTarget leftFrame rightFrame
  have path := leftPacket.selected.comparePath henv leftBelow rightBelow hTarget
    leftFrame.substitutions rightFrame.substitutions rightPacket.selected
  refine ⟨?_, ?_⟩
  · simpa only [left.realizedType common, right.realizedType common] using path
  · intro n profile footprint certificate resources
    exact ConstantPrefix.compare henv hscoped leftBelow rightBelow
      left.context right.context (left.sourceValuation_closed closed)
      (right.sourceValuation_closed closed) hTarget
      leftFrame.substitutions rightFrame.substitutions leftFrame.fits rightFrame.fits
      leftPacket.selected rightPacket.selected leftCalls rightCalls left.map right.map common [] rfl rfl
      (fun _ => rfl) (fun _ => rfl) certificate resources

theorem EndpointDisplay.constantCoherence
    (left : EndpointDisplay leftEnv U displayed (.const name levels) leftAssigned)
    (right : EndpointDisplay rightEnv U displayed (.const name levels) rightAssigned)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (leftCalls : left.constantPrefix.Fundamentals env registry)
    (rightCalls : right.constantPrefix.Fundamentals env registry) :
    DisplayCoherence env U registry left right :=
  left.constantPrefix.compare right.constantPrefix henv hscoped leftBelow rightBelow leftCalls rightCalls

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
