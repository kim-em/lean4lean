import Lean4Lean.Theory.Typing.AnchoredOriginalLambdaPrefix
import Lean4Lean.Theory.Typing.AnchoredOriginalPrefixReturn

/-! The complete displayed lambda branch, including the actual original
conversion prefixes on both endpoints. Recursive premises refer only to the
fixed source children selected by the two retained prefix packets. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

structure LambdaDisplayPrefix.Fundamentals (env : VEnv) (registry : CanonicalHead.Registry)
    {display : EndpointDisplay sourceEnv U displayed (.lam annotation body) assigned}
    (packet : LambdaDisplayPrefix display) : Prop where
  conversions : PrefixCall.Fundamentals env registry packet.selected.route display.context
  domain : StateFundamental env registry
    (packet.selected.view.location.contextDerivation display.provenance.initial) packet.selected.view.domain
  codomain : StateFundamental env registry
    ((Located.lamCodomain packet.selected.view.location).contextDerivation display.provenance.initial)
    packet.selected.view.codomain

/-- The body call is strictly smaller as an original pair, independently of
future target worlds, query rank, or the number of retained rows. -/
theorem LambdaDisplayPrefix.body_pair_schedule
    {left : EndpointDisplay leftEnv U displayed (.lam annotation body) leftAssigned}
    {right : EndpointDisplay rightEnv U displayed (.lam annotation body) rightAssigned}
    (leftPacket : LambdaDisplayPrefix left) (rightPacket : LambdaDisplayPrefix right) :
    schedule .coherence (leftPacket.bodyDisplay.cost + rightPacket.bodyDisplay.cost) <
      schedule .coherence (left.cost + right.cost) := by
  apply schedule_strict
  exact Nat.add_lt_add leftPacket.bodyDisplay_cost_lt rightPacket.bodyDisplay_cost_lt

/-- Every retained conversion equality is an actual smaller original F call. -/
theorem LambdaDisplayPrefix.conversion_schedule
    {display : EndpointDisplay sourceEnv U displayed (.lam annotation body) assigned}
    (packet : LambdaDisplayPrefix display)
    (call : PrefixCall packet.selected.route original) (otherCost : Nat) :
    schedule .fundamental
      (Closure.close original.origin (call.contextDerivation display.context).closures).cost <
    schedule .coherence (display.cost + otherCost) := by
  apply schedule_strict
  rw [PrefixCall.contextDerivation_closures]
  have smaller := call.cost_lt display.context.closures
  simp only [EndpointState.origin_cast] at smaller
  exact Nat.lt_of_lt_of_le smaller (Nat.le_add_right _ _)

theorem LambdaDisplayPrefix.formation_schedule
    {display : EndpointDisplay sourceEnv U displayed (.lam annotation body) assigned}
    (packet : LambdaDisplayPrefix display) (otherCost : Nat) :
    schedule .fundamental (Closure.close packet.selected.view.domain.origin
      (packet.selected.view.location.contextDerivation display.provenance.initial).closures).cost <
      schedule .coherence (display.cost + otherCost) ∧
    schedule .fundamental (Closure.close packet.selected.view.codomain.origin
      ((Located.lamCodomain packet.selected.view.location).contextDerivation display.provenance.initial).closures).cost <
      schedule .coherence (display.cost + otherCost) := by
  have result := packet.selected.view.formation_schedule display.provenance.initial otherCost
  rw [Located.castExpression_environment,
    ← display.provenance.location.contextDerivation_closures,
    ← display.provenance.context_eq, EndpointState.origin_cast] at result
  exact result

/-- Complete the lambda branch of DisplayCoherence from its fixed smaller
original calls. Prefix selection, domain/body display agreement, fresh-neutral
raw comparison and every finite row/frame are computed from the endpoints. -/
theorem LambdaDisplayPrefix.compare
    {left : EndpointDisplay leftEnv U displayed (.lam annotation body) leftAssigned}
    {right : EndpointDisplay rightEnv U displayed (.lam annotation body) rightAssigned}
    (leftPacket : LambdaDisplayPrefix left) (rightPacket : LambdaDisplayPrefix right)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (leftF : leftPacket.Fundamentals env registry)
    (rightF : rightPacket.Fundamentals env registry)
    (bodyIH : DisplayCoherence env U registry leftPacket.bodyDisplay rightPacket.bodyDisplay) :
    DisplayCoherence env U registry left right := by
  intro target common available leftLocals rightLocals closed hTarget leftFrame rightFrame
  have leftClosed := left.sourceValuation_closed closed
  have rightClosed := right.sourceValuation_closed closed
  have naturalPath := LamView.naturalPath leftPacket.selected.view rightPacket.selected.view
    left.provenance.initial right.provenance.initial left.insertion right.insertion
    leftPacket.annotation_eq rightPacket.annotation_eq leftPacket.body_eq rightPacket.body_eq
    henv leftBelow rightBelow bodyIH closed hTarget leftFrame.fits rightFrame.fits
    leftFrame.substitutions rightFrame.substitutions
  have path := PrefixRoute.comparePath henv leftBelow rightBelow hTarget
    leftFrame.substitutions rightFrame.substitutions
    leftPacket.selected.route rightPacket.selected.route naturalPath
  refine ⟨?_, ?_⟩
  · simpa only [left.realizedType common, right.realizedType common] using path
  · intro n profile footprint certificate resources
    apply PrefixRoute.compareHeadsOriginal henv hscoped leftBelow rightBelow
      left.context right.context leftClosed rightClosed hTarget
      leftFrame.substitutions rightFrame.substitutions leftFrame.fits rightFrame.fits
      leftPacket.selected.route rightPacket.selected.route leftF.conversions rightF.conversions
      (certificate := certificate) (resources := resources)
    intro required natural incoming
    exact LamView.naturalQueries leftPacket.selected.view rightPacket.selected.view
      left.provenance.initial right.provenance.initial left.insertion right.insertion
      leftPacket.annotation_eq rightPacket.annotation_eq leftPacket.body_eq rightPacket.body_eq
      henv hscoped leftBelow rightBelow bodyIH closed hTarget leftFrame.fits rightFrame.fits
      leftFrame.substitutions rightFrame.substitutions leftF.domain leftF.codomain rightF.domain rightF.codomain
      natural incoming

/-- The public branch computes both actual prefix packets itself. -/
theorem EndpointDisplay.lambdaCoherence
    (left : EndpointDisplay leftEnv U displayed (.lam annotation body) leftAssigned)
    (right : EndpointDisplay rightEnv U displayed (.lam annotation body) rightAssigned)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (leftF : left.lambdaPrefix.Fundamentals env registry)
    (rightF : right.lambdaPrefix.Fundamentals env registry)
    (bodyIH : DisplayCoherence env U registry left.lambdaPrefix.bodyDisplay right.lambdaPrefix.bodyDisplay) :
    DisplayCoherence env U registry left right :=
  left.lambdaPrefix.compare right.lambdaPrefix henv hscoped leftBelow rightBelow leftF rightF bodyIH

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
