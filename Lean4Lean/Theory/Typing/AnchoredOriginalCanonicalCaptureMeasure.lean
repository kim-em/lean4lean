import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalConstApplication
import Lean4Lean.Theory.Typing.EquationWorldClosureOrder

/-! The mixed canonical/caller application edge in the closure-world order.
Both original proof costs are computed here. An arbitrarily large canonical
original can retain the actual proper caller argument without a joined world
or a product bound on the canonical proof size. This does not construct the
semantic capture frame or its hereditary world envelope. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
open OriginalEndpointFactor EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CanonicalConstApplicationAt

theorem capturedOpeningDecrease
    {function : EndpointRef sourceEnv U source (.const name levels) (.forallE A B)}
    {argument : EndpointState sourceEnv U source a A}
    (query : CanonicalConstApplicationAt sourceEnv env U registry target strata
      function argument locals σ available key output relevant)
    (ordered : sourceEnv.Ordered)
    {context : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (domain : EndpointState sourceEnv U source A (.sort u))
    (codomain : EndpointState sourceEnv U (A :: source) B (.sort v))
    (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (canonical : EndpointState query.functionQuery.owner.selected.origin.source U
      canonicalContext canonicalExpression canonicalType)
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length) (fuel : Nat → Nat)
    (bounded : WithinAbove cutoff fuel query.depth)
    (ambient : List (EquationWorldClosureOrder.World strata.rules.length)) :
    let captured := frame.dependencyEnvironment ordered
    let argumentClosure := Closure.close (argument.dependencyOrigin ordered) captured
    let argumentKey := EquationControlMeasure.key strata.rules.length cutoff fuel ordered.constantCount
      (richSchedule .fundamental argumentClosure.cost)
    let parentKey := EquationControlMeasure.key strata.rules.length cutoff fuel ordered.constantCount
      (applicationSchedule (function := function) (argument := argument)
        ordered domain codomain result hu hv captured)
    let canonicalKey := EquationControlMeasure.key strata.rules.length
      (query.functionQuery.owner.selected.ordinal - 1)
      (fun control => query.functionQuery.query.stratifiedDepth (strata.headOrdinal registry) control)
      query.functionQuery.owner.selected.origin.ordered.constantCount
      (richSchedule .fundamental (Closure.close
        (canonical.dependencyOrigin query.functionQuery.owner.selected.origin.ordered)
        [argumentClosure]).cost)
    EquationWorldClosureOrder.CallBelow strata.rules.length
      [.node canonicalKey (.node argumentKey ambient :: ambient), .node argumentKey ambient]
      [.node parentKey ambient] := by
  dsimp only
  have functionBound : WithinAbove cutoff fuel query.functionQuery.chargeDepth :=
    fun control above => Nat.le_trans (Nat.le_max_left _ _) (bounded control above)
  have proper := argument_schedule (function := function) (argument := argument) ordered domain codomain result hu hv
    (frame.dependencyEnvironment ordered)
  apply EquationWorldClosureOrder.split_call
  intro child member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append] using
      EquationWorldClosureOrder.opening_with_caller_captures
        query.functionQuery.owner.selected.ordinal_pos
        query.functionQuery.owner.selected.ordinal_le cutoffBound functionBound
        ordered.constantCount
        (applicationSchedule (function := function) (argument := argument)
          ordered domain codomain result hu hv (frame.dependencyEnvironment ordered))
        query.functionQuery.owner.selected.origin.ordered.constantCount
        (richSchedule .fundamental (Closure.close
          (canonical.dependencyOrigin query.functionQuery.owner.selected.origin.ordered)
          [Closure.close (argument.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)]).cost)
        [richSchedule .fundamental
          (Closure.close (argument.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost]
        (fun cost member => by simpa only [List.mem_singleton.mp member] using proper) ambient
  · exact EquationWorldClosureOrder.original_child proper strata.rules.length cutoff fuel
      ordered.constantCount ambient

end CanonicalConstApplicationAt
end Lean4Lean.AnchoredSource.Adapted
