import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionRichComparison

/-! Construct the ambient certificate of an actually converted projection
before storing its query. The natural formation, conversion source, and
conversion destination remain three distinct original occurrences.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

structure AmbientProjectionCode
    (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    {source : List VExpr} {name : Name} {index : Nat} {major natural assigned : VExpr}
    (head : EndpointState sourceEnv U source (.proj name index major) natural)
    (node : EndpointState sourceEnv U source (.proj name index major) assigned)
    (locals : List Nat) (σ : Subst) (available : Valuation) (support : Profile n) where
  naturalFootprint : Footprint
  naturalCode : RichCert sourceEnv env U registry target head.typeFormation.node
    locals σ true support naturalFootprint
  naturalAvailable : naturalFootprint.Available available
  ambientFootprint : Footprint
  ambientCode : RichCert sourceEnv env U registry target node.typeFormation.node
    locals σ true support ambientFootprint
  ambientAvailable : ambientFootprint.Available available
  bridge : TypeRelated env U registry target (natural.subst σ) (assigned.subst σ) support

/-- A later projection reindex consumes this stored ambient certificate
without rebuilding its conversion route. The consumed syntax is a strict
subterm even if its construction increased the original field-query size. -/
theorem AmbientProjectionCode.ambient_size_lt
    (packet : AmbientProjectionCode sourceEnv env U registry target head node locals σ available support) :
    sizeOf packet.ambientCode < sizeOf packet := by
  cases packet
  simp_wf
  omega

/-- This producer consumes exactly the fixed original child reindex and the
fixed original equality F transfer. Neither is a global rich-F assumption;
the strict calls are proved below against this same conversion occurrence. -/
theorem AmbientProjectionCode.forward
    (henv : env.Ordered)
    (head : EndpointState sourceEnv U source (.proj name index major) A)
    (levelWF : level.WF U)
    (equality : Derivation sourceEnv U source A B (.sort level))
    (certificate : RichCert sourceEnv env U registry target head.typeFormation.node
      locals σ true support footprint)
    (resources : footprint.Available available)
    (toEquality : RichCodeTransfer env U registry target head.typeFormation.node (.ref (.left equality))
      locals locals σ σ available available)
    (equalityForward : RichCodeTransfer env U registry target (.ref (.left equality)) (.ref (.right equality))
      locals locals σ σ available available) :
    Nonempty (AmbientProjectionCode sourceEnv env U registry target head
      (.convert (.forward levelWF equality) head) locals σ available support) := by
  obtain ⟨input⟩ := toEquality certificate resources
  obtain ⟨output⟩ := equalityForward input.certificate input.resources
  exact ⟨{
    naturalFootprint := footprint
    naturalCode := certificate
    naturalAvailable := resources
    ambientFootprint := output.footprint
    ambientCode := output.certificate
    ambientAvailable := output.resources
    bridge := input.related.trans henv output.related }⟩

/-- Reverse-oriented original conversions have the same finite producer;
no inverse certificate or source occurrence is fabricated. -/
theorem AmbientProjectionCode.backward
    (henv : env.Ordered)
    (head : EndpointState sourceEnv U source (.proj name index major) B)
    (levelWF : level.WF U)
    (equality : Derivation sourceEnv U source A B (.sort level))
    (certificate : RichCert sourceEnv env U registry target head.typeFormation.node
      locals σ true support footprint)
    (resources : footprint.Available available)
    (toEquality : RichCodeTransfer env U registry target head.typeFormation.node (.ref (.right equality))
      locals locals σ σ available available)
    (equalityBackward : RichCodeTransfer env U registry target (.ref (.right equality)) (.ref (.left equality))
      locals locals σ σ available available) :
    Nonempty (AmbientProjectionCode sourceEnv env U registry target head
      (.convert (.backward levelWF equality) head) locals σ available support) := by
  obtain ⟨input⟩ := toEquality certificate resources
  obtain ⟨output⟩ := equalityBackward input.certificate input.resources
  exact ⟨{
    naturalFootprint := footprint
    naturalCode := certificate
    naturalAvailable := resources
    ambientFootprint := output.footprint
    ambientCode := output.certificate
    ambientAvailable := output.resources
    bridge := input.related.trans henv output.related }⟩

/-- The child reindex's entire two-original cost is strict, independent of
any increase in the converted certificate's finite query size. -/
theorem converted_projection_reindex_schedule
    (head : EndpointState sourceEnv U source (.proj name index major) A)
    (levelWF : level.WF U)
    (equality : Derivation sourceEnv U source A B (.sort level))
    (captured : List Closure) :
    schedule .coherence
      ((Closure.close head.typeFormation.node.origin captured).cost +
       (Closure.close (EndpointRef.left equality).origin captured).cost) <
    schedule .fundamental
      (Closure.close (EndpointState.convert (.forward levelWF equality) head).origin captured).cost := by
  apply schedule_strict
  have bound := head.typeFormation_cost_le captured
  have strict : (Closure.close head.origin captured).cost +
      (Closure.close equality.origin captured).cost <
      (Closure.close (EndpointState.convert (.forward levelWF equality) head).origin captured).cost := by
    have positive : 0 < 1 + environmentCost captured := by omega
    have weight : head.origin.weight + equality.origin.weight <
        (EndpointState.convert (.forward levelWF equality) head).origin.weight := by
      simp only [EndpointState.origin, EndpointConversion.origin, Origin.weight,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega
    simpa only [Closure.cost, Nat.add_mul] using Nat.mul_lt_mul_of_pos_right weight positive
  exact Nat.lt_of_le_of_lt (Nat.add_le_add_right bound _) strict

theorem converted_projection_equality_schedule
    (head : EndpointState sourceEnv U source (.proj name index major) A)
    (levelWF : level.WF U)
    (equality : Derivation sourceEnv U source A B (.sort level))
    (captured : List Closure) :
    schedule .fundamental (Closure.close equality.origin captured).cost <
    schedule .fundamental
      (Closure.close (EndpointState.convert (.forward levelWF equality) head).origin captured).cost := by
  apply schedule_strict
  exact original_child_same_environment (Origin.rule_child (by simp [EndpointConversion.origin])) captured

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
