import Lean4Lean.Theory.Typing.AnchoredOriginalLambdaPrefix
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionFields
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionOrigin
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionFactor
import Lean4Lean.Theory.Typing.AnchoredOriginalPrefixReturn

/-! Actual projection comparison occurrences and their strict recursive
schedule. The dependent declared-field comparison is not postulated here.
The hidden major endpoints retain their own original typings, which need
not assign their arguments the declaration's parameter domains. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
open OriginalFactorCut
set_option backward.isDefEq.respectTransparency false

structure ProjectionDisplayPrefix
    (display : EndpointDisplay sourceEnv U displayed (.proj name index major) assigned) where
  sourceMajor : VExpr
  source_eq : display.sourceExpression = .proj name index sourceMajor
  major_eq : major = sourceMajor.lift' display.map
  head : ProjectionHead (display.node.cast source_eq rfl)

noncomputable def EndpointDisplay.projectionPrefix
    (display : EndpointDisplay sourceEnv U displayed (.proj name index major) assigned) :
    ProjectionDisplayPrefix display := by
  have shape : ∃ m, display.sourceExpression = .proj name index m ∧
      major = m.lift' display.map := by
    have equal := display.expression_eq
    cases h : display.sourceExpression <;> simp only [h, VExpr.lift'] at equal
    all_goals try cases equal
    case proj n i m =>
      obtain ⟨rfl, rfl, hm⟩ := VExpr.proj.inj equal
      exact ⟨m, rfl, hm⟩
  let m := Classical.choose shape
  have equal := (Classical.choose_spec shape).1
  exact ⟨m, equal, (Classical.choose_spec shape).2,
    projectionHead (display.node.cast equal rfl)⟩

/-- Capture factoring starts at this actual stored field reference, even
when the enclosing display was reached through synthetic endpoint states. -/
theorem ProjectionDisplayPrefix.field_isReference
    {display : EndpointDisplay sourceEnv U displayed (.proj name index major) assigned}
    (packet : ProjectionDisplayPrefix display) :
    ∃ reference, packet.head.field = .ref reference := by
  have invariant := (packet.head.route.locate
    (display.provenance.location.castExpression packet.source_eq)).originalProjectionFields
  exact invariant.1

noncomputable def ProjectionDisplayPrefix.fieldReference
    {display : EndpointDisplay sourceEnv U displayed (.proj name index major) assigned}
    (packet : ProjectionDisplayPrefix display) :
    EndpointRef sourceEnv U display.source packet.head.fieldType (.sort packet.head.fieldLevel) :=
  Classical.choose packet.field_isReference

theorem ProjectionDisplayPrefix.field_eq
    {display : EndpointDisplay sourceEnv U displayed (.proj name index major) assigned}
    (packet : ProjectionDisplayPrefix display) :
    packet.head.field = .ref packet.fieldReference :=
  Classical.choose_spec packet.field_isReference

/-- The right endpoint of the stored major equality has exactly the
syntactic major of the enclosing projection. Its source type remains the
actual hidden family application. -/
noncomputable def ProjectionDisplayPrefix.majorDisplay
    {display : EndpointDisplay sourceEnv U displayed (.proj name index major) assigned}
    (packet : ProjectionDisplayPrefix display) :
    EndpointDisplay sourceEnv U displayed major
      ((mkApps (.const name packet.head.levels)
        (packet.head.parameters ++ packet.head.indices)).lift' display.map) where
  source := display.source
  sourceExpression := packet.sourceMajor
  sourceType := mkApps (.const name packet.head.levels)
    (packet.head.parameters ++ packet.head.indices)
  context := display.context
  node := .ref (.right packet.head.major)
  provenance := .ofLocation .here display.context
  map := display.map
  insertion := display.insertion
  expression_eq := packet.major_eq
  type_eq := rfl

def ProjectionDisplayPrefix.majorFrame
    {display : EndpointDisplay sourceEnv U displayed (.proj name index major) assigned}
    (packet : ProjectionDisplayPrefix display)
    (frame : DisplayFits env registry target display common available locals) :
    DisplayFits env registry target packet.majorDisplay common available locals :=
  ⟨frame.fits, frame.original, frame.substitutions⟩

theorem ProjectionDisplayPrefix.children_cost_lt
    {display : EndpointDisplay sourceEnv U displayed (.proj name index major) assigned}
    (packet : ProjectionDisplayPrefix display) :
    (Closure.close packet.head.field.origin display.context.closures).cost < display.cost ∧
      packet.majorDisplay.cost < display.cost := by
  have parent := Nat.mul_le_mul_right (1 + environmentCost display.context.closures)
    packet.head.route.weight_le
  simp only [EndpointState.origin_cast] at parent
  constructor
  · exact Nat.lt_of_lt_of_le
      (original_child_same_environment (Origin.rule_child
        (children := [packet.head.field.origin, packet.head.major.origin])
        (by simp)) display.context.closures) parent
  · change (Closure.close packet.head.major.origin display.context.closures).cost < display.cost
    exact Nat.lt_of_lt_of_le
      (original_child_same_environment (Origin.rule_child
        (children := [packet.head.field.origin, packet.head.major.origin])
        (by simp)) display.context.closures) parent

theorem ProjectionDisplayPrefix.info_eq
    {left : EndpointDisplay leftEnv U displayed (.proj name index major) leftAssigned}
    {right : EndpointDisplay rightEnv U displayed (.proj name index major) rightAssigned}
    (leftPacket : ProjectionDisplayPrefix left) (rightPacket : ProjectionDisplayPrefix right)
    (henv : env.Ordered) (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env) :
    leftPacket.head.info = rightPacket.head.info :=
  henv.projections_unique (leftBelow.projections leftPacket.head.registered)
    (rightBelow.projections rightPacket.head.registered)

theorem ProjectionDisplayPrefix.formation_schedule
    {display : EndpointDisplay sourceEnv U displayed (.proj name index major) assigned}
    (packet : ProjectionDisplayPrefix display) (otherCost : Nat) :
    schedule .fundamental (Closure.close packet.fieldReference.origin display.context.closures).cost <
      schedule .coherence (display.cost + otherCost) ∧
    schedule .fundamental (Closure.close packet.head.major.origin display.context.closures).cost <
      schedule .coherence (display.cost + otherCost) := by
  have fieldOrigin : packet.fieldReference.origin = packet.head.field.origin := by
    rw [packet.field_eq]; rfl
  constructor <;> apply schedule_strict
  · rw [fieldOrigin]
    exact Nat.lt_of_lt_of_le packet.children_cost_lt.1 (Nat.le_add_right _ _)
  · exact Nat.lt_of_lt_of_le packet.children_cost_lt.2 (Nat.le_add_right _ _)

theorem ProjectionDisplayPrefix.major_pair_schedule
    {left : EndpointDisplay leftEnv U displayed (.proj name index major) leftAssigned}
    {right : EndpointDisplay rightEnv U displayed (.proj name index major) rightAssigned}
    (leftPacket : ProjectionDisplayPrefix left) (rightPacket : ProjectionDisplayPrefix right) :
    schedule .coherence (leftPacket.majorDisplay.cost + rightPacket.majorDisplay.cost) <
      schedule .coherence (left.cost + right.cost) := by
  apply schedule_strict
  exact Nat.add_lt_add leftPacket.children_cost_lt.2 rightPacket.children_cost_lt.2

theorem ProjectionDisplayPrefix.conversion_schedule
    {display : EndpointDisplay sourceEnv U displayed (.proj name index major) assigned}
    (packet : ProjectionDisplayPrefix display)
    (call : PrefixCall packet.head.route original) (otherCost : Nat) :
    schedule .fundamental
      (Closure.close original.origin (call.contextDerivation display.context).closures).cost <
      schedule .coherence (display.cost + otherCost) := by
  apply schedule_strict
  rw [PrefixCall.contextDerivation_closures]
  have smaller := call.cost_lt display.context.closures
  simp only [EndpointState.origin_cast] at smaller
  exact Nat.lt_of_lt_of_le smaller (Nat.le_add_right _ _)

/-- Field cuts and hidden-family argument endpoints may be charged jointly
to one actual projection. This reserve is stronger than two separate child
bounds, and permits exact cut reindexing without a new numerical premise. -/
theorem ProjectionDisplayPrefix.field_major_schedule
    {display : EndpointDisplay sourceEnv U displayed (.proj name index major) assigned}
    (packet : ProjectionDisplayPrefix display) (otherCost : Nat) :
    schedule .coherence ((Closure.close packet.head.field.origin display.context.closures).cost +
      packet.majorDisplay.cost) < schedule .coherence (display.cost + otherCost) := by
  apply schedule_strict
  have parent := Nat.mul_le_mul_right (1 + environmentCost display.context.closures)
    packet.head.route.weight_le
  simp only [EndpointState.origin_cast] at parent
  have children := original_two_children packet.head.field.origin packet.head.major.origin []
    display.context.closures
  exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le children parent) (Nat.le_add_right _ _)

/-- The actual field reference supplies the complete capture trace at the
selected declaration template. No new source formation proof is introduced. -/
theorem ProjectionDisplayPrefix.factorField
    {display : EndpointDisplay sourceEnv U displayed (.proj name index major) assigned}
    (packet : ProjectionDisplayPrefix display)
    (shape : packet.head.info.ctorType = wrapForalls domains result)
    (fieldBound : packet.head.info.nparams + index < domains.length)
    (certificate : CodeCert env U registry target locals σ packet.head.fieldType support footprint)
    (newLocals : List Nat) :
    ∃ required, Nonempty (CodeCert env U registry target newLocals
      (nativeCaptureSubst ((packet.head.parameters ++ (List.range index).map
        (fun field => VExpr.proj name field packet.head.sourceMajor)).map (·.subst σ)))
      (domains[packet.head.info.nparams + index].instL packet.head.levels) support required) ∧
      Nonempty (CaptureFootprint (env := env) packet.fieldReference registry target locals σ
        (packet.head.parameters ++ (List.range index).map
          (fun field => VExpr.proj name field packet.head.sourceMajor)) 0 0
        (fun initial => (Closure.close packet.fieldReference.origin initial).cost) footprint required) :=
  OriginalFactorCut.CodeCert.factorProjectionTypeOriginal shape packet.head.closed packet.head.levelCount
    packet.head.parameterCount fieldBound packet.head.selected certificate packet.fieldReference newLocals

/-- An actual field cut and an actual hidden-family argument jointly fit
under the selected projection closure, including their captured contexts. -/
theorem ProjectionDisplayPrefix.cut_argument_schedule
    {display : EndpointDisplay sourceEnv U displayed (.proj name index major) assigned}
    (packet : ProjectionDisplayPrefix display)
    (cut : CutOrigin packet.fieldReference expression 0)
    (position : Nat)
    (selected : (packet.head.parameters ++ packet.head.indices)[position]? = some expression)
    (otherCost : Nat) :
    schedule .coherence ((cut.sourceDisplay display.context).cost +
      (Closure.close (familyArgument packet.head.major position selected).node.origin
        display.context.closures).cost) < schedule .coherence (display.cost + otherCost) := by
  have cutBound := cut.location.cost_le display.context.closures
  have fieldOrigin : packet.fieldReference.origin = packet.head.field.origin := by
    rw [packet.field_eq]; rfl
  rw [fieldOrigin] at cutBound
  have argumentBound := familyArgument_cost_le packet.head.major position selected
    display.context.closures
  have childBound := Nat.add_le_add cutBound argumentBound
  have parent := Nat.mul_le_mul_right (1 + environmentCost display.context.closures)
    packet.head.route.weight_le
  simp only [EndpointState.origin_cast] at parent
  have children := original_two_children packet.head.field.origin packet.head.major.origin []
    display.context.closures
  apply schedule_strict
  rw [CutOriginAt.sourceDisplay_cost]
  exact Nat.lt_of_le_of_lt childBound
    (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le children parent) (Nat.le_add_right _ _))

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
