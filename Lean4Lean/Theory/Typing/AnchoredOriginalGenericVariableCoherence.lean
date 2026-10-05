import Lean4Lean.Theory.Typing.AnchoredOriginalGenericDisplay
import Lean4Lean.Theory.Typing.AnchoredOriginalVariableCase
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPrefixMeasure
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPrefixReturn
import Lean4Lean.Theory.Typing.AnchoredOriginalLocatedDirect

/-! The rich variable C step. Context lookup gives literal equality of the
displayed natural types. The exact rich certificate is transferred between
their two actual formation children by a strictly smaller expression-R call;
it is never reflected or relabelled onto another source typing. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalRecordSource OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem VariableDisplayPrefix.context_eq
    {display : EndpointDisplay sourceEnv U displayed (.bvar index) assigned}
    (packet : VariableDisplayPrefix display) :
    packet.selected.view.location.contextDerivation display.provenance.initial = display.context := by
  rw [← packet.selected.location_eq, PrefixRoute.locate_contextDerivation,
    Located.castExpression_contextDerivation, ← display.provenance.context_eq]

noncomputable def VariableDisplayPrefix.naturalDisplay
    {display : EndpointDisplay sourceEnv U displayed (.bvar index) assigned}
    (packet : VariableDisplayPrefix display) :
    EndpointDisplay sourceEnv U displayed (.bvar index)
      (packet.selected.view.sourceType.lift' display.map) where
  source := display.source
  sourceExpression := .bvar packet.sourceIndex
  sourceType := packet.selected.view.sourceType
  context := display.context
  node := .bvar packet.selected.view.lookup packet.selected.view.levelWF packet.selected.view.formation
  provenance := {
    rootSource := display.provenance.rootSource
    rootExpression := display.provenance.rootExpression
    rootType := display.provenance.rootType
    root := display.provenance.root
    initial := display.provenance.initial
    location := packet.selected.view.location
    context_eq := packet.context_eq.symm }
  map := display.map
  insertion := display.insertion
  expression_eq := packet.expression_eq
  type_eq := rfl

noncomputable def VariableDisplayPrefix.naturalFrame
    {display : EndpointDisplay sourceEnv U displayed (.bvar index) assigned}
    (packet : VariableDisplayPrefix display)
    (frame : OriginalRichDisplayFrame env registry target display common locals available) :
    OriginalRichDisplayFrame env registry target packet.naturalDisplay common locals available :=
  ⟨frame.frame, frame.substitutions⟩

theorem VariableDisplayPrefix.formation_dependency_cost_lt
    {display : EndpointDisplay sourceEnv U displayed (.bvar index) assigned}
    (packet : VariableDisplayPrefix display)
    (frame : OriginalRichDisplayFrame env registry target display common locals available)
    (ordered : sourceEnv.Ordered) :
    (packet.naturalFrame frame).formation.cost ordered < frame.cost ordered := by
  have child : (Closure.close (packet.selected.view.formation.dependencyOrigin ordered)
      (frame.frame.dependencyEnvironment ordered)).cost <
      (Closure.close ((EndpointState.bvar packet.selected.view.lookup packet.selected.view.levelWF
        packet.selected.view.formation).dependencyOrigin ordered)
        (frame.frame.dependencyEnvironment ordered)).cost :=
    original_child_same_environment (Origin.rule_child (by simp)) _
  have bound := packet.selected.route.dependency_cost_le ordered (frame.frame.dependencyEnvironment ordered)
  simp only [EndpointState.dependencyOrigin_cast] at bound
  exact Nat.lt_of_lt_of_le child bound

theorem VariableDisplayPrefix.naturalTypes_eq
    {left : EndpointDisplay leftEnv U displayed (.bvar index) leftAssigned}
    {right : EndpointDisplay rightEnv U displayed (.bvar index) rightAssigned}
    (leftPacket : VariableDisplayPrefix left) (rightPacket : VariableDisplayPrefix right) :
    leftPacket.selected.view.sourceType.lift' left.map = rightPacket.selected.view.sourceType.lift' right.map :=
  displayedLookupTypes_eq leftPacket.selected.view.lookup rightPacket.selected.view.lookup
    left.insertion right.insertion (leftPacket.expression_eq.symm.trans rightPacket.expression_eq)

/-- Both child costs use the actual generic frames, rather than the source
formation spines alone. Captured and grouped entries remain charged. -/
theorem VariableDisplayPrefix.naturalRichCoherence
    {left : EndpointDisplay leftEnv U displayed (.bvar index) leftAssigned}
    {right : EndpointDisplay rightEnv U displayed (.bvar index) rightAssigned}
    (leftPacket : VariableDisplayPrefix left) (rightPacket : VariableDisplayPrefix right)
    (lf : leftEnv.Ordered) (rf : rightEnv.Ordered)
    (leftFrame : OriginalRichDisplayFrame env registry target left common leftLocals leftAvailable)
    (rightFrame : OriginalRichDisplayFrame env registry target right common rightLocals rightAvailable)
    (formationR :
      richSchedule .expressionReindex
        ((leftPacket.naturalFrame leftFrame).formation.cost lf +
         (rightPacket.naturalFrame rightFrame).formation.cost rf) <
      richSchedule .assignedComparison (leftFrame.cost lf + rightFrame.cost rf) →
      OriginalRichDisplayReindex (leftPacket.naturalFrame leftFrame).formation
        ((rightPacket.naturalFrame rightFrame).formation.relabelExpression
          (leftPacket.naturalTypes_eq rightPacket))) :
    OriginalRichDisplayCoherence (leftPacket.naturalFrame leftFrame) (rightPacket.naturalFrame rightFrame) := by
  have equal := leftPacket.naturalTypes_eq rightPacket
  refine ⟨?_, ?_⟩
  · rw [equal]
    exact .refl
  · exact formationR (richSchedule_strict (Nat.add_lt_add
      (leftPacket.formation_dependency_cost_lt leftFrame lf)
      (rightPacket.formation_dependency_cost_lt rightFrame rf)) _ _) rfl rfl

/-- Directness follows the actual original variable occurrence, including
after arbitrary assigned-formation and conversion locations. -/
noncomputable def VariableDisplayPrefix.directRoute
    {display : EndpointDisplay sourceEnv U displayed (.bvar index) assigned}
    (packet : VariableDisplayPrefix display) :
    DirectPrefixRoute sourceEnv U display.source (.bvar packet.sourceIndex)
      (display.node.cast packet.source_eq rfl)
      (.bvar packet.selected.view.lookup packet.selected.view.levelWF packet.selected.view.formation) :=
  Classical.choice (packet.selected.route.direct (fun _ _ equal => by cases equal)
    ((display.provenance.location.castExpression packet.source_eq).originalDirect.direct
      (fun _ _ equal => by cases equal)))

private theorem formation_cast_expression
    (node : EndpointState sourceEnv U source expression assigned) (same : expression = expression') :
    (node.cast same rfl).typeFormation = node.typeFormation := by
  cases same
  rfl

/-- Full rich assigned-type C for variables, with both actual conversion
prefixes. All query constructors are covered by the formation R channel;
the wrapper never erases or reconstructs an indexed rich certificate. -/
theorem VariableDisplayPrefix.richCoherence
    {left : EndpointDisplay leftEnv U displayed (.bvar index) leftAssigned}
    {right : EndpointDisplay rightEnv U displayed (.bvar index) rightAssigned}
    (leftPacket : VariableDisplayPrefix left) (rightPacket : VariableDisplayPrefix right)
    (henv : env.Ordered) (lf : leftEnv.Ordered) (rf : rightEnv.Ordered)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (leftFrame : OriginalRichDisplayFrame env registry target left common leftLocals leftAvailable)
    (rightFrame : OriginalRichDisplayFrame env registry target right common rightLocals rightAvailable)
    (leftCalls : leftPacket.directRoute.PeelCalls env registry target lf
      (leftFrame.frame.dependencyEnvironment lf) leftLocals (left.sourceSubst common) leftAvailable)
    (rightCalls : rightPacket.directRoute.RestoreCalls env registry target rf
      (rightFrame.frame.dependencyEnvironment rf) rightLocals (right.sourceSubst common) rightAvailable)
    (formationR :
      richSchedule .expressionReindex
        ((leftPacket.naturalFrame leftFrame).formation.cost lf +
         (rightPacket.naturalFrame rightFrame).formation.cost rf) <
      richSchedule .assignedComparison (leftFrame.cost lf + rightFrame.cost rf) →
      OriginalRichDisplayReindex (leftPacket.naturalFrame leftFrame).formation
        ((rightPacket.naturalFrame rightFrame).formation.relabelExpression
          (leftPacket.naturalTypes_eq rightPacket))) :
    OriginalRichDisplayCoherence leftFrame rightFrame := by
  have natural := leftPacket.naturalRichCoherence rightPacket lf rf leftFrame rightFrame formationR
  refine ⟨?_, ?_⟩
  · have naturalPath : TypeConversion env U target
        (leftPacket.selected.view.sourceType.subst (left.sourceSubst common))
        (rightPacket.selected.view.sourceType.subst (right.sourceSubst common)) := by
      simpa only [VariableDisplayPrefix.naturalDisplay, subst_lift', EndpointDisplay.sourceSubst] using natural.path
    have path := PrefixRoute.comparePath henv leftBelow rightBelow formed leftFrame.substitutions
      rightFrame.substitutions leftPacket.selected.route rightPacket.selected.route naturalPath
    simpa only [left.realizedType common, right.realizedType common] using path
  · have compared : RichCodeTransfer env U registry target
        (left.node.cast leftPacket.source_eq rfl).typeFormation.node
        (right.node.cast rightPacket.source_eq rfl).typeFormation.node
        leftLocals rightLocals (left.sourceSubst common) (right.sourceSubst common) leftAvailable rightAvailable :=
      leftPacket.directRoute.compareCode henv lf rf
      (leftFrame.frame.dependencyEnvironment lf) (rightFrame.frame.dependencyEnvironment rf)
      rightPacket.directRoute leftCalls rightCalls natural.queries
    rw [formation_cast_expression left.node leftPacket.source_eq,
      formation_cast_expression right.node rightPacket.source_eq] at compared
    exact @compared

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
