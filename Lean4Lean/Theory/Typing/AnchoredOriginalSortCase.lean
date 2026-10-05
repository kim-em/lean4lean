import Lean4Lean.Theory.Typing.AnchoredOriginalLambdaPrefix
import Lean4Lean.Theory.Typing.AnchoredOriginalPrefixReturn
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSortRule

/-! Displayed sort comparison has a fixed natural successor universe.
Only the retained assigned-type conversions need recursive fundamental calls. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

structure SortPrefix
    (node : EndpointState sourceEnv U source (.sort level) assigned) where
  typeLevel : VLevel
  levelWF : typeLevel.WF U
  level_eq : typeLevel ≈ level.succ
  natural : EndpointState sourceEnv U source (.sort level) (.sort typeLevel)
  route : PrefixRoute sourceEnv U source (.sort level) node natural

private theorem primitiveSort
    (reference : EndpointRef sourceEnv U source expression assigned)
    (expression_eq : expression = .sort level) (primitive : reference.Primitive) :
    ∃ typeLevel, assigned = .sort typeLevel ∧ typeLevel.WF U ∧ typeLevel ≈ level.succ := by
  cases reference with
  | left original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expression_eq
    case sortDF.refl => exact ⟨_, rfl, by assumption, rfl⟩
  | right original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expression_eq
    case sortDF.refl => exact ⟨_, rfl, by assumption, VLevel.succ_congr (by assumption)⟩

private def castLastType
    {first : EndpointState sourceEnv U source expression assigned}
    {last : EndpointState sourceEnv U source expression natural}
    (route : PrefixRoute sourceEnv U source expression first last) (equal : natural = output) :
    PrefixRoute sourceEnv U source expression first (last.cast rfl equal) := by
  cases equal; exact route

noncomputable def sortPrefix
    (node : EndpointState sourceEnv U source (.sort level) assigned) : SortPrefix node := by
  obtain ⟨type, head, route, normal⟩ := prefixHead node
  cases head with
  | ref reference =>
    have result := primitiveSort reference rfl normal
    let typeLevel := Classical.choose result
    have properties := Classical.choose_spec result
    exact ⟨typeLevel, properties.2.1, properties.2.2,
      (EndpointState.ref reference).cast rfl properties.1, castLastType route properties.1⟩
  | convert plan term => exact normal.elim
  | sort levelWF => exact ⟨.succ level, levelWF, rfl, .sort levelWF, route⟩

structure SortDisplayPrefix
    (display : EndpointDisplay env U displayed (.sort level) assigned) where
  source_eq : display.sourceExpression = .sort level
  selected : SortPrefix (display.node.cast source_eq rfl)

noncomputable def EndpointDisplay.sortPrefix
    (display : EndpointDisplay env U displayed (.sort level) assigned) : SortDisplayPrefix display := by
  have source_eq : display.sourceExpression = .sort level := by
    have equal := display.expression_eq
    cases h : display.sourceExpression <;> simp only [h, VExpr.lift'] at equal
    all_goals cases equal
    rfl
  exact ⟨source_eq, OriginalEndpointFactor.sortPrefix (display.node.cast source_eq rfl)⟩

theorem SortDisplayPrefix.conversion_schedule
    {display : EndpointDisplay sourceEnv U displayed (.sort level) assigned}
    (packet : SortDisplayPrefix display)
    (call : PrefixCall packet.selected.route original) (otherCost : Nat) :
    schedule .fundamental
      (Closure.close original.origin (call.contextDerivation display.context).closures).cost <
    schedule .coherence (display.cost + otherCost) := by
  apply schedule_strict
  rw [PrefixCall.contextDerivation_closures]
  have smaller := call.cost_lt display.context.closures
  simp only [EndpointState.origin_cast] at smaller
  exact Nat.lt_of_lt_of_le smaller (Nat.le_add_right _ _)

theorem SortDisplayPrefix.compare
    {left : EndpointDisplay leftEnv U displayed (.sort level) leftAssigned}
    {right : EndpointDisplay rightEnv U displayed (.sort level) rightAssigned}
    (leftPacket : SortDisplayPrefix left) (rightPacket : SortDisplayPrefix right)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (leftCalls : PrefixCall.Fundamentals env registry leftPacket.selected.route left.context)
    (rightCalls : PrefixCall.Fundamentals env registry rightPacket.selected.route right.context) :
    DisplayCoherence env U registry left right := by
  intro target common available leftLocals rightLocals closed hTarget leftFrame rightFrame
  have leftClosed := left.sourceValuation_closed closed
  have rightClosed := right.sourceValuation_closed closed
  have levels := leftPacket.selected.level_eq.trans rightPacket.selected.level_eq.symm
  have naturalPath : TypeConversion env U target
      ((VExpr.sort leftPacket.selected.typeLevel).subst (left.sourceSubst common))
      ((VExpr.sort rightPacket.selected.typeLevel).subst (right.sourceSubst common)) :=
    .single (.sortDF leftPacket.selected.levelWF rightPacket.selected.levelWF levels)
  have path := PrefixRoute.comparePath henv leftBelow rightBelow hTarget
    leftFrame.substitutions rightFrame.substitutions
    leftPacket.selected.route rightPacket.selected.route naturalPath
  refine ⟨?_, ?_⟩
  · simpa only [left.realizedType common, right.realizedType common] using path
  · intro n profile footprint certificate resources
    apply PrefixRoute.compareHeadsOriginal henv hscoped leftBelow rightBelow
      left.context right.context leftClosed rightClosed hTarget
      leftFrame.substitutions rightFrame.substitutions leftFrame.fits rightFrame.fits
      leftPacket.selected.route rightPacket.selected.route leftCalls rightCalls
      (certificate := certificate) (resources := resources)
    intro required natural incoming
    have formation : GradedTransfer env U registry target leftLocals (left.sourceSubst common)
        (left.sourceSubst common) (left.sourceValuation available)
        (.sort leftPacket.selected.typeLevel) (.sort rightPacket.selected.typeLevel)
        (.sort leftPacket.selected.typeLevel.succ) :=
      GradedTransfer.sortDF (left := leftPacket.selected.typeLevel) (right := rightPacket.selected.typeLevel)
        (assigned := leftPacket.selected.typeLevel.succ) henv hscoped
        leftPacket.selected.levelWF rightPacket.selected.levelWF leftPacket.selected.levelWF
        levels (Relevant.succ _) hTarget
    obtain ⟨answer⟩ := natural.transfer_graded henv hscoped hTarget leftClosed formation incoming
    obtain ⟨required, ⟨transported⟩, resources⟩ := OriginalFactorCut.CodeCert.betweenDisplays
      (right := .sort rightPacket.selected.typeLevel)
      answer.certificate left.map right.map common rfl rfl rfl [] rightLocals
      answer.available (fun _ => rfl) (fun _ => rfl)
    exact ⟨⟨required, transported, resources, answer.related⟩⟩

theorem EndpointDisplay.sortCoherence
    (left : EndpointDisplay leftEnv U displayed (.sort level) leftAssigned)
    (right : EndpointDisplay rightEnv U displayed (.sort level) rightAssigned)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (leftCalls : PrefixCall.Fundamentals env registry left.sortPrefix.selected.route left.context)
    (rightCalls : PrefixCall.Fundamentals env registry right.sortPrefix.selected.route right.context) :
    DisplayCoherence env U registry left right :=
  left.sortPrefix.compare right.sortPrefix henv hscoped leftBelow rightBelow leftCalls rightCalls

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
