import Lean4Lean.Theory.Typing.AnchoredOriginalPiPrefix
import Lean4Lean.Theory.Typing.AnchoredOriginalPrefixReturn
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSortRule

/-! Complete displayed Pi coherence. Actual smaller domain/body C calls
recover both universe equalities from finite literal sort observations. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

structure PiComparisonCalls (env : VEnv) (registry : CanonicalHead.Registry)
    {left : EndpointDisplay leftEnv U displayed (.forallE annotation body) leftAssigned}
    {right : EndpointDisplay rightEnv U displayed (.forallE annotation body) rightAssigned}
    (leftPacket : PiDisplayPrefix left) (rightPacket : PiDisplayPrefix right) : Prop where
  leftConversions : PrefixCall.Fundamentals env registry leftPacket.selected.route left.context
  rightConversions : PrefixCall.Fundamentals env registry rightPacket.selected.route right.context
  domains : DisplayCoherence env U registry leftPacket.domainDisplay rightPacket.domainDisplay
  bodies : DisplayCoherence env U registry leftPacket.bodyDisplay rightPacket.bodyDisplay

theorem PiDisplayPrefix.child_pair_schedule
    {left : EndpointDisplay leftEnv U displayed (.forallE annotation body) leftAssigned}
    {right : EndpointDisplay rightEnv U displayed (.forallE annotation body) rightAssigned}
    (leftPacket : PiDisplayPrefix left) (rightPacket : PiDisplayPrefix right) :
    schedule .coherence (leftPacket.domainDisplay.cost + rightPacket.domainDisplay.cost) <
      schedule .coherence (left.cost + right.cost) ∧
    schedule .coherence (leftPacket.bodyDisplay.cost + rightPacket.bodyDisplay.cost) <
      schedule .coherence (left.cost + right.cost) := by
  constructor <;> apply schedule_strict
  · exact Nat.add_lt_add leftPacket.children_cost_lt.1 rightPacket.children_cost_lt.1
  · exact Nat.add_lt_add leftPacket.children_cost_lt.2 rightPacket.children_cost_lt.2

theorem PiDisplayPrefix.conversion_schedule
    {display : EndpointDisplay sourceEnv U displayed (.forallE annotation body) assigned}
    (packet : PiDisplayPrefix display)
    (call : PrefixCall packet.selected.route original) (otherCost : Nat) :
    schedule .fundamental
      (Closure.close original.origin (call.contextDerivation display.context).closures).cost <
    schedule .coherence (display.cost + otherCost) := by
  apply schedule_strict
  rw [PrefixCall.contextDerivation_closures]
  have smaller := call.cost_lt display.context.closures
  simp only [EndpointState.origin_cast] at smaller
  exact Nat.lt_of_lt_of_le smaller (Nat.le_add_right _ _)

theorem PiDisplayPrefix.naturalLevels
    {left : EndpointDisplay leftEnv U displayed (.forallE annotation body) leftAssigned}
    {right : EndpointDisplay rightEnv U displayed (.forallE annotation body) rightAssigned}
    (leftPacket : PiDisplayPrefix left) (rightPacket : PiDisplayPrefix right)
    (henv : env.Ordered) (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (domains : DisplayCoherence env U registry leftPacket.domainDisplay rightPacket.domainDisplay)
    (bodies : DisplayCoherence env U registry leftPacket.bodyDisplay rightPacket.bodyDisplay)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (leftFrame : DisplayFits env registry target left common available leftLocals)
    (rightFrame : DisplayFits env registry target right common available rightLocals) :
    VLevel.imax leftPacket.selected.view.domainLevel leftPacket.selected.view.bodyLevel ≈
      VLevel.imax rightPacket.selected.view.domainLevel rightPacket.selected.view.bodyLevel := by
  have domainAnswer := domains target common available leftLocals rightLocals closed hTarget
    (leftPacket.domainFrame leftFrame) (rightPacket.domainFrame rightFrame)
  have domainLevels := domainAnswer.sortLevels hTarget rfl rfl
  have formed := (leftPacket.selected.view.domain.sound.defeq.mono leftBelow).subst henv
    leftFrame.substitutions.left hTarget
  have hAnnotation : env.IsType U target (annotation.subst common) := by
    rw [leftPacket.annotation_eq, subst_lift']
    exact ⟨_, formed⟩
  let leftBodyFrame := leftPacket.selected.view.neutralDisplayFits left.provenance.initial
    left.insertion leftPacket.annotation_eq leftPacket.body_eq henv leftBelow hTarget hAnnotation
    leftFrame.fits leftFrame.substitutions
  let rightBodyFrame := rightPacket.selected.view.neutralDisplayFits right.provenance.initial
    right.insertion rightPacket.annotation_eq rightPacket.body_eq henv rightBelow hTarget hAnnotation
    rightFrame.fits rightFrame.substitutions
  have shiftedClosed : (Valuation.push [] (available.rename (.skip .refl))).AtomClosed := by
    simpa only [List.nil_append, List.flatMap_nil] using
      Valuation.push_atomized_closed (closed.rename (.skip .refl)) []
  have bodyAnswer := bodies (annotation.subst common :: target) common.lift
    (Valuation.push [] (available.rename (.skip .refl))) (Locals.push leftLocals) (Locals.push rightLocals)
    shiftedClosed ⟨hTarget, hAnnotation⟩ leftBodyFrame rightBodyFrame
  have bodyLevels := bodyAnswer.sortLevels ⟨hTarget, hAnnotation⟩ rfl rfl
  exact VLevel.imax_congr domainLevels bodyLevels

theorem PiDisplayPrefix.compare
    {left : EndpointDisplay leftEnv U displayed (.forallE annotation body) leftAssigned}
    {right : EndpointDisplay rightEnv U displayed (.forallE annotation body) rightAssigned}
    (leftPacket : PiDisplayPrefix left) (rightPacket : PiDisplayPrefix right)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (calls : PiComparisonCalls env registry leftPacket rightPacket) :
    DisplayCoherence env U registry left right := by
  intro target common available leftLocals rightLocals closed hTarget leftFrame rightFrame
  have leftClosed := left.sourceValuation_closed closed
  have rightClosed := right.sourceValuation_closed closed
  have levels := leftPacket.naturalLevels rightPacket henv leftBelow rightBelow
    calls.domains calls.bodies closed hTarget leftFrame rightFrame
  have leftWF : (VLevel.imax leftPacket.selected.view.domainLevel leftPacket.selected.view.bodyLevel).WF U :=
    ⟨leftPacket.selected.view.domainWF, leftPacket.selected.view.bodyWF⟩
  have rightWF : (VLevel.imax rightPacket.selected.view.domainLevel rightPacket.selected.view.bodyLevel).WF U :=
    ⟨rightPacket.selected.view.domainWF, rightPacket.selected.view.bodyWF⟩
  have naturalPath : TypeConversion env U target
      ((VExpr.sort (.imax leftPacket.selected.view.domainLevel leftPacket.selected.view.bodyLevel)).subst (left.sourceSubst common))
      ((VExpr.sort (.imax rightPacket.selected.view.domainLevel rightPacket.selected.view.bodyLevel)).subst (right.sourceSubst common)) :=
    .single (.sortDF leftWF rightWF levels)
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
    have formation : GradedTransfer env U registry target leftLocals (left.sourceSubst common)
        (left.sourceSubst common) (left.sourceValuation available)
        (.sort (.imax leftPacket.selected.view.domainLevel leftPacket.selected.view.bodyLevel))
        (.sort (.imax rightPacket.selected.view.domainLevel rightPacket.selected.view.bodyLevel))
        (.sort (.succ (.imax leftPacket.selected.view.domainLevel leftPacket.selected.view.bodyLevel))) :=
      GradedTransfer.sortDF (assigned := .succ (.imax leftPacket.selected.view.domainLevel leftPacket.selected.view.bodyLevel))
        henv hscoped leftWF rightWF leftWF levels (Relevant.succ _) hTarget
    obtain ⟨answer⟩ := natural.transfer_graded henv hscoped hTarget leftClosed formation incoming
    obtain ⟨required, ⟨transported⟩, resources⟩ := OriginalFactorCut.CodeCert.betweenDisplays
      (right := .sort (.imax rightPacket.selected.view.domainLevel rightPacket.selected.view.bodyLevel))
      answer.certificate left.map right.map common rfl rfl rfl [] rightLocals
      answer.available (fun _ => rfl) (fun _ => rfl)
    exact ⟨⟨required, transported, resources, answer.related⟩⟩

theorem EndpointDisplay.piCoherence
    (left : EndpointDisplay leftEnv U displayed (.forallE annotation body) leftAssigned)
    (right : EndpointDisplay rightEnv U displayed (.forallE annotation body) rightAssigned)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (calls : PiComparisonCalls env registry left.piPrefix right.piPrefix) :
    DisplayCoherence env U registry left right :=
  left.piPrefix.compare right.piPrefix henv hscoped leftBelow rightBelow calls

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
