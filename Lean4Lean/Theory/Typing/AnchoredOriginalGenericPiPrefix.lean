import Lean4Lean.Theory.Typing.AnchoredOriginalGenericPiCoherence
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPrefixReturn
import Lean4Lean.Theory.Typing.AnchoredOriginalLocatedDirect
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPrefixMeasure

namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalRecordSource OriginalTail
set_option backward.isDefEq.respectTransparency false

noncomputable def Located.piNaturalDisplay
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    (location : Located root (.pi hu hv domain body))
    (initial : ContextDerivation sourceEnv U rootSource)
    (insertion : Ctx.Lift' map source displayed)
    (annotationEq : annotation = A.lift' map) (bodyEq : displayedBody = B.lift' map.cons) :
    EndpointDisplay sourceEnv U displayed (.forallE annotation displayedBody) (.sort (.imax u v)) where
  source := source
  sourceExpression := .forallE A B
  sourceType := .sort (.imax u v)
  context := location.contextDerivation initial
  node := .pi hu hv domain body
  provenance := .ofLocation location initial
  map := map
  insertion := insertion
  expression_eq := by simp only [lift', ← annotationEq, ← bodyEq]
  type_eq := rfl

/-- The binary induction hypothesis is restricted to strictly smaller
original display pairs; it is used below only on actual Pi children. -/
def RichDisplayComparisonBelow (leftEnv rightEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (lf : leftEnv.Ordered) (rf : rightEnv.Ordered)
    (limit : Nat) : Prop :=
  ∀ {displayed expression leftAssigned rightAssigned}
    (left : EndpointDisplay leftEnv U displayed expression leftAssigned)
    (right : EndpointDisplay rightEnv U displayed expression rightAssigned)
    {target common leftLocals rightLocals leftAvailable rightAvailable}
    (_formed : OnCtx target (env.IsType U))
    (_leftClosed : leftAvailable.AtomClosed) (_rightClosed : rightAvailable.AtomClosed)
    (leftFrame : OriginalRichDisplayFrame env registry target left common leftLocals leftAvailable)
    (rightFrame : OriginalRichDisplayFrame env registry target right common rightLocals rightAvailable),
    richSchedule .assignedComparison (leftFrame.cost lf + rightFrame.cost rf) < limit →
    OriginalRichDisplayCoherence leftFrame rightFrame

theorem Located.piNaturalCoherence
    {leftRoot : EndpointRef leftEnv U leftRootSource le lt}
    {rightRoot : EndpointRef rightEnv U rightRootSource re rt}
    {leftDomain : EndpointState leftEnv U leftSource A (.sort u)}
    {rightDomain : EndpointState rightEnv U rightSource C (.sort u')}
    {leftBody : EndpointState leftEnv U (A :: leftSource) B (.sort v)}
    {rightBody : EndpointState rightEnv U (C :: rightSource) D (.sort v')}
    (leftLocation : Located leftRoot (.pi lu lv leftDomain leftBody))
    (rightLocation : Located rightRoot (.pi ru rv rightDomain rightBody))
    (leftInitial : ContextDerivation leftEnv U leftRootSource)
    (rightInitial : ContextDerivation rightEnv U rightRootSource)
    (leftInsertion : Ctx.Lift' leftMap leftSource displayed)
    (rightInsertion : Ctx.Lift' rightMap rightSource displayed)
    (leftAnnotation : annotation = A.lift' leftMap) (rightAnnotation : annotation = C.lift' rightMap)
    (leftExpression : displayedBody = B.lift' leftMap.cons)
    (rightExpression : displayedBody = D.lift' rightMap.cons)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (lf : leftEnv.Ordered) (rf : rightEnv.Ordered)
    (formed : OnCtx target (env.IsType U))
    (leftFrame : OriginalRichDisplayFrame env registry target
      (leftLocation.piNaturalDisplay leftInitial leftInsertion leftAnnotation leftExpression)
      common leftLocals leftAvailable)
    (rightFrame : OriginalRichDisplayFrame env registry target
      (rightLocation.piNaturalDisplay rightInitial rightInsertion rightAnnotation rightExpression)
      common rightLocals rightAvailable)
    (leftClosed : leftAvailable.AtomClosed) (rightClosed : rightAvailable.AtomClosed)
    (calls : RichDisplayComparisonBelow leftEnv rightEnv env U registry lf rf limit)
    (bound : richSchedule .assignedComparison (leftFrame.cost lf + rightFrame.cost rf) ≤ limit) :
    OriginalRichDisplayCoherence leftFrame rightFrame := by
  obtain ⟨ld, rfl⟩ := leftLocation.originalDomains.1
  obtain ⟨rd, rfl⟩ := rightLocation.originalDomains.1
  apply OriginalRichDisplayFrame.nativePiCoherence leftLocation rightLocation leftInitial rightInitial
    leftInsertion rightInsertion leftAnnotation rightAnnotation leftExpression rightExpression
    henv leftBelow rightBelow lf rf hscoped formed leftFrame rightFrame leftClosed
  · intro smaller
    exact calls _ _ formed leftClosed rightClosed _ _ (Nat.lt_of_lt_of_le smaller bound)
  · intro annotationType leftChild rightChild smaller
    have lc : (Valuation.push [] (leftAvailable.rename (.skip .refl))).AtomClosed := by
      simpa only [List.nil_append, List.flatMap_nil] using
        Valuation.push_atomized_closed (leftClosed.rename (.skip .refl)) []
    have rc : (Valuation.push [] (rightAvailable.rename (.skip .refl))).AtomClosed := by
      simpa only [List.nil_append, List.flatMap_nil] using
        Valuation.push_atomized_closed (rightClosed.rename (.skip .refl)) []
    exact calls _ _ (target := annotation.subst common :: target) ⟨formed, annotationType⟩ lc rc leftChild rightChild (Nat.lt_of_lt_of_le smaller bound)

private def castContext {first second : ContextDerivation sourceEnv U source} (equal : first = second)
    (frame : OriginalRichFrame sourceEnv env U registry target first locals σ τ available) :
    OriginalRichFrame sourceEnv env U registry target second locals σ τ available := equal ▸ frame
private theorem castContext_environment {first second : ContextDerivation sourceEnv U source} (equal : first = second)
    (frame : OriginalRichFrame sourceEnv env U registry target first locals σ τ available)
    (ordered : sourceEnv.Ordered) :
    (castContext equal frame).dependencyEnvironment ordered = frame.dependencyEnvironment ordered := by
  cases equal; rfl

noncomputable def PiDisplayPrefix.genericNaturalFrame
    {display : EndpointDisplay sourceEnv U displayed (.forallE annotation body) assigned}
    (packet : PiDisplayPrefix display)
    (frame : OriginalRichDisplayFrame env registry target display common locals available) :
    OriginalRichDisplayFrame env registry target
      (packet.selected.view.location.piNaturalDisplay display.provenance.initial display.insertion
        packet.annotation_eq packet.body_eq) common locals available :=
  ⟨castContext packet.context_eq.symm frame.frame, frame.substitutions⟩

theorem PiDisplayPrefix.genericNaturalFrame_cost_le
    {display : EndpointDisplay sourceEnv U displayed (.forallE annotation body) assigned}
    (packet : PiDisplayPrefix display)
    (frame : OriginalRichDisplayFrame env registry target display common locals available)
    (ordered : sourceEnv.Ordered) :
    (packet.genericNaturalFrame frame).cost ordered ≤ frame.cost ordered := by
  simp only [OriginalRichDisplayFrame.cost, PiDisplayPrefix.genericNaturalFrame,
    Located.piNaturalDisplay, castContext_environment]
  have bound := packet.selected.route.dependency_cost_le ordered (frame.frame.dependencyEnvironment ordered)
  simpa only [EndpointState.dependencyOrigin_cast] using bound

noncomputable def PiDisplayPrefix.directRoute
    {display : EndpointDisplay sourceEnv U displayed (.forallE annotation body) assigned}
    (packet : PiDisplayPrefix display) :
    DirectPrefixRoute sourceEnv U display.source (.forallE packet.sourceDomain packet.sourceBody)
      (display.node.cast packet.source_eq rfl)
      (.pi packet.selected.view.domainWF packet.selected.view.bodyWF
        packet.selected.view.domain packet.selected.view.body) :=
  Classical.choice (packet.selected.route.direct (fun _ _ equal => by cases equal)
    ((display.provenance.location.castExpression packet.source_eq).originalDirect.direct
      (fun _ _ equal => by cases equal)))

private theorem formation_cast_expression
    (node : EndpointState sourceEnv U source expression assigned) (same : expression = expression') :
    (node.cast same rfl).typeFormation = node.typeFormation := by cases same; rfl

theorem PiDisplayPrefix.richCoherence
    {left : EndpointDisplay leftEnv U displayed (.forallE annotation body) leftAssigned}
    {right : EndpointDisplay rightEnv U displayed (.forallE annotation body) rightAssigned}
    (leftPacket : PiDisplayPrefix left) (rightPacket : PiDisplayPrefix right)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (lf : leftEnv.Ordered) (rf : rightEnv.Ordered)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (leftFrame : OriginalRichDisplayFrame env registry target left common leftLocals leftAvailable)
    (rightFrame : OriginalRichDisplayFrame env registry target right common rightLocals rightAvailable)
    (leftClosed : leftAvailable.AtomClosed) (rightClosed : rightAvailable.AtomClosed)
    (leftCalls : leftPacket.directRoute.PeelCalls env registry target lf
      (leftFrame.frame.dependencyEnvironment lf) leftLocals (left.sourceSubst common) leftAvailable)
    (rightCalls : rightPacket.directRoute.RestoreCalls env registry target rf
      (rightFrame.frame.dependencyEnvironment rf) rightLocals (right.sourceSubst common) rightAvailable)
    (calls : RichDisplayComparisonBelow leftEnv rightEnv env U registry lf rf
      (richSchedule .assignedComparison (leftFrame.cost lf + rightFrame.cost rf))) :
    OriginalRichDisplayCoherence leftFrame rightFrame := by
  have natural := Located.piNaturalCoherence leftPacket.selected.view.location rightPacket.selected.view.location
    left.provenance.initial right.provenance.initial left.insertion right.insertion
    leftPacket.annotation_eq rightPacket.annotation_eq leftPacket.body_eq rightPacket.body_eq
    henv hscoped leftBelow rightBelow lf rf formed
    (leftPacket.genericNaturalFrame leftFrame) (rightPacket.genericNaturalFrame rightFrame)
    leftClosed rightClosed calls
    (by
      have bound := Nat.add_le_add (leftPacket.genericNaturalFrame_cost_le leftFrame lf)
        (rightPacket.genericNaturalFrame_cost_le rightFrame rf)
      unfold richSchedule
      omega)
  refine ⟨?_, ?_⟩
  · have path := PrefixRoute.comparePath henv leftBelow rightBelow formed
      leftFrame.substitutions rightFrame.substitutions leftPacket.selected.route rightPacket.selected.route
      (show TypeConversion env U target _ _ from natural.path)
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
