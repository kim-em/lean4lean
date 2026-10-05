import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationCase
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableApplicationNatural
import Lean4Lean.Theory.Typing.AnchoredOriginalSortablePrefix

/-! Complete displayed application coherence, with both original conversion
prefixes restored. All semantic premises name fixed smaller original calls. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

structure SortableApplicationComparisonCalls (env : VEnv) (registry : CanonicalHead.Registry)
    {left : EndpointDisplay leftEnv U displayed (.app function argument) leftAssigned}
    {right : EndpointDisplay rightEnv U displayed (.app function argument) rightAssigned}
    (leftPacket : ApplicationDisplayPrefix left) (rightPacket : ApplicationDisplayPrefix right) : Prop where
  leftConversions : PrefixCall.HereditaryFundamentals env registry leftPacket.selected.route left.context
  rightConversions : PrefixCall.HereditaryFundamentals env registry rightPacket.selected.route right.context
  argument : StateHereditaryFundamental env registry
    ((Located.appArgument leftPacket.selected.view.location).contextDerivation left.provenance.initial)
    leftPacket.selected.view.argument
  rightDomain : StateSortableFundamental env registry
    (rightPacket.selected.view.location.contextDerivation right.provenance.initial) rightPacket.selected.view.domain
  rightCodomain : StateSortableFundamental env registry
    ((Located.appCodomain rightPacket.selected.view.location).contextDerivation right.provenance.initial)
    rightPacket.selected.view.codomain
  functionTypes : DisplaySortableCoherence env U registry leftPacket.functionDisplay rightPacket.functionDisplay

/-- Actual left prefix replay, natural application comparison, and actual
right restoration form the full displayed application C branch. -/
theorem ApplicationDisplayPrefix.compareSortable
    {left : EndpointDisplay leftEnv U displayed (.app function argument) leftAssigned}
    {right : EndpointDisplay rightEnv U displayed (.app function argument) rightAssigned}
    (leftPacket : ApplicationDisplayPrefix left) (rightPacket : ApplicationDisplayPrefix right)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (calls : SortableApplicationComparisonCalls env registry leftPacket rightPacket) :
    DisplaySortableCoherence env U registry left right := by
  intro target common available leftLocals rightLocals closed hTarget leftFrame rightFrame
  have leftClosed := left.sourceValuation_closed closed
  have rightClosed := right.sourceValuation_closed closed
  have sameArgument := leftPacket.argument_eq.symm.trans rightPacket.argument_eq
  intro relevant n profile footprint certificate resources
  apply PrefixRoute.compareHeadsSortableOriginal henv hscoped leftBelow rightBelow
      left.context right.context leftClosed rightClosed hTarget
      leftFrame.substitutions rightFrame.substitutions leftFrame.fits rightFrame.fits
      leftPacket.selected.route rightPacket.selected.route calls.leftConversions calls.rightConversions
      (certificate := certificate) (resources := resources)
  intro required natural incoming
  exact (AppView.naturalSortableComparison leftPacket.selected.view rightPacket.selected.view
      left.provenance.initial right.provenance.initial left.insertion right.insertion
      leftPacket.function_eq rightPacket.function_eq sameArgument henv hscoped leftBelow rightBelow
      calls.argument calls.functionTypes calls.rightDomain calls.rightCodomain closed hTarget
      leftFrame.fits rightFrame.fits leftFrame.substitutions rightFrame.substitutions natural incoming).2

/-- The same actual smaller calls also give the original assigned-type path,
independently of any nonempty formation query. -/
theorem ApplicationDisplayPrefix.sortableComparisonPath
    {left : EndpointDisplay leftEnv U displayed (.app function argument) leftAssigned}
    {right : EndpointDisplay rightEnv U displayed (.app function argument) rightAssigned}
    (leftPacket : ApplicationDisplayPrefix left) (rightPacket : ApplicationDisplayPrefix right)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (calls : SortableApplicationComparisonCalls env registry leftPacket rightPacket)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (leftFrame : SortableDisplayFits env registry target left common available leftLocals)
    (rightFrame : SortableDisplayFits env registry target right common available rightLocals) :
    TypeConversion env U target (leftAssigned.subst common) (rightAssigned.subst common) := by
  have natural := AppView.naturalSortablePath leftPacket.selected.view rightPacket.selected.view
    left.provenance.initial right.provenance.initial left.insertion right.insertion
    leftPacket.function_eq rightPacket.function_eq
    (leftPacket.argument_eq.symm.trans rightPacket.argument_eq) henv hscoped leftBelow rightBelow
    calls.argument calls.functionTypes calls.rightDomain calls.rightCodomain closed formed
    leftFrame.fits rightFrame.fits leftFrame.substitutions rightFrame.substitutions
  have path := PrefixRoute.comparePath henv leftBelow rightBelow formed
    leftFrame.substitutions rightFrame.substitutions
    leftPacket.selected.route rightPacket.selected.route natural
  simpa only [left.realizedType common, right.realizedType common] using path

theorem EndpointDisplay.applicationSortableCoherence
    (left : EndpointDisplay leftEnv U displayed (.app function argument) leftAssigned)
    (right : EndpointDisplay rightEnv U displayed (.app function argument) rightAssigned)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (calls : SortableApplicationComparisonCalls env registry left.applicationPrefix right.applicationPrefix) :
    DisplaySortableCoherence env U registry left right :=
  left.applicationPrefix.compareSortable right.applicationPrefix henv hscoped leftBelow rightBelow calls

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
