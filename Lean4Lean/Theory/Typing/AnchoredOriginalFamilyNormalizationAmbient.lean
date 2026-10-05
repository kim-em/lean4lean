import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyNormalizationRoute
import Lean4Lean.Theory.Typing.AnchoredOriginalRawTypeRouteAmbient

/-! Every environment in the initial normalization route comes from the
actual constant installation. Empty generated frames alone cannot establish
these inclusions. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

theorem RichHeaderSelection.headerBelow
    (selection : RichHeaderSelection sourceEnv U name levels ordered) :
    selection.header.source ≤ sourceEnv :=
  (Classical.choice (ordered.constantHeaderOrigin selection.lookup)).sourceBelow

theorem RawGeneratedTypeRoute.sameExpression_ambient
    (left : OriginalNestedDisplay U common leftExpression leftAssigned)
    (right : OriginalNestedDisplay U common rightExpression rightAssigned)
    (same : leftExpression = rightExpression)
    (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered)
    (initial : List Closure)
    (frame : OriginalTypeRouteFrame env registry target right.graph commonLeft commonRight)
    (leftBelow : left.sourceEnv ≤ env) (rightBelow : right.sourceEnv ≤ env) :
    (RawGeneratedTypeRoute.sameExpression left right same lf rf initial frame).Ambient := by
  cases same
  rw [RawGeneratedTypeRoute.sameExpression, RawGeneratedTypeRoute.Ambient.eq_def]
  exact ⟨leftBelow, rightBelow⟩

theorem RichHeaderSelection.normalizationRoute_ambient
    {info : VProjectionInfo} {ordered : sourceEnv.Ordered}
    (selection : RichHeaderSelection sourceEnv U name levels ordered)
    (registered : sourceEnv.projections name info) (positive : 0 < info.nparams)
    (below : sourceEnv ≤ env) (common : List VExpr)
    (registry : CanonicalHead.Registry) (target : List VExpr) (left right : Subst) :
    (selection.normalizationRoute registered positive below common registry target left right).Ambient := by
  let packet := selectProjectionParameters ordered registered selection.seedWF
  rw [normalizationRoute, RawGeneratedTypeRoute.Ambient.eq_def]
  constructor
  · rw [RawGeneratedTypeRoute.Ambient.eq_def]
    exact selection.headerBelow.trans below
  · apply RawGeneratedTypeRoute.sameExpression_ambient
    · exact packet.origin.baseBelow.trans below
    · exact packet.origin.baseBelow.trans below

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
