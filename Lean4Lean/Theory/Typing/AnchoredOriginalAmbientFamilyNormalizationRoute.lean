import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientTypeRouteGeneration
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyNormalizationAmbient

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096

theorem closedTypeRouteFrame_ambientGenerated
    (context : ContextDerivation sourceEnv U []) (common : List VExpr)
    {base : OriginalCaptureBase env U registry target} (caps : CaptureCaps)
    (left right : Subst) (below : sourceEnv ≤ env) :
    AmbientCaptureGenerated base caps left right (closedCaptureGraph context common)
      (closedTypeRouteFrame context common env registry target left right).realization.frame.raw := by
  cases context
  exact .empty common left right below

theorem normalizedFamilyRouteFrame_ambientGenerated
    (packet : OriginalProjectionParameters sourceEnv U name info levels)
    (positive : 0 < info.nparams) (common : List VExpr)
    {base : OriginalCaptureBase env U registry target} (caps : CaptureCaps)
    (left right : Subst) (below : packet.origin.base ≤ env) :
    AmbientCaptureGenerated base caps left right (normalizedFamilyRouteSide packet positive common).graph
      (normalizedFamilyRouteFrame packet positive common env registry target left right).realization.frame.raw :=
  closedTypeRouteFrame_ambientGenerated _ common caps left right below

theorem RawGeneratedTypeRoute.sameExpression_ambientGenerated
    (left : OriginalNestedDisplay U common leftExpression leftAssigned)
    (right : OriginalNestedDisplay U common rightExpression rightAssigned)
    (same : leftExpression = rightExpression)
    (leftOrdered : left.sourceEnv.Ordered) (rightOrdered : right.sourceEnv.Ordered)
    (initial : List Closure)
    (frame : OriginalTypeRouteFrame env registry target right.graph commonLeft commonRight)
    (leftBelow : left.sourceEnv ≤ env)
    (generated : AmbientCaptureGenerated base commonCaps commonLeft commonRight right.graph frame.realization.frame.raw) :
    (sameExpression left right same leftOrdered rightOrdered initial frame).AmbientGenerated base commonCaps := by
  cases same
  refine ⟨?_, ?_, ?_⟩
  · rw [sameExpression, WellFormed.eq_def]; trivial
  · rw [sameExpression, Ambient.eq_def]
    exact ⟨leftBelow, generated.ambient.1.below⟩
  · intro boxed member
    simp only [sameExpression, frames.eq_def, List.mem_singleton] at member
    subst boxed
    exact generated

theorem RichHeaderSelection.normalizationRoute_ambientGenerated
    {info : VProjectionInfo} {ordered : sourceEnv.Ordered}
    (selection : RichHeaderSelection sourceEnv U name levels ordered)
    (registered : sourceEnv.projections name info) (positive : 0 < info.nparams)
    (below : sourceEnv ≤ env) (common : List VExpr)
    {base : OriginalCaptureBase env U registry target} (caps : CaptureCaps) (left right : Subst) :
    (selection.normalizationRoute registered positive below common registry target left right).AmbientGenerated base caps := by
  let packet := selectProjectionParameters ordered registered selection.seedWF
  have last := RawGeneratedTypeRoute.sameExpression_ambientGenerated
    ((closedCaptureGraph (ContextDerivation.nil (env := packet.origin.base) (U := U)) common).typeEqualityDisplay
      packet.instantiated.normalization false)
    (normalizedFamilyRouteSide packet positive common).display
    (congrArg (fun expression => expression.subst Subst.id) (normalizedFamilyPrefix packet positive).shape)
    packet.origin.baseOrdered packet.origin.baseOrdered
    ((closedTypeRouteFrame (ContextDerivation.nil (U := U)) common env registry target left right).realization.frame.dependencyEnvironment
      packet.origin.baseOrdered)
    (normalizedFamilyRouteFrame packet positive common env registry target left right)
    (packet.origin.baseBelow.trans below)
    (normalizedFamilyRouteFrame_ambientGenerated packet positive common caps left right
      (packet.origin.baseBelow.trans below) (base := base))
  refine ⟨?_, selection.normalizationRoute_ambient registered positive below common registry target left right, ?_⟩
  · rw [normalizationRoute, RawGeneratedTypeRoute.WellFormed.eq_def]
    refine ⟨?_, last.wellFormed⟩
    rw [RawGeneratedTypeRoute.WellFormed.eq_def]
    trivial
  · intro boxed member
    rw [normalizationRoute, RawGeneratedTypeRoute.frames.eq_def] at member
    rcases List.mem_append.mp member with first | final
    · rw [RawGeneratedTypeRoute.frames.eq_def, List.mem_singleton] at first
      subst boxed
      exact closedTypeRouteFrame_ambientGenerated .nil common caps left right (packet.origin.baseBelow.trans below)
    · exact last.frames boxed final


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
