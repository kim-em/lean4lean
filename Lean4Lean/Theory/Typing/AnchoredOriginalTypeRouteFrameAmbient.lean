import Lean4Lean.Theory.Typing.AnchoredOriginalRawTypeRouteAmbient
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFrameAmbient
import Lean4Lean.Theory.Typing.AnchoredOriginalSourceCaptureGraphAmbient
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyNormalizationAmbient

/-! Route leaves retain both nominal source-map provenance and the actual
owner frames used by replay. Inclusion of only the displayed endpoints does
not establish either hereditary property. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

def OriginalTypeRouteFrame.Ambient
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight) : Prop :=
  graph.Ambient env ∧ frame.realization.frame.Ambient

def OriginalTypeRouteFrameBox.Ambient
    (boxed : OriginalTypeRouteFrameBox env U registry target common commonLeft commonRight) : Prop :=
  boxed.frame.Ambient

def RawGeneratedTypeRoute.FramesAmbient
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final) : Prop :=
  ∀ boxed ∈ route.frames, boxed.Ambient

theorem closedTypeRouteFrame_ambient
    (context : ContextDerivation sourceEnv U []) (common : List VExpr)
    (below : sourceEnv ≤ env) (registry : CanonicalHead.Registry)
    (target : List VExpr) (left right : Subst) :
    (closedTypeRouteFrame context common env registry target left right).Ambient := by
  cases context
  refine ⟨OriginalCaptureMap.Ambient.empty below common, ?_⟩
  change (RawOriginalRichFrame.nil (env := env) (sourceEnv := sourceEnv)).Ambient
  rw [RawOriginalRichFrame.Ambient.eq_def]
  exact ⟨below, trivial⟩

theorem RawGeneratedTypeRoute.FramesAmbient.trans
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {middle : OriginalNestedDisplay U common middleExpression middleAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    {first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate}
    {second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final}
    (firstAmbient : first.FramesAmbient) (secondAmbient : second.FramesAmbient) :
    (first.trans second).FramesAmbient := by
  intro boxed member
  rw [RawGeneratedTypeRoute.frames.eq_def] at member
  exact (List.mem_append.mp member).elim (firstAmbient boxed) (secondAmbient boxed)

theorem RawGeneratedTypeRoute.sameExpression_framesAmbient
    (left : OriginalNestedDisplay U common leftExpression leftAssigned)
    (right : OriginalNestedDisplay U common rightExpression rightAssigned)
    (same : leftExpression = rightExpression)
    (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered)
    (initial : List Closure)
    (frame : OriginalTypeRouteFrame env registry target right.graph commonLeft commonRight)
    (ambient : frame.Ambient) :
    (RawGeneratedTypeRoute.sameExpression left right same lf rf initial frame).FramesAmbient := by
  cases same
  intro boxed member
  rw [RawGeneratedTypeRoute.sameExpression, RawGeneratedTypeRoute.frames.eq_def] at member
  cases List.mem_singleton.mp member
  exact ambient

theorem RichHeaderSelection.normalizationRoute_framesAmbient
    {info : VProjectionInfo} {ordered : sourceEnv.Ordered}
    (selection : RichHeaderSelection sourceEnv U name levels ordered)
    (registered : sourceEnv.projections name info) (positive : 0 < info.nparams)
    (below : sourceEnv ≤ env) (common : List VExpr)
    (registry : CanonicalHead.Registry) (target : List VExpr) (left right : Subst) :
    (selection.normalizationRoute registered positive below common registry target left right).FramesAmbient := by
  let packet := selectProjectionParameters ordered registered selection.seedWF
  rw [normalizationRoute]
  apply RawGeneratedTypeRoute.FramesAmbient.trans
  · intro boxed member
    rw [RawGeneratedTypeRoute.frames.eq_def] at member
    cases List.mem_singleton.mp member
    exact closedTypeRouteFrame_ambient .nil common (packet.origin.baseBelow.trans below) registry target left right
  · apply RawGeneratedTypeRoute.sameExpression_framesAmbient
    exact closedTypeRouteFrame_ambient _ common (packet.origin.baseBelow.trans below) registry target left right

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
