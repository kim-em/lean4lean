import Lean4Lean.Theory.Typing.AnchoredOriginalRawTypeRouteOperations
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRouteProvenance
import Lean4Lean.Theory.Typing.AnchoredOriginalSourceTypeRouteGeneration

/-! Structural transports for the actual annotated route and its finite source generation. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

private theorem environment_worlds_mpr
    {first second : List OriginalClosureMeasure.Closure}
    (indices : first = second)
    (equal : WorldEnvironmentProvenance strata U first = WorldEnvironmentProvenance strata U second)
    (annotation : WorldEnvironmentProvenance strata U second) :
    (equal.mpr annotation).worlds = annotation.worlds := by
  cases indices
  cases equal
  rfl

private noncomputable def trans_worldInputs
    {strata : EquationStratification env}
    {first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate}
    {second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final}
    (firstInput : first.WorldInputs strata) (secondInput : second.WorldInputs strata) :
    (first.trans second).WorldInputs strata := by
  rw [RawGeneratedTypeRoute.WorldInputs.eq_def]
  exact ⟨firstInput, secondInput⟩

private theorem trans_worldReserve
    {strata : EquationStratification env}
    {first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate}
    {second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final}
    (firstInput : first.WorldInputs strata) (secondInput : second.WorldInputs strata) :
    ((first.trans second).worldReserve (trans_worldInputs firstInput secondInput)).worlds =
      (first.worldReserve firstInput).worlds ++ (second.worldReserve secondInput).worlds := by
  simp only [RawGeneratedTypeRoute.worldReserve, RawGeneratedTypeRoute.WorldInputs, trans_worldInputs]
  rw [environment_worlds_mpr (RawGeneratedTypeRoute.reserve.eq_def (first.trans second))]
  exact WorldEnvironmentProvenance.worlds_append _ _

namespace RetainedHeaderUniverse

private theorem source_trans
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {middle : OriginalNestedDisplay U common middleExpression middleAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    {first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate}
    {second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final}
    (firstGenerated : first.SourceGenerated P base caps)
    (secondGenerated : second.SourceGenerated P base caps) :
    (first.trans second).SourceGenerated P base caps := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [RawGeneratedTypeRoute.WellFormed.eq_def]
    exact ⟨firstGenerated.wellFormed, secondGenerated.wellFormed⟩
  · rw [RawGeneratedTypeRoute.Ambient.eq_def]
    exact ⟨firstGenerated.ambient, secondGenerated.ambient⟩
  · rw [RawGeneratedTypeRoute.AllSources.eq_def]
    exact ⟨firstGenerated.sources.left, secondGenerated.sources.right,
      firstGenerated.sources, secondGenerated.sources⟩
  · intro boxed member
    rw [RawGeneratedTypeRoute.frames.eq_def] at member
    exact (List.mem_append.mp member).elim (firstGenerated.frames boxed) (secondGenerated.frames boxed)

private theorem source_same
    (left : OriginalNestedDisplay U common leftExpression leftAssigned)
    (right : OriginalNestedDisplay U common rightExpression rightAssigned)
    (same : leftExpression = rightExpression)
    (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered)
    (initial : List Closure)
    (frame : OriginalTypeRouteFrame env registry target right.graph commonLeft commonRight)
    (leftBelow : left.sourceEnv ≤ env) (rightBelow : right.sourceEnv ≤ env)
    (leftSource : P left.sourceEnv) (rightSource : P right.sourceEnv)
    (generated : SourceCaptureGenerated P base caps commonLeft commonRight right.graph frame.realization.frame.raw) :
    (RawGeneratedTypeRoute.sameExpression left right same lf rf initial frame).SourceGenerated P base caps := by
  cases same
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [RawGeneratedTypeRoute.sameExpression, RawGeneratedTypeRoute.WellFormed.eq_def]; trivial
  · rw [RawGeneratedTypeRoute.sameExpression, RawGeneratedTypeRoute.Ambient.eq_def]
    exact ⟨leftBelow, rightBelow⟩
  · rw [RawGeneratedTypeRoute.sameExpression, RawGeneratedTypeRoute.AllSources.eq_def]
    exact ⟨leftSource, rightSource, trivial⟩
  · intro boxed member
    rw [RawGeneratedTypeRoute.sameExpression, RawGeneratedTypeRoute.frames.eq_def,
      List.mem_singleton] at member
    subst boxed
    exact generated

end RetainedHeaderUniverse

private theorem nestedDisplay_heq
    (context : ContextDerivation sourceEnv U source)
    (node : EndpointState sourceEnv U source expression assigned)
    (provenance : EndpointProvenance context node)
    (graph : OriginalCaptureMap (common := common) context raw)
    (first : firstExpression = expression.subst raw)
    (second : secondExpression = expression.subst raw)
    (typed : commonType = assigned.subst raw) :
    HEq
      (OriginalNestedDisplay.mk sourceEnv source expression assigned context node provenance raw graph first typed)
      (OriginalNestedDisplay.mk sourceEnv source expression assigned context node provenance raw graph second typed) := by
  cases first
  cases second
  rfl


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
