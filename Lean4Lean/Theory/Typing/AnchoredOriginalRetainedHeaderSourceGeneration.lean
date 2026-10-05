import Lean4Lean.Theory.Typing.AnchoredOriginalRetainedHeaderUniverseRoute
import Lean4Lean.Theory.Typing.AnchoredOriginalSourceTypeRouteGeneration

/-! Positive generation for the actual retained universe route. No semantic interpreter is imported. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

namespace RetainedHeaderUniverse

theorem sourceGenerated_trans
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

theorem sourceGenerated_same
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

/-- Every route leaf has positive source generation, even for a predicate
that retains the caller's equation cutoff in addition to declaration stage. -/
theorem route_sourceGenerated
    {U : Nat} {leftLevels rightLevels : List VLevel} {P : VEnv → Prop}
    (leftOrigin : ConstantHeaderOrigin leftEnv name info)
    (rightOrigin : ConstantHeaderOrigin rightEnv name info)
    (leftWF : ∀ level ∈ leftLevels, level.WF U)
    (rightWF : ∀ level ∈ rightLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) leftLevels rightLevels)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env) (common : List VExpr)
    {base : OriginalCaptureBase env U registry target} (caps : CaptureCaps) (left right : Subst)
    (leftSource : P leftOrigin.source) (rightSource : P rightOrigin.source) :
    (route leftOrigin rightOrigin leftWF rightWF equivalent rightBelow common registry target left right).SourceGenerated
      P base caps := by
  let equality := original rightOrigin leftWF rightWF equivalent
  let graph := closedCaptureGraph (ContextDerivation.nil (env := rightOrigin.source) (U := U)) common
  have positive : SourceCaptureGenerated P base caps left right graph
      (closedTypeRouteFrame .nil common env registry target left right).realization.frame.raw :=
    .empty common left right (rightOrigin.sourceBelow.trans rightBelow) rightSource
  have first := sourceGenerated_same
    (display leftOrigin leftWF common) (graph.typeEqualityDisplay equality true)
    subst_id.symm leftOrigin.ordered rightOrigin.ordered []
    (closedTypeRouteFrame .nil common env registry target left right)
    (leftOrigin.sourceBelow.trans leftBelow) (rightOrigin.sourceBelow.trans rightBelow)
    leftSource rightSource positive
  have middle : (RawGeneratedTypeRoute.equality (registry := registry) (target := target)
      (commonLeft := left) (commonRight := right) graph equality true rightOrigin.ordered
      (rightOrigin.sourceBelow.trans rightBelow) []).SourceGenerated P base caps := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [RawGeneratedTypeRoute.WellFormed.eq_def]; trivial
    · rw [RawGeneratedTypeRoute.Ambient.eq_def]; trivial
    · rw [RawGeneratedTypeRoute.AllSources.eq_def]
      exact ⟨rightSource, rightSource, trivial⟩
    · intro boxed member
      rw [RawGeneratedTypeRoute.frames.eq_def] at member
      cases member
  have last := sourceGenerated_same
    (graph.typeEqualityDisplay equality false) (display rightOrigin rightWF common)
    subst_id rightOrigin.ordered rightOrigin.ordered []
    (frame rightOrigin rightWF common env registry target left right)
    (rightOrigin.sourceBelow.trans rightBelow) (rightOrigin.sourceBelow.trans rightBelow)
    rightSource rightSource positive
  exact sourceGenerated_trans first (sourceGenerated_trans middle last)

end RetainedHeaderUniverse

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
