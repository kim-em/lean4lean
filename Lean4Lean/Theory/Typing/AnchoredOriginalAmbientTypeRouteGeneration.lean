import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientCaptureGeneration
import Lean4Lean.Theory.Typing.AnchoredOriginalRawTypeRouteGeneration

/-! Positive generation for every actual history leaf. This retains dormant
capture histories and owner scopes, and includes the environments of edges
whose route has no frame leaves. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target common : List VExpr}

structure RawGeneratedTypeRoute.AmbientGenerated
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final)
    (base : OriginalCaptureBase env U registry target) (caps : CaptureCaps) : Prop where
  wellFormed : route.WellFormed
  ambient : route.Ambient
  frames : ∀ boxed ∈ route.frames, AmbientCaptureGenerated base caps commonLeft commonRight
    boxed.graph boxed.frame.realization.frame.raw

theorem RawGeneratedTypeRoute.AmbientGenerated.generated
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    {route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    (generated : route.AmbientGenerated base caps) : route.Generated base caps :=
  ⟨generated.wellFormed, fun boxed member => (generated.frames boxed member).capped⟩

theorem RawGeneratedTypeRoute.AmbientGenerated.trans
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {middle : OriginalNestedDisplay U common middleExpression middleAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    {first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate}
    {second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    (firstGenerated : first.AmbientGenerated base caps)
    (secondGenerated : second.AmbientGenerated base caps) :
    (first.trans second).AmbientGenerated base caps := by
  refine ⟨?_, ?_, ?_⟩
  · rw [RawGeneratedTypeRoute.WellFormed.eq_def]
    exact ⟨firstGenerated.wellFormed, secondGenerated.wellFormed⟩
  · rw [RawGeneratedTypeRoute.Ambient.eq_def]
    exact ⟨firstGenerated.ambient, secondGenerated.ambient⟩
  · intro boxed member
    rw [RawGeneratedTypeRoute.frames.eq_def] at member
    exact (List.mem_append.mp member).elim (firstGenerated.frames boxed) (secondGenerated.frames boxed)

theorem RawGeneratedTypeRoute.AmbientGenerated.trans_left
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {middle : OriginalNestedDisplay U common middleExpression middleAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    {first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate}
    {second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    (generated : (first.trans second).AmbientGenerated base caps) : first.AmbientGenerated base caps := by
  have wellFormed := generated.wellFormed
  have ambient := generated.ambient
  rw [RawGeneratedTypeRoute.WellFormed.eq_def] at wellFormed
  rw [RawGeneratedTypeRoute.Ambient.eq_def] at ambient
  exact ⟨wellFormed.1, ambient.1, fun boxed member => generated.frames boxed
    (by rw [RawGeneratedTypeRoute.frames.eq_def]; exact List.mem_append_left _ member)⟩

theorem RawGeneratedTypeRoute.AmbientGenerated.trans_right
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {middle : OriginalNestedDisplay U common middleExpression middleAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    {first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate}
    {second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    (generated : (first.trans second).AmbientGenerated base caps) : second.AmbientGenerated base caps := by
  have wellFormed := generated.wellFormed
  have ambient := generated.ambient
  rw [RawGeneratedTypeRoute.WellFormed.eq_def] at wellFormed
  rw [RawGeneratedTypeRoute.Ambient.eq_def] at ambient
  exact ⟨wellFormed.2, ambient.2, fun boxed member => generated.frames boxed
    (by rw [RawGeneratedTypeRoute.frames.eq_def]; exact List.mem_append_right _ member)⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
