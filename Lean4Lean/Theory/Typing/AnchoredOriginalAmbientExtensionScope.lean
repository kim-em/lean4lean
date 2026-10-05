import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientCaptureGeneration

/-! Original binder extensions preserve hereditary ambient generation at
the actual computed common scope and finite caps. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- Every hidden owner extension inherits all outer common caps. Its new
original binders get exactly the finite inputs of their retained guards. -/
theorem OriginalFrameExtension.generateAmbientScope
    {base : OriginalCaptureBase env U registry target}
    {startContext : ContextDerivation sourceEnv U startSource}
    {graph : OriginalCaptureMap (common := common) startContext raw}
    {start : RawOriginalRichFrame sourceEnv env U registry target startContext startLocals startLeft startRight startAvailable}
    {context : ContextDerivation sourceEnv U source}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (extension : OriginalFrameExtension start frame)
    (generated : AmbientCaptureGenerated base commonCaps commonLeft commonRight graph start) :
    ∃ nextCommon nextRaw nextLeft nextRight nextCaps,
      ∃ nextGraph : OriginalCaptureMap (common := nextCommon) context nextRaw,
      AmbientCaptureGenerated base nextCaps nextLeft nextRight nextGraph frame ∧
      nextRaw = raw.liftN extension.length ∧
      Ctx.Lift' (.skipN .refl extension.length) common nextCommon ∧
      Subst.lift_l (.skipN .refl extension.length) nextLeft = commonLeft ∧
      Subst.lift_l (.skipN .refl extension.length) nextRight = commonRight ∧
      (fun index => nextCaps ((Lift.skipN .refl extension.length).liftVar index)) = commonCaps := by
  induction extension with
  | refl => exact ⟨_, _, _, _, _, graph, generated, rfl, .refl, rfl, rfl, rfl⟩
  | bind previous domain certificate resources typed arguments needs bounded covered ih =>
    obtain ⟨nextCommon, nextRaw, nextLeft, nextRight, nextCaps, nextGraph, nextGenerated,
      rawEq, insertion, leftTail, rightTail, capsTail⟩ := ih
    refine ⟨_, nextRaw.lift, _, _, _, .bind nextGraph domain _ rfl,
      .bind nextGenerated domain _ rfl certificate resources typed arguments needs bounded covered,
      ?_, .skip insertion, ?_, ?_, ?_⟩
    · rw [rawEq]; rfl
    · exact OriginalFactorCut.capture_tail_cons _ _ _ _ leftTail
    · exact OriginalFactorCut.capture_tail_cons _ _ _ _ rightTail
    · exact capsTail


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
