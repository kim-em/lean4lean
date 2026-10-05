import Lean4Lean.Theory.Typing.AnchoredOriginalRichFrameAmbient
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFramePeelMeasure

/-! Peeling keeps the full suffix across merges and preserves every retained
owner environment, including after dropping a head-local reserve. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private headerMeasuredSuffix from Lean4Lean.Theory.Typing.AnchoredOriginalRichFramePeelMeasure
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096

private theorem ambient_castLocals
    {context : ContextDerivation sourceEnv U source}
    {frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (ambient : frame.Ambient) (same : locals = other) :
    (same ▸ frame : OriginalRichFrame sourceEnv env U registry target context other σ τ available).Ambient := by
  cases same
  exact ambient

private theorem headerSuffix_ambient
    {header : EndpointRef sourceEnv U [] he ht}
    {field : EndpointRef capturedEnv U capturedSource fe ft}
    {major : EndpointRef capturedEnv U capturedSource me majorType}
    {context : ContextDerivation sourceEnv U source}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    (ordered : capturedEnv.Ordered) (initial : List Closure)
    (frame : HeaderBinderFrame header field major env registry target (.cons context domain) locals σ τ available)
    (below : sourceEnv ≤ env) (capturedBelow : capturedEnv ≤ env) :
    (headerMeasuredSuffix ordered initial frame).val.frame.Ambient := by
  cases frame with
  | bind tail =>
    change (OriginalRichFrame.header ordered initial tail).Ambient
    unfold OriginalRichFrame.Ambient OriginalRichFrame.header
    rw [RawOriginalRichFrame.Ambient.eq_def]
    exact ⟨below, capturedBelow⟩
  | captured tail =>
    cases tail with
    | skip tail =>
      change (OriginalRichFrame.header ordered initial (.captured tail)).Ambient
      unfold OriginalRichFrame.Ambient OriginalRichFrame.header
      rw [RawOriginalRichFrame.Ambient.eq_def]
      exact ⟨below, capturedBelow⟩
    | push tail =>
      change (OriginalRichFrame.header ordered initial (.captured tail)).Ambient
      unfold OriginalRichFrame.Ambient OriginalRichFrame.header
      rw [RawOriginalRichFrame.Ambient.eq_def]
      exact ⟨below, capturedBelow⟩

/-- The actual fullTail computation, not an independently selected suffix,
preserves ambient inclusion through both branches of a merge. -/
private theorem rawFullTailAmbient
    {context : ContextDerivation sourceEnv U source}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    (raw : RawOriginalRichFrame sourceEnv env U registry target (.cons context domain) locals σ τ available)
    (valid : raw.Valid) (ambient : raw.Ambient) :
    (OriginalRichFrame.mk raw valid).fullTail.frame.Ambient := by
  match raw, valid with
  | .reserve previous closures, valid =>
    rw [RawOriginalRichFrame.Ambient.eq_def] at ambient
    unfold OriginalRichFrame.fullTail
    rw [OriginalRichFrame.peelMeasuredData.eq_def]
    dsimp only
    exact (rawFullTailAmbient previous (by simpa only [RawOriginalRichFrame.Valid] using valid) ambient.2)
  | .header ordered initial frame, valid =>
    rw [RawOriginalRichFrame.Ambient.eq_def] at ambient
    unfold OriginalRichFrame.fullTail
    rw [OriginalRichFrame.peelMeasuredData.eq_def]
    dsimp only
    exact headerSuffix_ambient ordered initial frame ambient.1 ambient.2
  | .bind previous domain .., valid =>
    rw [RawOriginalRichFrame.Ambient.eq_def] at ambient
    unfold OriginalRichFrame.fullTail
    rw [OriginalRichFrame.peelMeasuredData.eq_def]
    dsimp only
    exact ambient.2
  | .capture previous domain .., valid =>
    rw [RawOriginalRichFrame.Ambient.eq_def] at ambient
    unfold OriginalRichFrame.fullTail
    rw [OriginalRichFrame.peelMeasuredData.eq_def]
    dsimp only
    exact ambient.2
  | .group previous domain ordered initial entries, valid =>
    rw [RawOriginalRichFrame.Ambient.eq_def] at ambient
    unfold OriginalRichFrame.fullTail
    rw [OriginalRichFrame.peelMeasuredData.eq_def]
    dsimp only
    exact ambient.2.1
  | .merge first second, valid =>
    rw [RawOriginalRichFrame.Ambient.eq_def] at ambient
    unfold OriginalRichFrame.fullTail
    rw [OriginalRichFrame.peelMeasuredData.eq_def]
    dsimp only
    simp only [RawOriginalRichFrame.Valid] at valid
    have firstAmbient := rawFullTailAmbient first valid.1 ambient.2.1
    have secondAmbient := rawFullTailAmbient second valid.2 ambient.2.2
    exact firstAmbient.merge (ambient_castLocals secondAmbient _)
termination_by sizeOf raw
decreasing_by all_goals simp_wf <;> omega

theorem OriginalRichFrame.Ambient.fullTail
    {context : ContextDerivation sourceEnv U source}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    (frame : OriginalRichFrame sourceEnv env U registry target (.cons context domain) locals σ τ available)
    (ambient : frame.Ambient) : frame.fullTail.frame.Ambient :=
  rawFullTailAmbient frame.raw frame.valid ambient

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
