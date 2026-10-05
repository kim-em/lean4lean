import Lean4Lean.Theory.Typing.AnchoredOriginalSourcePredicates
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

theorem OriginalRichFrame.AllSources.merge
    {left : OriginalRichFrame sourceEnv env U registry target context locals σ τ leftAvailable}
    {right : OriginalRichFrame sourceEnv env U registry target context locals σ τ rightAvailable}
    (first : left.AllSources P) (second : right.AllSources P) : (left.merge right).AllSources P := by
  change (RawOriginalRichFrame.merge left.raw right.raw).AllSources P
  rw [RawOriginalRichFrame.AllSources.eq_def]
  exact ⟨RawOriginalRichFrame.AllSources.source first, first, second⟩

private theorem sources_castLocals
    {context : ContextDerivation sourceEnv U sourceContext}
    {frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (ambient : frame.AllSources P) (same : locals = other) :
    (same ▸ frame : OriginalRichFrame sourceEnv env U registry target context other σ τ available).AllSources P := by
  cases same
  exact ambient

private theorem headerSuffix_sources
    {header : EndpointRef sourceEnv U [] he ht}
    {field : EndpointRef capturedEnv U capturedSource fe ft}
    {major : EndpointRef capturedEnv U capturedSource me majorType}
    {context : ContextDerivation sourceEnv U sourceContext}
    {domain : EndpointRef sourceEnv U sourceContext A (.sort level)}
    (ordered : capturedEnv.Ordered) (initial : List Closure)
    (frame : HeaderBinderFrame header field major env registry target (.cons context domain) locals σ τ available)
    (below : P sourceEnv) (capturedBelow : P capturedEnv) :
    (headerMeasuredSuffix ordered initial frame).val.frame.AllSources P := by
  cases frame with
  | bind tail =>
    change (OriginalRichFrame.header ordered initial tail).AllSources P
    unfold OriginalRichFrame.AllSources OriginalRichFrame.header
    rw [RawOriginalRichFrame.AllSources.eq_def]
    exact ⟨below, capturedBelow⟩
  | captured tail =>
    cases tail with
    | skip tail =>
      change (OriginalRichFrame.header ordered initial (.captured tail)).AllSources P
      unfold OriginalRichFrame.AllSources OriginalRichFrame.header
      rw [RawOriginalRichFrame.AllSources.eq_def]
      exact ⟨below, capturedBelow⟩
    | push tail =>
      change (OriginalRichFrame.header ordered initial (.captured tail)).AllSources P
      unfold OriginalRichFrame.AllSources OriginalRichFrame.header
      rw [RawOriginalRichFrame.AllSources.eq_def]
      exact ⟨below, capturedBelow⟩

/-- The actual fullTail computation, not an independently selected suffix,
preserves the source predicate through both branches of a merge. -/
private theorem rawFullTailSources
    {context : ContextDerivation sourceEnv U sourceContext}
    {domain : EndpointRef sourceEnv U sourceContext A (.sort level)}
    (raw : RawOriginalRichFrame sourceEnv env U registry target (.cons context domain) locals σ τ available)
    (valid : raw.Valid) (ambient : raw.AllSources P) :
    (OriginalRichFrame.mk raw valid).fullTail.frame.AllSources P := by
  match raw, valid with
  | .reserve previous closures, valid =>
    rw [RawOriginalRichFrame.AllSources.eq_def] at ambient
    unfold OriginalRichFrame.fullTail
    rw [OriginalRichFrame.peelMeasuredData.eq_def]
    dsimp only
    exact (rawFullTailSources previous (by simpa only [RawOriginalRichFrame.Valid] using valid) ambient.2)
  | .header ordered initial frame, valid =>
    rw [RawOriginalRichFrame.AllSources.eq_def] at ambient
    unfold OriginalRichFrame.fullTail
    rw [OriginalRichFrame.peelMeasuredData.eq_def]
    dsimp only
    exact headerSuffix_sources ordered initial frame ambient.1 ambient.2
  | .bind previous domain .., valid =>
    rw [RawOriginalRichFrame.AllSources.eq_def] at ambient
    unfold OriginalRichFrame.fullTail
    rw [OriginalRichFrame.peelMeasuredData.eq_def]
    dsimp only
    exact ambient.2
  | .capture previous domain .., valid =>
    rw [RawOriginalRichFrame.AllSources.eq_def] at ambient
    unfold OriginalRichFrame.fullTail
    rw [OriginalRichFrame.peelMeasuredData.eq_def]
    dsimp only
    exact ambient.2
  | .group previous domain ordered initial entries, valid =>
    rw [RawOriginalRichFrame.AllSources.eq_def] at ambient
    unfold OriginalRichFrame.fullTail
    rw [OriginalRichFrame.peelMeasuredData.eq_def]
    dsimp only
    exact ambient.2.1
  | .merge first second, valid =>
    rw [RawOriginalRichFrame.AllSources.eq_def] at ambient
    unfold OriginalRichFrame.fullTail
    rw [OriginalRichFrame.peelMeasuredData.eq_def]
    dsimp only
    simp only [RawOriginalRichFrame.Valid] at valid
    have firstAllSources := rawFullTailSources first valid.1 ambient.2.1
    have secondAllSources := rawFullTailSources second valid.2 ambient.2.2
    exact firstAllSources.merge (sources_castLocals secondAllSources _)
termination_by sizeOf raw
decreasing_by all_goals simp_wf <;> omega

theorem OriginalRichFrame.AllSources.fullTail
    {context : ContextDerivation sourceEnv U sourceContext}
    {domain : EndpointRef sourceEnv U sourceContext A (.sort level)}
    (frame : OriginalRichFrame sourceEnv env U registry target (.cons context domain) locals σ τ available)
    (ambient : frame.AllSources P) : frame.fullTail.frame.AllSources P :=
  rawFullTailSources frame.raw frame.valid ambient

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
