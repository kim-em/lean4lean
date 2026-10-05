import Lean4Lean.Theory.Typing.AnchoredOriginalRichFrameHeadDepth
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFramePeelMeasure

/-! Taking the computed full suffix preserves every declaration-depth bound.
The proof follows the actual peel operation, including both merge branches
and the locals cast used to join them. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private headerMeasuredSuffix from Lean4Lean.Theory.Typing.AnchoredOriginalRichFramePeelMeasure
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096

private theorem headDepth_castLocals (policy : Name → Nat → Nat)
    {context : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (same : locals = other) :
    (same ▸ frame : OriginalRichFrame sourceEnv env U registry target context other σ τ available).headDepth policy =
      frame.headDepth policy := by
  cases same
  rfl

private theorem headerSuffix_headDepth (policy : Name → Nat → Nat)
    {header : EndpointRef sourceEnv U [] he ht}
    {field : EndpointRef capturedEnv U capturedSource fe ft}
    {major : EndpointRef capturedEnv U capturedSource me majorType}
    {context : ContextDerivation sourceEnv U source}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    (ordered : capturedEnv.Ordered) (initial : List Closure)
    (frame : HeaderBinderFrame header field major env registry target (.cons context domain) locals σ τ available) :
    (headerMeasuredSuffix ordered initial frame).val.frame.headDepth policy ≤ frame.headDepth policy := by
  cases frame with
  | bind tail =>
    change (OriginalRichFrame.header ordered initial tail).headDepth policy ≤ _
    simp only [OriginalRichFrame.headDepth, OriginalRichFrame.header,
      RawOriginalRichFrame.headDepth, HeaderBinderFrame.headDepth]
    exact Nat.le_max_right _ _
  | captured tail =>
    cases tail with
    | skip tail =>
      change (OriginalRichFrame.header ordered initial (.captured tail)).headDepth policy ≤ _
      simp only [OriginalRichFrame.headDepth, OriginalRichFrame.header,
        RawOriginalRichFrame.headDepth, HeaderBinderFrame.headDepth, HeaderRichTail.headDepth]
      exact Nat.le_refl _
    | push tail =>
      change (OriginalRichFrame.header ordered initial (.captured tail)).headDepth policy ≤ _
      simp only [OriginalRichFrame.headDepth, OriginalRichFrame.header,
        RawOriginalRichFrame.headDepth, HeaderBinderFrame.headDepth, HeaderRichTail.headDepth]
      exact Nat.le_max_right _ _

private theorem rawFullTail_headDepth (policy : Name → Nat → Nat)
    {context : ContextDerivation sourceEnv U source}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    (raw : RawOriginalRichFrame sourceEnv env U registry target (.cons context domain) locals σ τ available)
    (valid : raw.Valid) :
    (OriginalRichFrame.mk raw valid).fullTail.frame.headDepth policy ≤ raw.headDepth policy := by
  match raw, valid with
  | .reserve previous closures, valid =>
    unfold OriginalRichFrame.fullTail
    rw [OriginalRichFrame.peelMeasuredData.eq_def]
    dsimp only
    simpa only [OriginalRichFrame.fullTail, RawOriginalRichFrame.headDepth] using
      rawFullTail_headDepth policy previous (by simpa only [RawOriginalRichFrame.Valid] using valid)
  | .header ordered initial frame, valid =>
    unfold OriginalRichFrame.fullTail
    rw [OriginalRichFrame.peelMeasuredData.eq_def]
    dsimp only
    simpa only [RawOriginalRichFrame.headDepth] using headerSuffix_headDepth policy ordered initial frame
  | .bind previous domain .., valid =>
    unfold OriginalRichFrame.fullTail
    rw [OriginalRichFrame.peelMeasuredData.eq_def]
    simp only [OriginalRichFrame.headDepth, RawOriginalRichFrame.headDepth]
    exact Nat.le_max_right _ _
  | .capture previous domain .., valid =>
    unfold OriginalRichFrame.fullTail
    rw [OriginalRichFrame.peelMeasuredData.eq_def]
    simp only [OriginalRichFrame.headDepth, RawOriginalRichFrame.headDepth]
    exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  | .group previous domain ordered initial entries, valid =>
    unfold OriginalRichFrame.fullTail
    rw [OriginalRichFrame.peelMeasuredData.eq_def]
    simp only [OriginalRichFrame.headDepth, RawOriginalRichFrame.headDepth]
    exact Nat.le_max_right _ _
  | .merge first second, valid =>
    unfold OriginalRichFrame.fullTail
    rw [OriginalRichFrame.peelMeasuredData.eq_def]
    dsimp only
    simp only [RawOriginalRichFrame.Valid] at valid
    rw [OriginalRichFrame.headDepth_merge, headDepth_castLocals]
    simp only [RawOriginalRichFrame.headDepth]
    exact Nat.max_le.mpr ⟨
      Nat.le_trans (rawFullTail_headDepth policy first valid.1) (Nat.le_max_left _ _),
      Nat.le_trans (rawFullTail_headDepth policy second valid.2) (Nat.le_max_right _ _)⟩
termination_by sizeOf raw
decreasing_by all_goals simp_wf <;> omega

/-- This bounds the actual `fullTail.frame`, simultaneously for every
declaration control, without choosing a different suffix. -/
theorem OriginalRichFrame.headDepth_fullTail
    {context : ContextDerivation sourceEnv U source}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    (frame : OriginalRichFrame sourceEnv env U registry target (.cons context domain) locals σ τ available)
    (policy : Name → Nat → Nat) :
    frame.fullTail.frame.headDepth policy ≤ frame.headDepth policy :=
  rawFullTail_headDepth policy frame.raw frame.valid

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
