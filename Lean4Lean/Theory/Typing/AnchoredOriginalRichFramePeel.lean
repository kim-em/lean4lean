import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichFrame

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- The whole suffix retains the resources of every merged branch. -/
structure OriginalRichFrameSuffix
    {env : VEnv} {registry : CanonicalHead.Registry} {target : List VExpr}
    {context : ContextDerivation sourceEnv U source}
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (locals : List Nat) (left right : Subst) (available : Valuation) where
  tailLocals : List Nat
  frame : OriginalRichFrame sourceEnv env U registry target context tailLocals
    left.tail right.tail (fun i => available (i + 1))
  positions : Locals.push tailLocals = locals

private noncomputable def headerSuffix
    {capturedEnv : VEnv}
    {header : EndpointRef sourceEnv U [] he ht}
    {field : EndpointRef capturedEnv U capturedSource fe ft}
    {major : EndpointRef capturedEnv U capturedSource me majorType}
    {context : ContextDerivation sourceEnv U source}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    (capturedOrdered : capturedEnv.Ordered) (initial : List Closure)
    (frame : HeaderBinderFrame header field major env registry target
      (.cons context domain) locals left right available) :
    OriginalRichFrameSuffix (context := context) (env := env) (registry := registry) (target := target)
      domain locals left right available := by
  cases frame with
  | bind tail domain location lineage certificate resources typed arguments needs bounded covered =>
    exact ⟨_, .header capturedOrdered initial tail, rfl⟩
  | captured tail =>
    cases tail with
    | skip tail domain location lineage arguments =>
      exact ⟨_, .header capturedOrdered initial (.captured tail), rfl⟩
    | push tail domain location lineage owner answer arguments needs bounded covered =>
      exact ⟨_, .header capturedOrdered initial (.captured tail), rfl⟩

noncomputable def OriginalRichFrame.peel
    {context : ContextDerivation sourceEnv U source}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    (frame : OriginalRichFrame sourceEnv env U registry target
      (.cons context domain) locals left right available) :
    OriginalRichFrameSuffix (context := context) (env := env) (registry := registry) (target := target)
      domain locals left right available := by
  rcases frame with ⟨raw, valid⟩
  match raw, valid with
  | .reserve frame _, valid =>
    exact (OriginalRichFrame.mk frame (by simpa only [RawOriginalRichFrame.Valid] using valid)).peel
  | .header ordered initial frame, _ => exact headerSuffix ordered initial frame
  | .bind tail domain .., valid => exact ⟨_, ⟨tail, by simpa only [RawOriginalRichFrame.Valid] using valid⟩, rfl⟩
  | .capture tail domain .., valid => exact ⟨_, ⟨tail, by simpa only [RawOriginalRichFrame.Valid] using valid⟩, rfl⟩
  | .group tail domain _ _ entries, valid =>
    simp only [RawOriginalRichFrame.Valid] at valid
    exact ⟨_, ⟨tail, valid.1⟩, rfl⟩
  | .merge first second, valid =>
    simp only [RawOriginalRichFrame.Valid] at valid
    let firstSuffix := OriginalRichFrame.peel ⟨first, valid.1⟩
    let secondSuffix := OriginalRichFrame.peel ⟨second, valid.2⟩
    have same : firstSuffix.tailLocals = secondSuffix.tailLocals := by
      have positions := firstSuffix.positions.trans secondSuffix.positions.symm
      exact (List.map_inj_right (fun _ _ h => Nat.succ.inj h)).mp (List.cons.inj positions).2
    let secondFrame := same.symm ▸ secondSuffix.frame
    exact ⟨_, firstSuffix.frame.merge secondFrame, firstSuffix.positions⟩
termination_by sizeOf frame.raw
decreasing_by all_goals simp_wf <;> omega

theorem OriginalRichFrameSuffix.closed
    {context : ContextDerivation sourceEnv U source}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    (suffix : OriginalRichFrameSuffix (env := env) (registry := registry) (target := target)
      (context := context) domain locals left right available)
    (closed : available.AtomClosed) :
    Valuation.AtomClosed (fun i => available (i + 1)) := by
  intro i need member atom atomMember
  exact closed (i + 1) need member atom atomMember

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
