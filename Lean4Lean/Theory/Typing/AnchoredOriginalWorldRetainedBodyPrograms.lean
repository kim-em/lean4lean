import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedDemandPrograms
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedBodyWitness

/-! Consume caller programs at the actual native or legacy body edge. The
pending row, old key and continuation are those retained by the SAME body
execution; the next-state program record is constructed without reselection. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

variable {Fits : Nat → Need → Prop}

noncomputable def RetainedBodyTransitionWitness.InputProgram
    {before after : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput}
    (edge : RetainedBodyTransitionWitness before after) (Fits : Nat → Need → Prop) : Type := by
  cases edge with
  | native expressionEq path selected admitted pending row execution continuation member readback normalized worlds depth =>
    exact CallerBinderProgram env U registry target Fits pending.oldKey
  | legacy expressionEq path selected admitted selection execution sameAnnotation continuation member readback normalized worlds depth =>
    exact CallerBinderProgram env U registry target Fits selection.pending.oldKey

private def castDemandPrograms (same : expression = next)
    (demand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput expression atom)
    (programs : demand.InputPrograms Fits) : (same ▸ demand).InputPrograms Fits := by
  cases same
  exact programs

/-- Replay the actual selected input adapter and carry the exact remaining
demand programs into that execution's concrete next state. The old key is
computed by the actual pending row; no matching-key premise is accepted. -/
noncomputable def RetainedBodyTransitionWitness.callerInputs
    {before after : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput}
    (edge : RetainedBodyTransitionWitness before after)
    (programs : before.demand.InputPrograms Fits)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) :
    edge.InputProgram Fits × after.demand.InputPrograms Fits := by
  cases edge with
  | native expressionEq path selected admitted pending row execution continuation member readback normalized worlds depth =>
    let changed := castDemandPrograms expressionEq before.demand programs
    let current := normalized.inputPrograms changed
    exact ⟨normalized.nativeInputProgram changed pending henv hscoped formed, current.2⟩
  | legacy expressionEq path selected admitted selection execution sameAnnotation continuation member readback normalized worlds depth =>
    let changed := castDemandPrograms expressionEq before.demand programs
    let current := normalized.inputPrograms changed
    exact ⟨normalized.nativeInputProgram changed selection.pending henv hscoped formed, current.2⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
