import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProgramApplicationReadback
import Lean4Lean.Theory.Typing.AnchoredNativeForwardLevels

/-! Read back the physical terminal operands in the actual source display.
The original context bounds every used substitution entry, so unused tails
require no universe well-formedness assumption. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

theorem RetainedProgramTerminal.displayedLevels
    (terminal : RetainedProgramTerminal env U registry target strata P frontier goalFunction goalArgument goalOutput)
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U)) :
    EqUpToLevels U (terminal.function.subst terminal.state.right) terminal.readback.1 ∧
      EqUpToLevels U (terminal.argument.subst terminal.state.right) terminal.readback.2 := by
  have scope := terminal.state.node.sound.defeq.closedN terminal.state.controls.ordered
    (CtxWF.closed terminal.state.controls.ordered terminal.state.context.forget.defeq)
  rw [terminal.expressionEq] at scope
  have values := (terminal.state.substitutions.right henv formed).nativeValueLevels henv formed
  constructor
  · simpa only [subst_lift', RetainedProgramTerminal.readback] using
      terminal.functionLevels.substScoped scope.1 values
  · simpa only [subst_lift', RetainedProgramTerminal.readback] using
      terminal.argumentLevels.substScoped scope.2 values

/-- Combine interpreter readback preservation with the actual terminal's
typing. These are the displayed source operands used by its two F answers. -/
theorem RetainedProgramTerminal.callerLevels
    (terminal : RetainedProgramTerminal env U registry target strata P frontier goalFunction goalArgument goalOutput)
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (same : terminal.readback = (goalFunction.subst callerRight, goalArgument.subst callerRight)) :
    EqUpToLevels U (terminal.function.subst terminal.state.right) (goalFunction.subst callerRight) ∧
      EqUpToLevels U (terminal.argument.subst terminal.state.right) (goalArgument.subst callerRight) := by
  simpa only [same] using terminal.displayedLevels henv formed

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
