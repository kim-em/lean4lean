import Lean4Lean.Theory.Typing.AnchoredOriginalRecipeRankedPendingRows
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDependencyReplay

/-! Execute mixed-grade pending row input demands on the caller's actual
finite variable program. Its leaf predicate is unchanged; a canonical binder
table is never copied into the caller. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

noncomputable def RankedPendingNativeRow.replayInput
    {Fits : Nat → Need → Prop}
    {n m : Nat} {original : List (Key n × Profile n)} {key : Key m} {result : Profile m}
    (row : RankedPendingNativeRow env U registry target original relevant key result)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (program : VariableDependencyProgram env U registry target Fits index key.input) :
    VariableDependencyProgram env U registry target Fits index row.oldKey.input := by
  induction row with
  | fixed row =>
    exact program.map henv hscoped formed (Classical.choice (row.argumentAdapter henv hscoped formed))
  | change row view action ih =>
    let step : PendingNativeRow env U registry target [(_, _)] relevant relevant _ _ :=
      ⟨_, _, List.mem_singleton_self _, _, view, action⟩
    exact ih (program.map henv hscoped formed
      (Classical.choice (step.argumentAdapter henv hscoped formed)))
  | @pad m key result row ih =>
    apply ih
    apply VariableDependencyProgram.lowerRequested (Nat.le_succ m)
    simpa only [raiseProfile_step (Nat.le_refl m), raiseProfile_self, Key.pad] using program
  | @down m key result row ih =>
    apply ih
    have raised := program.raiseRequested henv hscoped formed (Nat.le_succ m)
    simpa only [raiseProfile_step (Nat.le_refl m), raiseProfile_self, Key.pad] using raised

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
