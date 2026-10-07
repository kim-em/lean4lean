import Lean4Lean.Theory.Typing.NativePrefixGeneratorLevels
import Lean4Lean.Theory.Typing.QuotPrefixReduction

/-! Fixed-context universe congruence of concrete native and primitive
quotient prefix reconstruction. -/

namespace Lean4Lean.VEnv
open VExpr InductiveSignature InductiveSignature.NativeRecursorData

theorem NativeDeltaRule.congr_levels {name : Name} {levels levels' : List VLevel}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : NativeDeltaRule env U registry Γ name levels args rhs)
    (hw' : ∀ level ∈ levels', level.WF U)
    (he : List.Forall₂ (· ≈ ·) levels levels')
    (ha : List.Forall₂ (EqUpToLevels U) args args') :
    ∃ rhs', NativeDeltaRule env U registry Γ name levels' args' rhs' ∧ EqUpToLevels U rhs rhs' := by
  cases H with
  | @intro data program hlookup hregistered hname hlarge hw hz hg replay =>
    obtain ⟨program', hg', hp⟩ := singletonProgram_levels hregistered hw hw' he ha hg
    have hs := EqUpToLevels.mkApps_args (EqUpToLevels.const (c := name) hw hw' he) ha
    have replay' := replay.congr_levels henv hΓ hp hs
    have hz' : data.sourceLevel levels' ≈ .zero :=
      (VLevel.inst_congr rfl he).symm.trans hz
    exact ⟨_, .intro hlookup hregistered hname hlarge hw' hz' hg' replay', hp.rhs replay.levels_wf⟩

theorem QuotDeltaRule.congr_levels {levels levels' : List VLevel}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : QuotDeltaRule env U Γ levels args rhs)
    (hw' : ∀ level ∈ levels', level.WF U)
    (he : List.Forall₂ (· ≈ ·) levels levels')
    (ha : List.Forall₂ (EqUpToLevels U) args args') :
    ∃ rhs', QuotDeltaRule env U Γ levels' args' rhs' ∧ EqUpToLevels U rhs rhs' := by
  cases H with
  | intro hregistered hw hz hg replay =>
    obtain ⟨program', hg', hp⟩ := QuotPrefixProgram.generate_levels hw hw' he ha hg
    have hs := EqUpToLevels.mkApps_args (EqUpToLevels.const (c := ``Quot.lift) hw hw' he) ha
    have replay' := replay.congr_levels henv hΓ hp hs
    have hz' : levels'[0]?.getD .zero ≈ .zero := by
      have hlen := (QuotPrefixProgram.generate_spec hg).1
      cases he with
      | nil => simp at hlen
      | cons h hs => exact h.symm.trans hz
    exact ⟨_, .intro hregistered hw' hz' hg' replay', hp.rhs replay.levels_wf⟩

end Lean4Lean.VEnv
