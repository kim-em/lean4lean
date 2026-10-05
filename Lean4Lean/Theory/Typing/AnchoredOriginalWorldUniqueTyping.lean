import Lean4Lean.Theory.Typing.AnchoredOriginalWorldAssignedConversion
import Lean4Lean.Theory.Typing.AnchoredInversionReadback

/-! Exact public type uniqueness follows directly from assigned comparison.
This bridge does not use field inversion or the old uniqueness induction. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- The actual replay interface supplies both the assigned-type path and the
sort coherence needed to read it at one universe. -/
theorem rawUniqueTypingOfWorldBanks
    (strata : EquationStratification env) (henv : env.WF)
    (formed : OnCtx Γ (env.IsType U))
    (replay : ∀ budget, WorldBoundedReplayAt env U registry strata (fun _ => True) budget)
    (first : env.IsDefEq U Γ e₁ e₂ A)
    (second : env.IsDefEq U Γ e₂ e₃ B) :
    ∃ u, env.IsDefEq U Γ A B (.sort u) := by
  have path := assignedConversionOfWorldBanks strata henv formed replay
    first.hasType.2 second.hasType.1
  obtain ⟨u, typed⟩ := first.isType henv formed
  exact ⟨u, path.defeqOfSortUniqueness henv formed
    (fun left right => sortTypingLevelsOfWorldBanks strata henv formed replay left right) typed⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
