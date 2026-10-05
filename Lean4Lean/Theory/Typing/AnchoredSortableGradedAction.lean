import Lean4Lean.Theory.Typing.AnchoredSortableGradedResult
import Lean4Lean.Theory.Typing.AnchoredAtomActionGeneralAdapter
import Lean4Lean.Theory.Typing.AnchoredAtomActionGrades
import Lean4Lean.Theory.Typing.AnchoredAtomActionLive

/-! Apply an action to an actual finite returned observation. The actual raw query is
retained; the finite action composes with its generalized adapter. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem SortableGradedResult.action
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (closed : available.AtomClosed)
    {a b : Atom n} (action : AtomAction env U registry Γ a b)
    (result : SortableGradedResult env U registry Γ locals σ available expression (.singleton a)) :
    Nonempty (SortableGradedResult env U registry Γ locals σ available expression (.singleton b)) := by
  exact ⟨{
    rank := result.rank
    bound := result.bound
    raw := result.raw
    footprint := result.footprint
    observation := result.observation
    adapter := by
      have step := (action.raise result.bound).toGeneralAdapter henv hscoped hΓ
      have first := result.adapter
      rw [raiseProfile_singleton] at first ⊢
      exact GeneralProfileAdapter.comp first
        (.cons (List.mem_singleton_self _) step (.nil _))
    resources := result.resources
    live := result.live }⟩

end Lean4Lean.AnchoredSource.Adapted
