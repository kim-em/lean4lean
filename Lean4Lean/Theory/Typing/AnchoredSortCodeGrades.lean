import Lean4Lean.Theory.Typing.AnchoredSortable

/-! A retained, inhabited universe-code query can move to the next rank
without wrapping its sort atom in padding. Its source expression is arbitrary. -/
namespace Lean4Lean.AnchoredProfiles

theorem Profile.HasType.sortPad
    (formed : (Profile.sort (n := n) flag).HasType (.sort relevant)) :
    (Profile.sort (n := n + 1) flag).HasType (.sort relevant) := by
  have equal : relevant = true := by
    cases n with
    | zero =>
      obtain ⟨cover, member, typed⟩ := formed flag (List.mem_singleton_self _)
      cases List.mem_singleton.mp member
      exact typed
    | succ n =>
      obtain ⟨cover, member, typed⟩ := formed.2.2 _ (List.mem_singleton_self _)
      cases List.mem_singleton.mp member
      exact typed
  subst relevant
  exact Profile.HasType.sort flag

end Lean4Lean.AnchoredProfiles

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles

theorem TypeRelated.sortPad
    (code : TypeRelated env U registry Γ left right (Profile.sort (n := n) flag)) :
    TypeRelated env U registry Γ left right (Profile.sort (n := n + 1) flag) := by
  intro Δ ρ future atom member
  cases List.mem_singleton.mp member
  cases n <;> exact code Δ ρ future _ (List.mem_singleton_self _)

end Lean4Lean.AnchoredSemantics
