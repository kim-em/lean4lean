import Lean4Lean.Theory.Typing.AnchoredSortableCert

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

noncomputable def SortableObs.raise {n N : Nat} {demand : Profile n} (h : n ≤ N)
    (observation : SortableObs env U registry Γ locals σ expression demand footprint) :
    SortableObs env U registry Γ locals σ expression (raiseProfile N h demand) footprint := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    exact observation
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; simpa only [raiseProfile_self] using observation
    · have hn : n ≤ N := by omega
      simpa only [raiseProfile_step hn] using SortableObs.pad (ih hn)

noncomputable def SortableObs.lower {n N : Nat} {demand : Profile n} (h : n ≤ N)
    (observation : SortableObs env U registry Γ locals σ expression
      (raiseProfile N h demand) footprint) :
    SortableObs env U registry Γ locals σ expression demand footprint := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    exact observation
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; simpa only [raiseProfile_self] using observation
    · have hn : n ≤ N := by omega
      rw [raiseProfile_step hn] at observation
      exact ih hn (SortableObs.unpad observation)

end Lean4Lean.AnchoredSource.Adapted
