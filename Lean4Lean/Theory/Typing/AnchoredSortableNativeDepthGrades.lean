import Lean4Lean.Theory.Typing.AnchoredSortableNativeDepth
import Lean4Lean.Theory.Typing.AnchoredSortableAdapter
import Lean4Lean.Theory.Typing.AnchoredSortableGrades
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableTail

/-! Changing only the query grade preserves every unfolding-depth budget. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

@[simp] theorem SortableObs.nativeDepth_raise (current : Name → Bool) {n N : Nat} {demand : Profile n}
    (bound : n ≤ N) (observation : SortableObs env U registry target locals σ expression demand footprint) :
    (observation.raise bound).nativeDepth current = observation.nativeDepth current := by
  induction N with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases hn : n = N + 1
    · subst n
      simp only [SortableObs.raise, Nat.recAux, dite_true]
      exact SortableObs.nativeDepth_cast current (raiseProfile_self ..).symm _ observation
    · simp only [SortableObs.raise, Nat.recAux, dif_neg hn]
      refine (SortableObs.nativeDepth_cast current
        (raiseProfile_step (show n ≤ N by omega) demand).symm _ _).trans ?_
      change (SortableObs.pad (observation.raise (show n ≤ N by omega))).nativeDepth current = _
      simpa only [SortableObs.nativeDepth] using ih (by omega)

@[simp] theorem SortableCert.nativeDepth_raise (current : Name → Bool) {n N : Nat} {demand : Profile n}
    (bound : n ≤ N) (certificate : SortableCert env U registry target locals σ expression relevant demand footprint) :
    (certificate.raise bound).nativeDepth current = certificate.nativeDepth current := by
  induction N with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases hn : n = N + 1
    · subst n
      simp only [SortableCert.raise, Nat.recAux, dite_true]
      exact SortableCert.nativeDepth_cast current (raiseProfile_self ..).symm _ certificate
    · simp only [SortableCert.raise, Nat.recAux, dif_neg hn]
      refine (SortableCert.nativeDepth_cast current
        (raiseProfile_step (show n ≤ N by omega) demand).symm _ _).trans ?_
      change (SortableCert.pad (certificate.raise (show n ≤ N by omega))).nativeDepth current = _
      simpa only [SortableCert.nativeDepth] using ih (by omega)

@[simp] theorem SortableCert.nativeDepth_lower (current : Name → Bool) {n N : Nat} {demand : Profile N}
    (bound : n ≤ N) (certificate : SortableCert env U registry target locals σ expression relevant demand footprint) :
    (certificate.lower n bound).nativeDepth current = certificate.nativeDepth current := by
  induction N with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases hn : n = N + 1
    · subst n
      simp only [SortableCert.lower, Nat.recAux, dite_true]
      exact SortableCert.nativeDepth_cast current (lowerProfile_self ..).symm _ certificate
    · simp only [SortableCert.lower, Nat.recAux, dif_neg hn]
      refine (SortableCert.nativeDepth_cast current
        (lowerProfile_step (show n ≤ N by omega) demand).symm _ _).trans ?_
      change (certificate.down.lower n (show n ≤ N by omega)).nativeDepth current = _
      simpa only [SortableCert.nativeDepth] using ih (by omega) (.down certificate)

@[simp] theorem SortableCert.nativeDepth_lowerRaised (current : Name → Bool)
    {n N : Nat} {demand : Profile n} (bound : n ≤ N)
    (certificate : SortableCert env U registry target locals σ expression relevant
      (raiseProfile N bound demand) footprint) :
    (certificate.lowerRaised bound).nativeDepth current = certificate.nativeDepth current := by
  induction N with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases hn : n = N + 1
    · subst n
      simp only [SortableCert.lowerRaised, Nat.recAux, dite_true]
      exact SortableCert.nativeDepth_cast current (raiseProfile_self ..) _ certificate
    · simp only [SortableCert.lowerRaised, Nat.recAux, dif_neg hn]
      have small : n ≤ N := by omega
      let changed := (congrArg (fun p => SortableCert env U registry target locals σ
        expression relevant p footprint) (raiseProfile_step small demand)).mp certificate
      change (changed.unpad.lowerRaised small).nativeDepth current = _
      refine (ih small changed.unpad).trans ?_
      simp only [SortableCert.nativeDepth]
      exact SortableCert.nativeDepth_cast current (raiseProfile_step small demand) _ certificate

@[simp] theorem SortableObs.nativeDepth_lower (current : Name → Bool)
    {n N : Nat} {demand : Profile n} (bound : n ≤ N)
    (observation : SortableObs env U registry target locals σ expression
      (raiseProfile N bound demand) footprint) :
    (observation.lower bound).nativeDepth current = observation.nativeDepth current := by
  induction N with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases hn : n = N + 1
    · subst n
      simp only [SortableObs.lower, Nat.recAux, dite_true]
      exact SortableObs.nativeDepth_cast current (raiseProfile_self ..) _ observation
    · simp only [SortableObs.lower, Nat.recAux, dif_neg hn]
      have small : n ≤ N := by omega
      let changed := (congrArg (fun p => SortableObs env U registry target locals σ
        expression p footprint) (raiseProfile_step small demand)).mp observation
      change (changed.unpad.lower small).nativeDepth current = _
      refine (ih small changed.unpad).trans ?_
      simp only [SortableObs.nativeDepth]
      exact SortableObs.nativeDepth_cast current (raiseProfile_step small demand) _ observation

end Lean4Lean.AnchoredSource.Adapted
