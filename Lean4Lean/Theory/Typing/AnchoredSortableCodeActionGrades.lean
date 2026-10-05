import Lean4Lean.Theory.Typing.AnchoredSortableCodeActionAtoms
import Lean4Lean.Theory.Typing.AnchoredFunctionGradeView

/-! Rank-polymorphic code actions normalize to one common grade through
exact padding and unpadding. No down projection loses an input observation. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

noncomputable def SortableCodeAction.raiseTo {n N : Nat} {profile : Profile n}
    (bound : n ≤ N) :
    SortableCodeAction env U registry target relevant profile relevant (raiseProfile N bound profile) := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    exact .id
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n; simpa only [raiseProfile_self] using (SortableCodeAction.id (profile := profile))
    · have previous : n ≤ N := by omega
      simpa only [raiseProfile_step previous] using SortableCodeAction.comp (ih previous) .pad

noncomputable def SortableCodeAction.lowerRaised {n N : Nat} {profile : Profile n}
    (bound : n ≤ N) :
    SortableCodeAction env U registry target relevant (raiseProfile N bound profile) relevant profile := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    exact .id
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n; simpa only [raiseProfile_self] using (SortableCodeAction.id (profile := profile))
    · have previous : n ≤ N := by omega
      simpa only [raiseProfile_step previous] using SortableCodeAction.comp .unpad (ih previous)

noncomputable def SortableCodeAction.atGrade {n m N : Nat}
    {profile : Profile n} {nextProfile : Profile m}
    (action : SortableCodeAction env U registry target relevant profile next nextProfile)
    (sourceBound : n ≤ N) (outputBound : m ≤ N) :
    SortableCodeAction env U registry target relevant (raiseProfile N sourceBound profile)
      next (raiseProfile N outputBound nextProfile) :=
  .comp (.lowerRaised sourceBound) (.comp action (.raiseTo outputBound))

/-- Singleton normalization uses actual padded source/output atoms; it does
not posit an adapter from padded sorts to promoted bare sorts. -/
noncomputable def SortableCodeAction.atomAtGrade {n m N : Nat}
    {source : Atom n} {output : Atom m}
    (action : SortableCodeAction env U registry target relevant (.singleton source)
      next (.singleton output))
    (sourceBound : n ≤ N) (outputBound : m ≤ N) :
    SortableCodeAction env U registry target relevant (.singleton (raiseAtom N sourceBound source))
      next (.singleton (raiseAtom N outputBound output)) := by
  simpa only [raiseProfile_singleton] using action.atGrade sourceBound outputBound

end Lean4Lean.AnchoredSource.Adapted
