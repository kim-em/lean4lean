import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceObservation
import Lean4Lean.Theory.Typing.AnchoredFunctionGradeView

/-! Literal finite grade changes preserve actual source leaves. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

noncomputable def Obs.raise {n N : Nat} {demand : Profile n} (h : n ≤ N)
    (observation : Obs env U registry Γ locals σ expression demand footprint) :
    Obs env U registry Γ locals σ expression (raiseProfile N h demand) footprint := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    exact observation
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; simpa only [raiseProfile_self] using observation
    · have hn : n ≤ N := by omega
      simpa only [raiseProfile_step hn] using Obs.pad (ih hn)

noncomputable def Obs.lower {n N : Nat} {demand : Profile n} (h : n ≤ N)
    (observation : Obs env U registry Γ locals σ expression
      (raiseProfile N h demand) footprint) :
    Obs env U registry Γ locals σ expression demand footprint := by
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
      exact ih hn (Obs.unpad observation)

noncomputable def CodeCert.raise {n N : Nat} {demand : Profile n} (h : n ≤ N)
    (certificate : CodeCert env U registry Γ locals σ expression demand footprint) :
    CodeCert env U registry Γ locals σ expression (raiseProfile N h demand) footprint := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    exact certificate
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; simpa only [raiseProfile_self] using certificate
    · have hn : n ≤ N := by omega
      simpa only [raiseProfile_step hn] using CodeCert.pad (ih hn)

noncomputable def CodeCert.lowerRaised {n N : Nat} {demand : Profile n} (h : n ≤ N)
    (certificate : CodeCert env U registry Γ locals σ expression
      (raiseProfile N h demand) footprint) :
    CodeCert env U registry Γ locals σ expression demand footprint := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    exact certificate
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; simpa only [raiseProfile_self] using certificate
    · have hn : n ≤ N := by omega
      rw [raiseProfile_step hn] at certificate
      exact ih hn (CodeCert.unpad certificate)

end Lean4Lean.AnchoredSource.Adapted
