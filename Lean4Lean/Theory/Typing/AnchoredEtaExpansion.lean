import Lean4Lean.Theory.Typing.AnchoredMixedTransport
import Lean4Lean.Theory.Typing.AnchoredBeta

/-! Eta expansion of an actual function observation. The function's chosen
display and supports are preserved; every applied eta redex is handled by the
closed head-beta theorem at the output rank. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

theorem eta_lift' (A f : VExpr) (ρ : Lift) :
    (VExpr.lam A (.app f.lift (.bvar 0))).lift' ρ =
      .lam (A.lift' ρ) (.app (f.lift' ρ).lift (.bvar 0)) := by
  simp only [lift', Lift.liftVar, lift_eq_lift', ← lift'_comp,
    Lift.comp, Lift.refl_comp]

theorem HeadBeta.etaApp (A f x : VExpr) :
    HeadBeta (.app (.lam A (.app f.lift (.bvar 0))) x) (.app f x) := by
  simpa only [mkApps, List.foldl_cons, List.foldl_nil, inst, inst_lift,
    instVar_zero] using
    (HeadBeta.contract (A := A) (body := .app f.lift (.bvar 0))
      (argument := x) (trailing := []))

theorem FunctionBehavior.etaExpand
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    (henv : env.Ordered)
    {Γ : List VExpr} {f g A B : VExpr}
    {key : Key n} {output : Atom n} {profile : Profile (n + 1)}
    (raw : env.IsDefEq U Γ f g (.forallE A B))
    (H : FunctionBehavior env U registry (relations env U registry n)
      Γ f g (.forallE A B) key output profile) :
    FunctionBehavior env U registry (relations env U registry n)
      Γ (.lam A (.app f.lift (.bvar 0))) g (.forallE A B) key output profile := by
  obtain ⟨seed, C, D, domain, rows, result, hm, hrow, typed, display, behavior⟩ := H
  refine ⟨seed, C, D, domain, rows, result, hm, hrow, typed, display, ?_⟩
  intro Δ ρ future x y admitted
  have insertion := display.leftExposure.insertion henv
  have exposurePath := display.leftExposure.sound.weak' henv future.weakening
  have leftEq := (insertion.eq henv (IsDefEq.eta raw.hasType.1)).weak' henv future.weakening
  have rightEq := (insertion.eq henv raw.hasType.2).weak' henv future.weakening
  have leftPi := exposurePath.cast leftEq
  have rightPi := exposurePath.cast rightEq
  obtain ⟨_, _, _, _, rowPath, _⟩ := display.rowDomains key result hrow
  have argumentPath := rowPath.weak' henv future.weakening
  have argumentEq : env.IsDefEq U Δ x y ((key.domain.lift' display.map).lift' ρ) := by
    simpa only [Key.rename, lift'_comp] using admitted.2.1
  have pair := argumentPath.cast argumentEq
  obtain ⟨level, bodyType⟩ := display.leftBodyType
  have bodyType' := bodyType.weak' henv future.weakening.cons
  have bodyEq := bodyType'.instDF henv (future.targetWF henv) pair
  have leftX := IsDefEq.appDF leftPi pair.hasType.1
  have leftY := IsDefEq.defeqDF bodyEq.symm (IsDefEq.appDF leftPi pair.hasType.2)
  have rightX := IsDefEq.appDF rightPi pair.hasType.1
  have leftHead (arg : VExpr) : HeadBeta
      (.app ((VExpr.lam A (.app f.lift (.bvar 0))).lift' (display.map.comp ρ)) arg)
      (.app (f.lift' (display.map.comp ρ)) arg) := by
    rw [eta_lift']
    exact HeadBeta.etaApp _ _ _
  obtain ⟨leftBehavior, rightBehavior, crossBehavior⟩ := behavior Δ ρ future x y admitted
  exact ⟨Related.headBeta henv (leftHead x) (leftHead y)
      (by simpa only [lift'_comp] using leftX)
      (by simpa only [lift'_comp] using leftY) leftBehavior,
    rightBehavior,
    Related.headBeta henv (leftHead x) .refl
      (by simpa only [lift'_comp] using leftX)
      (by simpa only [lift'_comp] using rightX) crossBehavior⟩

theorem Related.etaExpand
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {Γ : List VExpr} {f g A B : VExpr} {key : Key n} {output : Atom n}
    {support : Profile (n + 1)}
    (raw : env.IsDefEq U Γ f g (.forallE A B))
    (H : Related env U registry Γ f g (.forallE A B) (.fn key output) support) :
    Related env U registry Γ (.lam A (.app f.lift (.bvar 0))) g
      (.forallE A B) (.fn key output) support := by
  intro requested member Δ ρ future
  cases List.mem_singleton.mp member
  rcases H (.fn key output) (List.mem_singleton_self _) Δ ρ future with
    empty | ⟨Ω, τ, insertion, typed, code, values⟩
  · cases empty
  · refine .inr ⟨Ω, τ, insertion, typed, code, ?_⟩
    intro atom member
    have original := values atom member
    simp only [Profile.rename_singleton, Atom.rename_fn] at member
    cases List.mem_singleton.mp member
    have raw' := (raw.weak' henv future.weakening).weak' henv insertion.weakening
    simp only [eta_lift']
    simpa only [TermAtom, lift'] using FunctionBehavior.etaExpand henv raw' original

end Lean4Lean.AnchoredSemantics
