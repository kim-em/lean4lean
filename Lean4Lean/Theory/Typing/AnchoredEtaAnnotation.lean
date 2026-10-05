import Lean4Lean.Theory.Typing.AnchoredMixedTransport
import Lean4Lean.Theory.Typing.AnchoredEtaExpansion

/-! Eta annotations may differ from the assigned Pi display. The original
raw eta equality supplies typing; semantic outputs use actual head beta. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

theorem FunctionBehavior.etaExpandAt
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    (henv : env.Ordered)
    {Γ : List VExpr} {f g annotation type : VExpr}
    {key : Key n} {output : Atom n} {profile : Profile (n + 1)}
    (raw : env.IsDefEq U Γ (.lam annotation (.app f.lift (.bvar 0))) f type)
    (rightTyped : env.HasType U Γ g type)
    (H : FunctionBehavior env U registry (relations env U registry n)
      Γ f g type key output profile) :
    FunctionBehavior env U registry (relations env U registry n)
      Γ (.lam annotation (.app f.lift (.bvar 0))) g type key output profile := by
  obtain ⟨seed, C, D, domain, rows, result, hm, hrow, typed, display, behavior⟩ := H
  refine ⟨seed, C, D, domain, rows, result, hm, hrow, typed, display, ?_⟩
  intro Δ ρ future x y admitted
  have insertion := display.leftExposure.insertion henv
  have exposurePath := display.leftExposure.sound.weak' henv future.weakening
  have leftEq := (insertion.eq henv raw).weak' henv future.weakening
  have rightEq := (insertion.eq henv rightTyped).weak' henv future.weakening
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
      (.app ((VExpr.lam annotation (.app f.lift (.bvar 0))).lift' (display.map.comp ρ)) arg)
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

theorem Related.etaExpandAt
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {Γ : List VExpr} {f g annotation type : VExpr} {key : Key n} {output : Atom n}
    {support : Profile (n + 1)}
    (raw : env.IsDefEq U Γ (.lam annotation (.app f.lift (.bvar 0))) f type)
    (rightTyped : env.HasType U Γ g type)
    (H : Related env U registry Γ f g type (.fn key output) support) :
    Related env U registry Γ (.lam annotation (.app f.lift (.bvar 0))) g
      type (.fn key output) support := by
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
    have rightTyped' := (rightTyped.weak' henv future.weakening).weak' henv insertion.weakening
    simp only [eta_lift'] at raw' ⊢
    simpa only [TermAtom, lift'] using FunctionBehavior.etaExpandAt henv raw' rightTyped' original

end Lean4Lean.AnchoredSemantics
