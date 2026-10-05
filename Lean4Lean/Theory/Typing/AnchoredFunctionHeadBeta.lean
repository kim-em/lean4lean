import Lean4Lean.Theory.Typing.AnchoredHeadBeta

/-! The function-atom step of head-beta expansion. The only recursive
premise is expansion at the already constructed strict lower semantic rank.
The chosen Pi display, its codomain and all supports are retained literally. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

theorem FunctionBehavior.headBeta
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    (henv : env.Ordered)
    (lower : ∀ (Γ : List VExpr) (leftExpanded rightExpanded left right type : VExpr)
      (value support : Profile n),
      HeadBeta leftExpanded left → HeadBeta rightExpanded right →
      env.IsDefEq U Γ leftExpanded left type → env.IsDefEq U Γ rightExpanded right type →
      Related env U registry Γ left right type value support →
      Related env U registry Γ leftExpanded rightExpanded type value support)
    {Γ : List VExpr} {leftExpanded rightExpanded left right type : VExpr}
    {key : Key n} {output : Atom n} {profile : Profile (n + 1)}
    (hl : HeadBeta leftExpanded left) (hr : HeadBeta rightExpanded right)
    (cl : env.IsDefEq U Γ leftExpanded left type)
    (cr : env.IsDefEq U Γ rightExpanded right type)
    (H : FunctionBehavior env U registry (relations env U registry n)
      Γ left right type key output profile) :
    FunctionBehavior env U registry (relations env U registry n)
      Γ leftExpanded rightExpanded type key output profile := by
  obtain ⟨seed, A, B, domain, rows, result, hm, hrow, typed, display, behavior⟩ := H
  refine ⟨seed, A, B, domain, rows, result, hm, hrow, typed, display, ?_⟩
  intro Δ ρ future x y admitted
  have insertion := display.leftExposure.insertion henv
  have exposurePath := display.leftExposure.sound.weak' henv future.weakening
  have leftEq := (insertion.eq henv cl).weak' henv future.weakening
  have rightEq := (insertion.eq henv cr).weak' henv future.weakening
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
  have rightY := IsDefEq.defeqDF bodyEq.symm (IsDefEq.appDF rightPi pair.hasType.2)
  have leftHead := hl.lift (display.map.comp ρ)
  have rightHead := hr.lift (display.map.comp ρ)
  obtain ⟨leftBehavior, rightBehavior, crossBehavior⟩ := behavior Δ ρ future x y admitted
  exact ⟨lower Δ _ _ _ _ _ _ _ (leftHead.app x) (leftHead.app y)
      (by simpa only [lift'_comp] using leftX) (by simpa only [lift'_comp] using leftY) leftBehavior,
    lower Δ _ _ _ _ _ _ _ (rightHead.app x) (rightHead.app y)
      (by simpa only [lift'_comp] using rightX) (by simpa only [lift'_comp] using rightY) rightBehavior,
    lower Δ _ _ _ _ _ _ _ (leftHead.app x) (rightHead.app x)
      (by simpa only [lift'_comp] using leftX) (by simpa only [lift'_comp] using rightX) crossBehavior⟩

end Lean4Lean.AnchoredSemantics
