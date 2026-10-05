import Lean4Lean.Theory.Typing.AnchoredDataAnchors
import Batteries.Tactic.OpenPrivate

/-! A concrete raw family conversion joins two observations at the same
frozen family demand. Their argument representations meet at the retained
anchors; no raw type or constructor-parameter injectivity is required. -/
namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv AnchoredProfiles
open private family_lift from Lean4Lean.Theory.Typing.AnchoredDataLaws
set_option backward.isDefEq.respectTransparency false

theorem FamilyWitness.joinPath
    {env : VEnv} {U : Nat} {registry : CanonicalDataHead.Registry} {lower : Relations n}
    (henv : env.Ordered) (laws : LowerEquality env U registry lower)
    (path : TypeConversion env U Γ left right)
    (first : FamilyWitness env U registry lower Γ left firstRight demand)
    (second : FamilyWitness env U registry lower Γ secondLeft right demand) :
    Nonempty (FamilyWitness env U registry lower Γ left right demand) := by
  obtain ⟨Ω, i, j, firstLeg, secondLeg, maps⟩ := MixedInsertion.amalgam henv
    first.leftExposure.generated.baseWF
    (first.leftExposure.insertion henv) (second.leftExposure.insertion henv)
  obtain ⟨leftExposure⟩ := first.leftExposure.transport henv firstLeg
  obtain ⟨rightExposure⟩ := second.rightExposure.transport henv secondLeg
  have firstArguments := first.arguments.transport henv laws.toLowerTransport firstLeg
  have secondArguments := second.arguments.transport henv laws.toLowerTransport secondLeg
  simp only [List.map_map, Function.comp_def, DataRequest.rename_comp, maps] at firstArguments secondArguments
  refine ⟨{
    registryScoped := first.registryScoped, headInert := first.headInert
    leftLevel := first.leftLevel, rightLevel := second.rightLevel
    leftRelevance := first.leftRelevance, rightRelevance := second.rightRelevance
    context := Ω, map := second.map.comp j
    path := ?_, leftType := ?_, rightType := ?_
    leftLevels := first.leftLevels, rightLevels := second.rightLevels
    leftArguments := first.leftArguments.map (·.lift' i)
    rightArguments := second.rightArguments.map (·.lift' j)
    leftExposure := ?_, rightExposure := ?_
    leftTerminal := ?_, rightTerminal := ?_
    leftUniverses := first.leftUniverses, rightUniverses := second.rightUniverses
    arguments := firstArguments.joinAnchors laws first.registryScoped secondArguments }⟩
  · simpa only [maps] using ((first.leftExposure.insertion henv).comp firstLeg).path henv path
  · simpa only [HasType, family_lift, lift'] using firstLeg.eq henv first.leftType
  · simpa only [HasType, family_lift, lift'] using secondLeg.eq henv second.rightType
  · simpa only [family_lift, maps] using leftExposure
  · simpa only [family_lift] using rightExposure
  · rw [← family_lift, CanonicalDataHead.step_rename registry first.registryScoped, first.leftTerminal]; rfl
  · rw [← family_lift, CanonicalDataHead.step_rename registry first.registryScoped, second.rightTerminal]; rfl

theorem FamilyRelation.joinPath
    {env : VEnv} {U : Nat} {registry : CanonicalDataHead.Registry} {lower : Relations n}
    (henv : env.Ordered) (laws : LowerEquality env U registry lower)
    (path : TypeConversion env U Γ left right)
    (first : FamilyRelation env U registry lower Γ left firstRight demand)
    (second : FamilyRelation env U registry lower Γ secondLeft right demand) :
    FamilyRelation env U registry lower Γ left right demand := by
  intro Δ ρ future
  obtain ⟨before⟩ := first Δ ρ future
  obtain ⟨after⟩ := second Δ ρ future
  exact before.joinPath henv laws (path.weak' henv future.weakening) after

end Lean4Lean.AnchoredSemantics.RankedData
