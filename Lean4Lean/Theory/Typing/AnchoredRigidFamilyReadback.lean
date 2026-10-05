import Lean4Lean.Theory.Typing.AnchoredFamilyLiteralArguments
import Lean4Lean.Theory.Typing.AnchoredConstructorIntroduction
import Lean4Lean.Theory.Typing.AnchoredCodeExtraction

/-! Readback of both literal rigid-family spines. All private-world evidence
is retracted through the actual inhabited insertion retained by the witness. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
open private family_lift family_spine from Lean4Lean.Theory.Typing.AnchoredDataLaws
set_option backward.isDefEq.respectTransparency false

private theorem literalInertExposure
    (hscoped : registry.Scoped) (inert : CanonicalDataHead.HeadInert registry name)
    (exposure : Exposure env U registry Γ (mkApps (.const name levels) args) Δ ρ
      (mkApps (.const name shownLevels) shownArgs))
    (terminal : CanonicalDataHead.step registry (mkApps (.const name shownLevels) shownArgs) = none) :
    (mkApps (.const name levels) args).lift' ρ = mkApps (.const name shownLevels) shownArgs := by
  have stopped : CanonicalDataHead.step registry exposure.result = none := by
    rw [← exposure.result_eq, CanonicalDataHead.step_rename registry hscoped] at terminal
    exact Option.map_eq_none_iff.mp terminal
  have literalTrace : CanonicalDataHead.Trace registry
      (mkApps (.const name levels) args) [] (mkApps (.const name levels) args) := .refl
  obtain ⟨sameAdded, sameResult⟩ := literalTrace.terminal_unique exposure.trace
    (inert.step levels args) stopped
  have sameMap := exposure.map_eq
  rw [← sameAdded] at sameMap
  simp only [List.length_nil, Lift.skipN, Lift.refl_comp] at sameMap
  simpa only [← sameResult, sameMap] using exposure.result_eq

private theorem universePair {base left right : List VLevel}
    (first : List.Forall₂ (· ≈ ·) base left)
    (second : List.Forall₂ (· ≈ ·) base right) : List.Forall₂ (· ≈ ·) left right := by
  induction first generalizing right with
  | nil => cases second; exact .nil
  | cons equal rest ih =>
    cases second with
    | cons other others => exact .cons (equal.symm.trans other) (ih others)

namespace RankedData

theorem Arguments.rawPairs
    (arguments : Arguments env U lower Γ requests left right) :
    List.Forall₂ (env.IsDefEqU U Γ) left right := by
  induction arguments with
  | nil => exact .nil
  | cons admitted rest ih => exact .cons ⟨_, admitted.2.1⟩ ih

theorem FamilyWitness.literalPairReadback
    (ordered : env.Ordered) (hscoped : registry.Scoped)
    {family : FamilyData (Profile n)}
    {leftLevels rightLevels : List VLevel} {leftArgs rightArgs : List VExpr}
    (witness : FamilyWitness env U registry (relations env U registry n) Γ
      (mkApps (.const family.name leftLevels) leftArgs)
      (mkApps (.const family.name rightLevels) rightArgs) family) :
    List.Forall₂ (· ≈ ·) leftLevels rightLevels ∧
      List.Forall₂ (env.IsDefEqU U Γ) leftArgs rightArgs := by
  have left := literalInertExposure hscoped witness.headInert witness.leftExposure witness.leftTerminal
  have right := literalInertExposure hscoped witness.headInert witness.rightExposure witness.rightTerminal
  rw [family_lift] at left right
  have leftSpine := congrArg VExpr.getAppFnArgs left
  have rightSpine := congrArg VExpr.getAppFnArgs right
  simp only [family_spine] at leftSpine rightSpine
  have leftLevelEq := (VExpr.const.inj (congrArg Prod.fst leftSpine)).2
  have rightLevelEq := (VExpr.const.inj (congrArg Prod.fst rightSpine)).2
  have leftArgEq : leftArgs.map (·.lift' witness.map) = witness.leftArguments := congrArg Prod.snd leftSpine
  have rightArgEq : rightArgs.map (·.lift' witness.map) = witness.rightArguments := congrArg Prod.snd rightSpine
  refine ⟨?_, ?_⟩
  · have pair := universePair witness.leftUniverses witness.rightUniverses
    simpa only [← leftLevelEq, ← rightLevelEq] using pair
  · have arguments := witness.arguments
    rw [← leftArgEq, ← rightArgEq] at arguments
    exact (arguments.mixedBack ordered hscoped (witness.leftExposure.insertion ordered)).rawPairs

theorem FamilyRelation.literalPairReadback
    (ordered : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx Γ (env.IsType U))
    {family : FamilyData (Profile n)}
    {leftLevels rightLevels : List VLevel} {leftArgs rightArgs : List VExpr}
    (related : FamilyRelation env U registry (relations env U registry n) Γ
      (mkApps (.const family.name leftLevels) leftArgs)
      (mkApps (.const family.name rightLevels) rightArgs) family) :
    List.Forall₂ (· ≈ ·) leftLevels rightLevels ∧
      List.Forall₂ (env.IsDefEqU U Γ) leftArgs rightArgs := by
  obtain ⟨witness⟩ := related.atBase formed
  exact witness.literalPairReadback ordered hscoped

end RankedData

theorem TypeRelated.rigidFamilyReadback
    {profile : Profile (n + 1)}
    (ordered : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx Γ (env.IsType U))
    {family : FamilyData (Profile n)}
    {leftLevels rightLevels : List VLevel} {leftArgs rightArgs : List VExpr}
    (related : TypeRelated env U registry Γ
      (mkApps (.const family.name leftLevels) leftArgs)
      (mkApps (.const family.name rightLevels) rightArgs) profile)
    (member : (AtomData.family family : Atom (n + 1)) ∈ profile.atoms) :
    List.Forall₂ (· ≈ ·) leftLevels rightLevels ∧
      List.Forall₂ (env.IsDefEqU U Γ) leftArgs rightArgs :=
  (related.familyRelation member).literalPairReadback ordered hscoped formed

theorem Related.rigidFamilyReadback
    {profile support : Profile (n + 1)}
    (ordered : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx Γ (env.IsType U))
    {family : FamilyData (Profile n)}
    {leftLevels rightLevels : List VLevel} {leftArgs rightArgs : List VExpr}
    (related : Related env U registry Γ
      (mkApps (.const family.name leftLevels) leftArgs)
      (mkApps (.const family.name rightLevels) rightArgs) assigned profile support)
    (sortable : profile.HasType (.sort relevant))
    (member : (AtomData.family family : Atom (n + 1)) ∈ profile.atoms) :
    List.Forall₂ (· ≈ ·) leftLevels rightLevels ∧
      List.Forall₂ (env.IsDefEqU U Γ) leftArgs rightArgs :=
  (related.code_of_sortable ordered hscoped formed sortable).rigidFamilyReadback
    ordered hscoped formed member

end Lean4Lean.AnchoredSemantics
