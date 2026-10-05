import Lean4Lean.Theory.Typing.AnchoredFamilyArguments
import Lean4Lean.Theory.Typing.AnchoredConstructorWitness
import Lean4Lean.Theory.Typing.AnchoredSymmetry

/-! Binary finite observations of declared family applications. Both type
endpoints retain their actual deterministic exposures and per-position lower
argument admissions. Composition compares the shared type's actual traces;
it does not assume injectivity of raw definitional equality. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

def FamilyKey.rename (key : FamilyKey) (ρ : Lift) : FamilyKey :=
  ⟨key.rank, key.key.rename ρ, key.support.rename ρ⟩

theorem FamilyKey.rename_comp (key : FamilyKey) (ρ τ : Lift) :
    (key.rename ρ).rename τ = key.rename (ρ.comp τ) := by
  cases key
  simp only [rename, Key.rename_comp, ← Profile.rename_comp]

namespace FamilyArguments

theorem transport (henv : env.Ordered) (route : MixedInsertion env U Γ Δ ρ)
    (arguments : FamilyArguments env U registry Γ keys lefts rights) :
    FamilyArguments env U registry Δ (keys.map (·.rename ρ))
      (lefts.map (·.lift' ρ)) (rights.map (·.lift' ρ)) := by
  induction arguments with
  | nil => exact .nil
  | cons head tail ih =>
    obtain ⟨anchor, pair, typed, formed, code, first, last⟩ := head
    exact .cons ⟨route.eq henv anchor, route.eq henv pair,
      Profile.rename_hasType_iff.mpr typed,
      by simpa only [FamilyKey.rename, FamilyKey.request, Profile.rename_sort] using
        (Profile.rename_hasType_iff (ρ := ρ)).mpr formed,
      route.code henv code, route.term henv first, route.term henv last⟩ ih

private theorem admittedTrans (henv : env.Ordered) (hscoped : registry.Scoped)
    (first : RankedData.RequestAdmission env U (relations env U registry n) Γ key left middle)
    (second : RankedData.RequestAdmission env U (relations env U registry n) Γ key middle right) :
    RankedData.RequestAdmission env U (relations env U registry n) Γ key left right := by
  obtain ⟨anchor, pair, _, _, _, before, across⟩ := first
  obtain ⟨_, next, typed, formed, code, _, after⟩ := second
  exact ⟨anchor, pair.trans next, typed, formed, code,
    before, Related.trans henv hscoped across after⟩

theorem trans (henv : env.Ordered) (hscoped : registry.Scoped)
    (first : FamilyArguments env U registry Γ keys lefts middles)
    (second : FamilyArguments env U registry Γ keys middles rights) :
    FamilyArguments env U registry Γ keys lefts rights := by
  induction first generalizing rights with
  | nil => cases second; exact .nil
  | cons head tail ih =>
    cases second with
    | cons next rest => exact .cons (admittedTrans henv hscoped head next) (ih rest)

theorem left_diagonal (arguments : FamilyArguments env U registry Γ keys lefts rights) :
    FamilyArguments env U registry Γ keys lefts lefts := by
  induction arguments with
  | nil => exact .nil
  | cons head tail ih =>
    obtain ⟨anchor, pair, typed, formed, code, first, last⟩ := head
    exact .cons ⟨anchor, pair.hasType.1, typed, formed, code,
      first, Related.left_diagonal last⟩ ih

theorem symm (henv : env.Ordered) (hscoped : registry.Scoped)
    (arguments : FamilyArguments env U registry Γ keys lefts rights) :
    FamilyArguments env U registry Γ keys rights lefts := by
  induction arguments with
  | nil => exact .nil
  | cons head tail ih =>
    obtain ⟨anchor, pair, typed, formed, code, first, last⟩ := head
    exact .cons ⟨anchor.trans pair, pair.symm, typed, formed, code,
      Related.trans henv hscoped first last, Related.symm henv last⟩ ih

end FamilyArguments

/-- Heterogeneous finite grades let each argument retain the exact grade of
its actual header row. Every recursive admission is strictly below this code. -/
structure FamilyCodeDemand (n : Nat) where
  name : Name
  levels : List VLevel
  relevant : Bool
  arguments : List FamilyKey
  bounded : ∀ key ∈ arguments, key.rank < n

/-- A family code relates two types, including their actual parameters and
indices. Their assigned universe levels are kept separately. Proposition-valued
families are permitted here: these are observations of types, not their proofs. -/
structure FamilyCodeWitness (env : VEnv) (U : Nat) (registry : CanonicalDataHead.Registry)
    (Γ : List VExpr) (left right : VExpr) (demand : FamilyCodeDemand n) where
  leftLevel : VLevel
  rightLevel : VLevel
  leftRelevance : Relevant leftLevel demand.relevant
  rightRelevance : Relevant rightLevel demand.relevant
  context : List VExpr
  map : Lift
  path : TypeConversion env U context (left.lift' map) (right.lift' map)
  leftType : env.HasType U context (left.lift' map) (.sort leftLevel)
  rightType : env.HasType U context (right.lift' map) (.sort rightLevel)
  leftLevels : List VLevel
  rightLevels : List VLevel
  leftArguments : List VExpr
  rightArguments : List VExpr
  leftExposure : ConstructorExposure env U registry Γ left (.sort leftLevel) context map
    (mkApps (.const demand.name leftLevels) leftArguments)
  rightExposure : ConstructorExposure env U registry Γ right (.sort rightLevel) context map
    (mkApps (.const demand.name rightLevels) rightArguments)
  leftTerminal : CanonicalDataHead.step registry (mkApps (.const demand.name leftLevels) leftArguments) = none
  rightTerminal : CanonicalDataHead.step registry (mkApps (.const demand.name rightLevels) rightArguments) = none
  leftUniverses : List.Forall₂ (· ≈ ·) demand.levels leftLevels
  rightUniverses : List.Forall₂ (· ≈ ·) demand.levels rightLevels
  arguments : FamilyArguments env U registry.toRegistry context
    (demand.arguments.map (·.rename map)) leftArguments rightArguments

def FamilyCodeWitness.left_diagonal
    (witness : FamilyCodeWitness env U registry Γ left right demand) :
    FamilyCodeWitness env U registry Γ left left demand :=
  { witness with
    path := .refl
    rightLevel := witness.leftLevel
    rightType := witness.leftType
    rightRelevance := witness.leftRelevance
    rightLevels := witness.leftLevels
    rightArguments := witness.leftArguments
    rightExposure := witness.leftExposure
    rightTerminal := witness.leftTerminal
    rightUniverses := witness.leftUniverses
    arguments := witness.arguments.left_diagonal }

theorem FamilyCodeWitness.symm (henv : env.Ordered) (hscoped : registry.Scoped)
    (witness : FamilyCodeWitness env U registry Γ left right demand) :
    Nonempty (FamilyCodeWitness env U registry Γ right left demand) := by
  exact ⟨{
    path := witness.path.symm
    leftLevel := witness.rightLevel
    rightLevel := witness.leftLevel
    leftType := witness.rightType
    rightType := witness.leftType
    leftRelevance := witness.rightRelevance
    rightRelevance := witness.leftRelevance
    context := witness.context
    map := witness.map
    leftLevels := witness.rightLevels
    rightLevels := witness.leftLevels
    leftArguments := witness.rightArguments
    rightArguments := witness.leftArguments
    leftExposure := witness.rightExposure
    rightExposure := witness.leftExposure
    leftTerminal := witness.rightTerminal
    rightTerminal := witness.leftTerminal
    leftUniverses := witness.rightUniverses
    rightUniverses := witness.leftUniverses
    arguments := witness.arguments.symm henv hscoped.base }⟩

private theorem family_lift (name : Name) (levels : List VLevel)
    (arguments : List VExpr) (ρ : Lift) :
    (mkApps (.const name levels) arguments).lift' ρ =
      mkApps (.const name levels) (arguments.map (·.lift' ρ)) := by
  suffices ∀ head, (mkApps head arguments).lift' ρ =
      mkApps (head.lift' ρ) (arguments.map (·.lift' ρ)) from this _
  induction arguments with
  | nil => intro head; rfl
  | cons arg rest ih => intro head; exact ih (.app head arg)

private theorem family_spine (name : Name) (levels : List VLevel) (arguments : List VExpr) :
    (mkApps (.const name levels) arguments).getAppFnArgs = (.const name levels, arguments) := by
  have getSpine : ∀ (head : VExpr) arguments accumulated,
      getAppFnArgs.go (mkApps head arguments) accumulated =
        getAppFnArgs.go head (arguments ++ accumulated) := by
    intro head arguments
    induction arguments generalizing head with
    | nil => intro accumulated; rfl
    | cons arg rest ih => intro accumulated; exact ih (.app head arg) accumulated
  simp only [getAppFnArgs, getSpine, getAppFnArgs.go, List.append_nil]

/-- Distinct declaration tags cannot be produced from the same observed
type, regardless of the two demands' grades or assigned universe levels. -/
theorem FamilyCodeWitness.sameFamily
    {firstDemand : FamilyCodeDemand n} {secondDemand : FamilyCodeDemand m}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (first : FamilyCodeWitness env U registry Γ type firstRight firstDemand)
    (second : FamilyCodeWitness env U registry Γ type secondRight secondDemand) :
    firstDemand.name = secondDemand.name := by
  obtain ⟨_, i, j, _, _, _, heads⟩ := first.leftExposure.sameHead henv hscoped
    second.leftExposure first.leftTerminal second.leftTerminal
  rw [family_lift, family_lift] at heads
  have names : VExpr.const firstDemand.name first.leftLevels =
      VExpr.const secondDemand.name second.leftLevels := by
    simpa only [family_spine] using congrArg Prod.fst (congrArg VExpr.getAppFnArgs heads)
  exact (VExpr.const.inj names).1

/-- Finite family codes compose in the actual common proof world. Lower
argument admissions are paired only after deterministic middle-head agreement. -/
theorem FamilyCodeWitness.trans (henv : env.Ordered) (hscoped : registry.Scoped)
    (first : FamilyCodeWitness env U registry Γ left middle demand)
    (second : FamilyCodeWitness env U registry Γ middle right demand) :
    Nonempty (FamilyCodeWitness env U registry Γ left right demand) := by
  obtain ⟨Ω, i, j, firstLeg, secondLeg, maps, heads⟩ :=
    first.rightExposure.sameHead henv hscoped second.leftExposure
      first.rightTerminal second.leftTerminal
  have middleArguments : first.rightArguments.map (·.lift' i) =
      second.leftArguments.map (·.lift' j) := by
    rw [family_lift, family_lift] at heads
    simpa only [family_spine] using congrArg Prod.snd (congrArg VExpr.getAppFnArgs heads)
  obtain ⟨leftExposure⟩ := first.leftExposure.transport henv firstLeg
  obtain ⟨rightExposure⟩ := second.rightExposure.transport henv secondLeg
  have firstArguments := first.arguments.transport henv firstLeg
  have secondArguments := second.arguments.transport henv secondLeg
  simp only [List.map_map, Function.comp_def, FamilyKey.rename_comp, maps] at firstArguments secondArguments
  rw [middleArguments] at firstArguments
  refine ⟨{
    leftLevel := first.leftLevel
    rightLevel := second.rightLevel
    leftRelevance := first.leftRelevance
    rightRelevance := second.rightRelevance
    context := Ω
    map := second.map.comp j
    path := ?_
    leftType := ?_
    rightType := ?_
    leftLevels := first.leftLevels
    rightLevels := second.rightLevels
    leftArguments := first.leftArguments.map (·.lift' i)
    rightArguments := second.rightArguments.map (·.lift' j)
    leftExposure := ?_
    rightExposure := ?_
    leftTerminal := ?_
    rightTerminal := ?_
    leftUniverses := first.leftUniverses
    rightUniverses := second.rightUniverses
    arguments := firstArguments.trans henv hscoped.base secondArguments }⟩
  · have before := firstLeg.path henv first.path
    have after := secondLeg.path henv second.path
    simp only [← lift'_comp, maps] at before after
    exact before.trans after
  · simpa only [HasType, ← lift'_comp, maps, lift'] using firstLeg.eq henv first.leftType
  · simpa only [HasType, ← lift'_comp, lift'] using secondLeg.eq henv second.rightType
  · simpa only [family_lift, maps] using leftExposure
  · simpa only [family_lift] using rightExposure
  · rw [← family_lift, CanonicalDataHead.step_rename registry hscoped, first.leftTerminal]
    rfl
  · rw [← family_lift, CanonicalDataHead.step_rename registry hscoped, second.rightTerminal]
    rfl

end Lean4Lean.AnchoredSemantics
