import Lean4Lean.Theory.Typing.AnchoredFamilyCodeRelation

/-! A constructor value freezes its exact finite family support. Both actual
constructor endpoints retain their declaration-derived result and a binary
family bridge to the assigned type. All raw evidence stays in actual private
display worlds; conversion never retracts a proof extension.
-/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles InductiveSignature
set_option backward.isDefEq.respectTransparency false

structure TypedConstructorDemand (n : Nat) where
  constructor : ConstructorDemand n
  family : FamilyCodeDemand (n + 1)
  relevant : family.relevant = true

/-- Intrinsic constructor typing selects precisely the family descriptor
frozen by the value demand. Extra support atoms cannot weaken that descriptor. -/
def TypedConstructorDemand.Covers (demand : TypedConstructorDemand n)
    (support : FamilyCodeDemand (n + 1)) : Prop := support = demand.family

theorem TypedConstructorDemand.support_unique
    {demand : TypedConstructorDemand n} {firstSupport secondSupport : FamilyCodeDemand (n + 1)}
    (first : demand.Covers firstSupport) (second : demand.Covers secondSupport) :
    firstSupport = secondSupport := first.trans second.symm

structure TypedConstructorWitness (env : VEnv) (U : Nat) (registry : CanonicalDataHead.Registry)
    (Γ : List VExpr) (left right type : VExpr) (demand : TypedConstructorDemand n) where
  value : ConstructorWitness env U registry Γ left right type demand.constructor
  leftHeader : ConstructorResultHeader env demand.constructor.name demand.family.name
    value.leftLevels value.leftArguments
  rightHeader : ConstructorResultHeader env demand.constructor.name demand.family.name
    value.rightLevels value.rightArguments
  leftBridge : FamilyCodeRelation env U registry value.context leftHeader.result
    (type.lift' value.map) (demand.family.rename value.map)
  rightBridge : FamilyCodeRelation env U registry value.context rightHeader.result
    (type.lift' value.map) (demand.family.rename value.map)

private theorem constructor_lift (name : Name) (levels : List VLevel)
    (arguments : List VExpr) (ρ : Lift) :
    (mkApps (.const name levels) arguments).lift' ρ =
      mkApps (.const name levels) (arguments.map (·.lift' ρ)) := by
  suffices ∀ head, (mkApps head arguments).lift' ρ =
      mkApps (head.lift' ρ) (arguments.map (·.lift' ρ)) from this _
  induction arguments with
  | nil => intro head; rfl
  | cons arg rest ih => intro head; exact ih (.app head arg)

namespace TypedConstructorWitness

/-- Move the entire typed constructor display along one actual world route.
Both result bridges and both declaration-derived argument tuples move with it. -/
theorem transportDisplay (henv : env.Ordered) (hscoped : registry.Scoped)
    (witness : TypedConstructorWitness env U registry Γ left right type demand)
    (route : MixedInsertion env U witness.value.context Δ ρ) :
    ∃ shifted : TypedConstructorWitness env U registry Γ left right type demand,
      shifted.value.context = Δ ∧ shifted.value.map = witness.value.map.comp ρ ∧
      shifted.value.leftLevels = witness.value.leftLevels ∧
      shifted.value.rightLevels = witness.value.rightLevels ∧
      shifted.value.leftArguments = witness.value.leftArguments.map (·.lift' ρ) ∧
      shifted.value.rightArguments = witness.value.rightArguments.map (·.lift' ρ) := by
  obtain ⟨leftDisplay⟩ := witness.value.leftExposure.transport henv route
  obtain ⟨rightDisplay⟩ := witness.value.rightExposure.transport henv route
  let value : ConstructorWitness env U registry Γ left right type demand.constructor := {
    context := Δ
    map := witness.value.map.comp ρ
    relevant := by
      obtain ⟨u, typed, relevant⟩ := witness.value.relevant
      exact ⟨u, by simpa only [HasType, ← lift'_comp, lift'] using route.eq henv typed, relevant⟩
    leftLevels := witness.value.leftLevels
    rightLevels := witness.value.rightLevels
    leftArguments := witness.value.leftArguments.map (·.lift' ρ)
    rightArguments := witness.value.rightArguments.map (·.lift' ρ)
    leftExposure := by simpa only [constructor_lift] using leftDisplay
    rightExposure := by simpa only [constructor_lift] using rightDisplay
    leftTerminal := by
      rw [← constructor_lift, CanonicalDataHead.step_rename registry hscoped, witness.value.leftTerminal]
      rfl
    rightTerminal := by
      rw [← constructor_lift, CanonicalDataHead.step_rename registry hscoped, witness.value.rightTerminal]
      rfl
    leftUniverses := witness.value.leftUniverses
    rightUniverses := witness.value.rightUniverses
    arguments := by
      simpa only [List.map_map, Function.comp_def, ← Key.rename_comp] using
        witness.value.arguments.transport henv route }
  let shifted : TypedConstructorWitness env U registry Γ left right type demand := {
    value := value
    leftHeader := witness.leftHeader.rename ρ
    rightHeader := witness.rightHeader.rename ρ
    leftBridge := by
      simpa only [value, witness.leftHeader.result_rename henv,
        ← lift'_comp, FamilyCodeDemand.rename_comp] using witness.leftBridge.mixed henv route
    rightBridge := by
      simpa only [value, witness.rightHeader.result_rename henv,
        ← lift'_comp, FamilyCodeDemand.rename_comp] using witness.rightBridge.mixed henv route }
  exact ⟨shifted, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Type conversion uses only the family descriptor frozen by the value.
The concrete code query supplies a further private world, and the constructor
display is moved there before any raw type is changed. -/
theorem convert (henv : env.Ordered) (hscoped : registry.Scoped)
    (witness : TypedConstructorWitness env U registry Γ left right oldType demand)
    (bridge : FamilyCodeRelation env U registry Γ oldType newType demand.family) :
    Nonempty (TypedConstructorWitness env U registry Γ left right newType demand) := by
  have current := bridge.mixed henv (witness.value.leftExposure.insertion henv)
  have formed := witness.value.leftExposure.terminal.targetWF henv
    (witness.value.leftExposure.post.targetWF henv)
  obtain ⟨code⟩ := current.atBase formed
  have route := code.leftExposure.insertion henv
  obtain ⟨shifted, contextEq, mapEq, _⟩ := witness.transportDisplay henv hscoped route
  have path : TypeConversion env U shifted.value.context
      (oldType.lift' shifted.value.map) (newType.lift' shifted.value.map) := by
    rw [contextEq, mapEq]
    simpa only [← lift'_comp] using code.path
  have next := bridge.mixed henv (shifted.value.leftExposure.insertion henv)
  let value : ConstructorWitness env U registry Γ left right newType demand.constructor := {
    shifted.value with
    relevant := by
      refine ⟨code.rightLevel, ?_, ?_⟩
      · rw [contextEq, mapEq]
        simpa only [← lift'_comp] using code.rightType
      · simpa only [FamilyCodeDemand.rename, demand.relevant, Relevant, if_true] using code.rightRelevance
    leftExposure := { shifted.value.leftExposure with sound := path.cast shifted.value.leftExposure.sound }
    rightExposure := { shifted.value.rightExposure with sound := path.cast shifted.value.rightExposure.sound } }
  exact ⟨{
    value := value
    leftHeader := shifted.leftHeader
    rightHeader := shifted.rightHeader
    leftBridge := shifted.leftBridge.trans henv hscoped next
    rightBridge := shifted.rightBridge.trans henv hscoped next }⟩

private theorem constructor_spine (name : Name) (levels : List VLevel) (arguments : List VExpr) :
    (mkApps (.const name levels) arguments).getAppFnArgs = (.const name levels, arguments) := by
  have getSpine : ∀ (head : VExpr) arguments accumulated,
      getAppFnArgs.go (mkApps head arguments) accumulated =
        getAppFnArgs.go head (arguments ++ accumulated) := by
    intro head arguments
    induction arguments generalizing head with
    | nil => intro accumulated; rfl
    | cons arg rest ih => intro accumulated; exact ih (.app head arg) accumulated
  simp only [getAppFnArgs, getSpine, getAppFnArgs.go, List.append_nil]

/-- Composition retains the first declared left result and the second
declared right result. Deterministic middle-head comparison aligns the actual
argument tuples before the lower admissions are composed. -/
theorem trans (henv : env.Ordered) (hscoped : registry.Scoped)
    (first : TypedConstructorWitness env U registry Γ left middle type demand)
    (second : TypedConstructorWitness env U registry Γ middle right type demand) :
    Nonempty (TypedConstructorWitness env U registry Γ left right type demand) := by
  obtain ⟨Ω, i, j, firstLeg, secondLeg, maps, heads⟩ :=
    first.value.rightExposure.sameHead henv hscoped second.value.leftExposure
      first.value.rightTerminal second.value.leftTerminal
  have middleArguments : first.value.rightArguments.map (·.lift' i) =
      second.value.leftArguments.map (·.lift' j) := by
    rw [constructor_lift, constructor_lift] at heads
    simpa only [constructor_spine] using congrArg Prod.snd (congrArg VExpr.getAppFnArgs heads)
  obtain ⟨before, context₁, map₁, _, _, _, arguments₁⟩ :=
    first.transportDisplay henv hscoped firstLeg
  obtain ⟨after, context₂, map₂, _, _, arguments₂, _⟩ :=
    second.transportDisplay henv hscoped secondLeg
  have contexts : before.value.context = after.value.context := context₁.trans context₂.symm
  have commonMap : before.value.map = after.value.map := map₁.trans (maps.trans map₂.symm)
  have commonArguments : before.value.rightArguments = after.value.leftArguments :=
    arguments₁.trans (middleArguments.trans arguments₂.symm)
  have later := after.value.arguments
  rw [← contexts, ← commonMap, ← commonArguments] at later
  let value : ConstructorWitness env U registry Γ left right type demand.constructor := {
    context := before.value.context
    map := before.value.map
    relevant := before.value.relevant
    leftLevels := before.value.leftLevels
    rightLevels := after.value.rightLevels
    leftArguments := before.value.leftArguments
    rightArguments := after.value.rightArguments
    leftExposure := before.value.leftExposure
    rightExposure := by simpa only [contexts, commonMap] using after.value.rightExposure
    leftTerminal := before.value.leftTerminal
    rightTerminal := after.value.rightTerminal
    leftUniverses := before.value.leftUniverses
    rightUniverses := after.value.rightUniverses
    arguments := before.value.arguments.trans henv hscoped.base later }
  exact ⟨{
    value := value
    leftHeader := before.leftHeader
    rightHeader := after.rightHeader
    leftBridge := before.leftBridge
    rightBridge := by simpa only [value, contexts, commonMap] using after.rightBridge }⟩

/-- Any two intrinsic supports for this constructor select the same family
descriptor, so the support-composition step retains every frozen index input. -/
theorem convertSupported (henv : env.Ordered) (hscoped : registry.Scoped)
    (witness : TypedConstructorWitness env U registry Γ left right oldType demand)
    (covered : demand.Covers support)
    (bridge : FamilyCodeRelation env U registry Γ oldType newType support) :
    Nonempty (TypedConstructorWitness env U registry Γ left right newType demand) := by
  cases covered
  exact witness.convert henv hscoped bridge

end TypedConstructorWitness
end Lean4Lean.AnchoredSemantics
