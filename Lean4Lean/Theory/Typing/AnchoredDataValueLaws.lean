import Lean4Lean.Theory.Typing.AnchoredDataAnchors
import Lean4Lean.Theory.Typing.AnchoredDataDiagonal
import Lean4Lean.Theory.Typing.AnchoredProjectionOriginTransport

/-! Constructor and projection clauses compose and convert using their exact
frozen family descriptor and preceding-rank argument laws. -/
namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

variable {env : VEnv} {U : Nat} {registry : CanonicalDataHead.Registry} {lower : Relations n}

private theorem head_lift (name : Name) (levels : List VLevel) (arguments : List VExpr) (ρ : Lift) :
    (mkApps (.const name levels) arguments).lift' ρ =
      mkApps (.const name levels) (arguments.map (·.lift' ρ)) := by
  suffices ∀ head, (mkApps head arguments).lift' ρ =
      mkApps (head.lift' ρ) (arguments.map (·.lift' ρ)) from this _
  induction arguments with
  | nil => intro head; rfl
  | cons arg rest ih => intro head; exact ih (.app head arg)

private theorem head_spine (name : Name) (levels : List VLevel) (arguments : List VExpr) :
    (mkApps (.const name levels) arguments).getAppFnArgs = (.const name levels, arguments) := by
  have getSpine : ∀ (head : VExpr) arguments accumulated,
      getAppFnArgs.go (mkApps head arguments) accumulated =
        getAppFnArgs.go head (arguments ++ accumulated) := by
    intro head arguments
    induction arguments generalizing head with
    | nil => intro accumulated; rfl
    | cons arg rest ih => intro accumulated; exact ih (.app head arg) accumulated
  simp only [getAppFnArgs, getSpine, getAppFnArgs.go, List.append_nil]

theorem ConstructorWitness.registryScoped (henv : env.Ordered)
    (witness : ConstructorWitness env U registry lower Γ left right type demand) : registry.Scoped := by
  obtain ⟨code⟩ := witness.leftBridge.atBase
    (witness.leftExposure.targetWF henv)
  exact code.registryScoped

theorem ConstructorWitness.transportDisplay (henv : env.Ordered)
    (laws : LowerTransport env U lower)
    (witness : ConstructorWitness env U registry lower Γ left right type demand)
    (route : MixedInsertion env U witness.context Δ ρ) :
    ∃ shifted : ConstructorWitness env U registry lower Γ left right type demand,
      shifted.context = Δ ∧ shifted.map = witness.map.comp ρ ∧
      shifted.leftArguments = witness.leftArguments.map (·.lift' ρ) ∧
      shifted.rightArguments = witness.rightArguments.map (·.lift' ρ) := by
  obtain ⟨leftExposure⟩ := witness.leftExposure.transport henv route
  obtain ⟨rightExposure⟩ := witness.rightExposure.transport henv route
  have scope := witness.registryScoped henv
  refine ⟨{
    headInert := witness.headInert
    context := Δ, map := witness.map.comp ρ
    leftLevels := witness.leftLevels, rightLevels := witness.rightLevels
    leftArguments := witness.leftArguments.map (·.lift' ρ)
    rightArguments := witness.rightArguments.map (·.lift' ρ)
    leftExposure := by simpa only [head_lift] using leftExposure
    rightExposure := by simpa only [head_lift] using rightExposure
    leftTerminal := ?_, rightTerminal := ?_
    leftUniverses := witness.leftUniverses, rightUniverses := witness.rightUniverses
    arguments := ?_
    leftHeader := witness.leftHeader.rename ρ, rightHeader := witness.rightHeader.rename ρ
    leftBridge := ?_, rightBridge := ?_ }, rfl, rfl, rfl, rfl⟩
  · rw [← head_lift, CanonicalDataHead.step_rename registry scope, witness.leftTerminal]; rfl
  · rw [← head_lift, CanonicalDataHead.step_rename registry scope, witness.rightTerminal]; rfl
  · simpa only [List.map_map, Function.comp_def, DataRequest.rename_comp] using
      witness.arguments.transport henv laws route
  · simpa only [witness.leftHeader.result_rename henv, ← lift'_comp, FamilyData.rename_comp] using
      witness.leftBridge.mixed henv route
  · simpa only [witness.rightHeader.result_rename henv, ← lift'_comp, FamilyData.rename_comp] using
      witness.rightBridge.mixed henv route

def ConstructorWitness.symm (henv : env.Ordered) (laws : LowerEquality env U registry lower)
    (witness : ConstructorWitness env U registry lower Γ left right type demand) :
    ConstructorWitness env U registry lower Γ right left type demand :=
  { witness with
    leftLevels := witness.rightLevels, rightLevels := witness.leftLevels
    leftArguments := witness.rightArguments, rightArguments := witness.leftArguments
    leftExposure := witness.rightExposure, rightExposure := witness.leftExposure
    leftTerminal := witness.rightTerminal, rightTerminal := witness.leftTerminal
    leftUniverses := witness.rightUniverses, rightUniverses := witness.leftUniverses
    arguments := witness.arguments.symm laws (witness.registryScoped henv)
    leftHeader := witness.rightHeader, rightHeader := witness.leftHeader
    leftBridge := witness.rightBridge, rightBridge := witness.leftBridge }

theorem ConstructorWitness.trans (henv : env.Ordered) (laws : LowerEquality env U registry lower)
    (first : ConstructorWitness env U registry lower Γ left middle type demand)
    (second : ConstructorWitness env U registry lower Γ middle right type demand) :
    Nonempty (ConstructorWitness env U registry lower Γ left right type demand) := by
  obtain ⟨Ω, i, j, firstLeg, secondLeg, maps⟩ := MixedInsertion.amalgam henv
    first.leftExposure.baseWF
    (first.leftExposure.insertion henv) (second.leftExposure.insertion henv)
  obtain ⟨before, context₁, map₁, _, _⟩ := first.transportDisplay henv laws.toLowerTransport firstLeg
  obtain ⟨after, context₂, map₂, _, _⟩ := second.transportDisplay henv laws.toLowerTransport secondLeg
  have contexts : before.context = after.context := context₁.trans context₂.symm
  have commonMap : before.map = after.map := map₁.trans (maps.trans map₂.symm)
  have later := after.arguments
  rw [← contexts, ← commonMap] at later
  exact ⟨{ before with
    rightLevels := after.rightLevels
    rightArguments := after.rightArguments
    rightExposure := by simpa only [contexts, commonMap] using after.rightExposure
    rightTerminal := after.rightTerminal
    rightUniverses := after.rightUniverses
    arguments := before.arguments.joinAnchors laws (before.registryScoped henv) later
    rightHeader := after.rightHeader
    rightBridge := by simpa only [contexts, commonMap] using after.rightBridge }⟩

theorem ConstructorWitness.convert (henv : env.Ordered) (laws : LowerEquality env U registry lower)
    (witness : ConstructorWitness env U registry lower Γ left right oldType demand)
    (bridge : FamilyRelation env U registry lower Γ oldType newType demand.family) :
    Nonempty (ConstructorWitness env U registry lower Γ left right newType demand) := by
  have current := bridge.mixed henv (witness.leftExposure.insertion henv)
  obtain ⟨code⟩ := current.atBase
    (witness.leftExposure.targetWF henv)
  have route := code.leftExposure.insertion henv
  obtain ⟨shifted, contextEq, mapEq, _⟩ := witness.transportDisplay henv laws.toLowerTransport route
  have path : TypeConversion env U shifted.context
      (oldType.lift' shifted.map) (newType.lift' shifted.map) := by
    rw [contextEq, mapEq]
    simpa only [← lift'_comp] using code.path
  have next := bridge.mixed henv (shifted.leftExposure.insertion henv)
  exact ⟨{ shifted with
    leftExposure := shifted.leftExposure.convert path
    rightExposure := shifted.rightExposure.convert path
    leftBridge := shifted.leftBridge.trans henv laws next
    rightBridge := shifted.rightBridge.trans henv laws next }⟩

theorem RecordWitness.registryScoped (henv : env.Ordered)
    (witness : RecordWitness env U registry lower Γ left right type demand) : registry.Scoped := by
  obtain ⟨code⟩ := witness.typeCode.atBase (witness.insertion.targetWF henv witness.baseWF)
  exact code.registryScoped

theorem RecordWitness.transportDisplay (henv : env.Ordered) (laws : LowerTransport env U lower)
    (witness : RecordWitness env U registry lower Γ left right type demand)
    (route : MixedInsertion env U witness.context Δ ρ) :
    ∃ shifted : RecordWitness env U registry lower Γ left right type demand,
      shifted.context = Δ ∧ shifted.map = witness.map.comp ρ := by
  refine ⟨{
    info := witness.info, lookup := witness.lookup, bounded := witness.bounded
    ctorDefinition := witness.ctorDefinition, ctorNative := witness.ctorNative
    ctorQuotient := witness.ctorQuotient
    baseWF := witness.baseWF, context := Δ, map := witness.map.comp ρ
    insertion := witness.insertion.comp route
    typeCode := ?_, leftType := ?_, rightType := ?_
    leftOrigins := ?_, rightOrigins := ?_, fields := ?_ }, rfl, rfl⟩
  · simpa only [← lift'_comp, FamilyData.rename_comp] using witness.typeCode.mixed henv route
  · simpa only [HasType, ← lift'_comp] using route.eq henv witness.leftType
  · simpa only [HasType, ← lift'_comp] using route.eq henv witness.rightType
  · intro entry member
    obtain ⟨origin⟩ := witness.leftOrigins entry member
    exact ⟨by simpa only [← lift'_comp] using origin.transport henv route⟩
  · intro entry member
    obtain ⟨origin⟩ := witness.rightOrigins entry member
    exact ⟨by simpa only [← lift'_comp] using origin.transport henv route⟩
  · simpa only [List.map_map, Function.comp_def, DataRequest.rename_comp, lift', ← lift'_comp] using
      witness.fields.transport henv laws route

def RecordWitness.symm (henv : env.Ordered) (laws : LowerEquality env U registry lower)
    (witness : RecordWitness env U registry lower Γ left right type demand) :
    RecordWitness env U registry lower Γ right left type demand :=
  { witness with
    leftType := witness.rightType, rightType := witness.leftType
    leftOrigins := witness.rightOrigins, rightOrigins := witness.leftOrigins
    fields := witness.fields.symm laws (witness.registryScoped henv) }

theorem RecordWitness.trans (henv : env.Ordered) (laws : LowerEquality env U registry lower)
    (first : RecordWitness env U registry lower Γ left middle type demand)
    (second : RecordWitness env U registry lower Γ middle right type demand) :
    Nonempty (RecordWitness env U registry lower Γ left right type demand) := by
  obtain ⟨Ω, i, j, firstLeg, secondLeg, maps⟩ := first.insertion.amalgam henv first.baseWF second.insertion
  obtain ⟨before, context₁, map₁⟩ := first.transportDisplay henv laws.toLowerTransport firstLeg
  obtain ⟨after, context₂, map₂⟩ := second.transportDisplay henv laws.toLowerTransport secondLeg
  have contexts : before.context = after.context := context₁.trans context₂.symm
  have commonMap : before.map = after.map := map₁.trans (maps.trans map₂.symm)
  have commonInfo : before.info = after.info := Option.some.inj (before.lookup.symm.trans after.lookup)
  have later := after.fields
  rw [← contexts, ← commonMap] at later
  exact ⟨{ before with
    rightType := by simpa only [contexts, commonMap] using after.rightType
    rightOrigins := by simpa only [contexts, commonMap, commonInfo] using after.rightOrigins
    fields := before.fields.trans laws (before.registryScoped henv) later }⟩

theorem RecordWitness.convert (henv : env.Ordered) (laws : LowerEquality env U registry lower)
    (witness : RecordWitness env U registry lower Γ left right oldType demand)
    (bridge : FamilyRelation env U registry lower Γ oldType newType demand.family) :
    Nonempty (RecordWitness env U registry lower Γ left right newType demand) := by
  obtain ⟨code⟩ := (bridge.mixed henv witness.insertion).atBase
    (witness.insertion.targetWF henv witness.baseWF)
  obtain ⟨shifted, contextEq, mapEq⟩ := witness.transportDisplay henv laws.toLowerTransport
    (code.leftExposure.insertion henv)
  have path : TypeConversion env U shifted.context
      (oldType.lift' shifted.map) (newType.lift' shifted.map) := by
    rw [contextEq, mapEq]
    simpa only [← lift'_comp] using code.path
  have next := bridge.mixed henv shifted.insertion
  exact ⟨{ shifted with
    typeCode := (next.symm laws).left_diagonal
      (fun _ _ _ _ _ _ h => laws.trans code.registryScoped h (laws.symm h))
    leftType := path.cast shifted.leftType, rightType := path.cast shifted.rightType
    leftOrigins := by
      intro entry member
      obtain ⟨origin⟩ := shifted.leftOrigins entry member
      exact ⟨origin.convertAssignedType path⟩
    rightOrigins := by
      intro entry member
      obtain ⟨origin⟩ := shifted.rightOrigins entry member
      exact ⟨origin.convertAssignedType path⟩ }⟩

theorem ConstructorRelation.symm (henv : env.Ordered) (laws : LowerEquality env U registry lower)
    (h : ConstructorRelation env U registry lower Γ left right type demand) :
    ConstructorRelation env U registry lower Γ right left type demand := by
  intro Δ ρ future
  obtain ⟨w⟩ := h Δ ρ future
  exact ⟨w.symm henv laws⟩

theorem ConstructorRelation.trans (henv : env.Ordered) (laws : LowerEquality env U registry lower)
    (first : ConstructorRelation env U registry lower Γ left middle type demand)
    (second : ConstructorRelation env U registry lower Γ middle right type demand) :
    ConstructorRelation env U registry lower Γ left right type demand := by
  intro Δ ρ future
  obtain ⟨before⟩ := first Δ ρ future
  obtain ⟨after⟩ := second Δ ρ future
  exact before.trans henv laws after

theorem ConstructorRelation.convert (henv : env.Ordered) (laws : LowerEquality env U registry lower)
    (h : ConstructorRelation env U registry lower Γ left right oldType demand)
    (bridge : FamilyRelation env U registry lower Γ oldType newType demand.family) :
    ConstructorRelation env U registry lower Γ left right newType demand := by
  intro Δ ρ future
  obtain ⟨w⟩ := h Δ ρ future
  exact w.convert henv laws (bridge.future henv future)

theorem RecordRelation.symm (henv : env.Ordered) (laws : LowerEquality env U registry lower)
    (h : RecordRelation env U registry lower Γ left right type demand) :
    RecordRelation env U registry lower Γ right left type demand := by
  intro Δ ρ future
  obtain ⟨w⟩ := h Δ ρ future
  exact ⟨w.symm henv laws⟩

theorem RecordRelation.trans (henv : env.Ordered) (laws : LowerEquality env U registry lower)
    (first : RecordRelation env U registry lower Γ left middle type demand)
    (second : RecordRelation env U registry lower Γ middle right type demand) :
    RecordRelation env U registry lower Γ left right type demand := by
  intro Δ ρ future
  obtain ⟨before⟩ := first Δ ρ future
  obtain ⟨after⟩ := second Δ ρ future
  exact before.trans henv laws after

theorem RecordRelation.convert (henv : env.Ordered) (laws : LowerEquality env U registry lower)
    (h : RecordRelation env U registry lower Γ left right oldType demand)
    (bridge : FamilyRelation env U registry lower Γ oldType newType demand.family) :
    RecordRelation env U registry lower Γ left right newType demand := by
  intro Δ ρ future
  obtain ⟨w⟩ := h Δ ρ future
  exact w.convert henv laws (bridge.future henv future)

end Lean4Lean.AnchoredSemantics.RankedData
