import Lean4Lean.Theory.Typing.AnchoredFamilyCodeRelation

/-! Records are observed through their primitive projections. A neutral
record need not reduce to a constructor, so constructor-head observations
cannot support structure eta. The value demand freezes its exact family code
as well as its finite field requests, preserving the support-composition law. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

structure RecordDemand (n : Nat) where
  family : FamilyCodeDemand (n + 1)
  relevant : family.relevant = true
  fields : List (Nat × Key n)

def RecordDemand.keys (demand : RecordDemand n) : List FamilyKey :=
  demand.fields.map (fun entry => ⟨n, entry.2⟩)

def RecordDemand.projections (demand : RecordDemand n) (value : VExpr) : List VExpr :=
  demand.fields.map (fun entry => .proj demand.family.name entry.1 value)

/-- The lower relation sees actual primitive projections, including those
of neutral values. Family support is literal and cannot silently lose index
requests during a later conversion or transitive comparison. -/
structure RecordWitness (env : VEnv) (U : Nat) (registry : CanonicalDataHead.Registry)
    (Γ : List VExpr) (left right type : VExpr) (demand : RecordDemand n) where
  info : VProjectionInfo
  lookup : registry.projections demand.family.name = some info
  unindexed : info.nindices = 0
  bounded : ∀ entry ∈ demand.fields, entry.1 < info.numFields
  baseWF : OnCtx Γ (env.IsType U)
  context : List VExpr
  map : Lift
  insertion : MixedInsertion env U Γ context map
  typeCode : FamilyCodeRelation env U registry context (type.lift' map) (type.lift' map)
    (demand.family.rename map)
  leftType : env.HasType U context (left.lift' map) (type.lift' map)
  rightType : env.HasType U context (right.lift' map) (type.lift' map)
  fields : FamilyArguments env U registry.toRegistry context (demand.keys.map (·.rename map))
    (demand.projections (left.lift' map)) (demand.projections (right.lift' map))

private theorem projections_lift (demand : RecordDemand n) (value : VExpr) (ρ : Lift) :
    (demand.projections value).map (·.lift' ρ) = demand.projections (value.lift' ρ) := by
  simp only [RecordDemand.projections, List.map_map, Function.comp_def, lift']

namespace RecordWitness

/-- Relevance is witnessed in an actual private world; it is never
strengthened back across a proof insertion. -/
theorem relevant (henv : env.Ordered)
    (witness : RecordWitness env U registry Γ left right type demand) :
    ∃ Δ ρ level, MixedInsertion env U Γ Δ ρ ∧
      env.HasType U Δ (type.lift' ρ) (.sort level) ∧ ¬level ≈ .zero := by
  obtain ⟨code⟩ := witness.typeCode.atBase (witness.insertion.targetWF henv witness.baseWF)
  refine ⟨code.context, witness.map.comp code.map, code.leftLevel,
    witness.insertion.comp (code.leftExposure.insertion henv), ?_, ?_⟩
  · simpa only [← lift'_comp] using code.leftType
  · simpa only [FamilyCodeDemand.rename, demand.relevant, Relevant, if_true] using code.leftRelevance

/-- Projection observations and their exact type descriptor move together
along one concrete proof/context route. -/
theorem transportDisplay (henv : env.Ordered)
    (witness : RecordWitness env U registry Γ left right type demand)
    (route : MixedInsertion env U witness.context Δ ρ) :
    ∃ shifted : RecordWitness env U registry Γ left right type demand,
      shifted.context = Δ ∧ shifted.map = witness.map.comp ρ := by
  refine ⟨{
    info := witness.info
    lookup := witness.lookup
    unindexed := witness.unindexed
    bounded := witness.bounded
    baseWF := witness.baseWF
    context := Δ
    map := witness.map.comp ρ
    insertion := witness.insertion.comp route
    typeCode := ?_
    leftType := ?_
    rightType := ?_
    fields := ?_ }, rfl, rfl⟩
  · simpa only [← lift'_comp, FamilyCodeDemand.rename_comp] using witness.typeCode.mixed henv route
  · simpa only [HasType, ← lift'_comp] using route.eq henv witness.leftType
  · simpa only [HasType, ← lift'_comp] using route.eq henv witness.rightType
  · simpa only [List.map_map, Function.comp_def, FamilyKey.rename_comp, projections_lift,
      ← lift'_comp] using witness.fields.transport henv route

def left_diagonal (witness : RecordWitness env U registry Γ left right type demand) :
    RecordWitness env U registry Γ left left type demand :=
  { witness with rightType := witness.leftType, fields := witness.fields.left_diagonal }

theorem symm (henv : env.Ordered) (hscoped : registry.Scoped)
    (witness : RecordWitness env U registry Γ left right type demand) :
    Nonempty (RecordWitness env U registry Γ right left type demand) := by
  exact ⟨{ witness with
    leftType := witness.rightType
    rightType := witness.leftType
    fields := witness.fields.symm henv hscoped.base }⟩

theorem trans (henv : env.Ordered) (hscoped : registry.Scoped)
    (first : RecordWitness env U registry Γ left middle type demand)
    (second : RecordWitness env U registry Γ middle right type demand) :
    Nonempty (RecordWitness env U registry Γ left right type demand) := by
  obtain ⟨Ω, i, j, firstLeg, secondLeg, maps⟩ :=
    first.insertion.amalgam henv first.baseWF second.insertion
  obtain ⟨before, context₁, map₁⟩ := first.transportDisplay henv firstLeg
  obtain ⟨after, context₂, map₂⟩ := second.transportDisplay henv secondLeg
  have contexts : before.context = after.context := context₁.trans context₂.symm
  have commonMap : before.map = after.map := map₁.trans (maps.trans map₂.symm)
  have later := after.fields
  rw [← contexts, ← commonMap] at later
  exact ⟨{ before with
    rightType := by simpa only [contexts, commonMap] using after.rightType
    fields := before.fields.trans henv hscoped.base later }⟩

/-- The frozen descriptor is preserved by conversion. The raw cast happens
only after the record and both projection tuples have moved into the code
query's actual private world. -/
theorem convert (henv : env.Ordered) (hscoped : registry.Scoped)
    (witness : RecordWitness env U registry Γ left right oldType demand)
    (bridge : FamilyCodeRelation env U registry Γ oldType newType demand.family) :
    Nonempty (RecordWitness env U registry Γ left right newType demand) := by
  have current := bridge.mixed henv witness.insertion
  obtain ⟨code⟩ := current.atBase (witness.insertion.targetWF henv witness.baseWF)
  have route := code.leftExposure.insertion henv
  obtain ⟨shifted, contextEq, mapEq⟩ := witness.transportDisplay henv route
  have path : TypeConversion env U shifted.context
      (oldType.lift' shifted.map) (newType.lift' shifted.map) := by
    rw [contextEq, mapEq]
    simpa only [← lift'_comp] using code.path
  have next := bridge.mixed henv shifted.insertion
  exact ⟨{ shifted with
    typeCode := (next.symm henv hscoped).left_diagonal
    leftType := path.cast shifted.leftType
    rightType := path.cast shifted.rightType }⟩

end RecordWitness
end Lean4Lean.AnchoredSemantics
