import Lean4Lean.Theory.Typing.AnchoredConstructorIntroduction
import Lean4Lean.Theory.Typing.AnchoredFamilyAnchorBridge

/-! A directed record-to-constructor packet retains finite evidence at one
actual display world. Field admissions may come from different record
observers after their explicit source domain and input alignments. No
semantic callback or equality of those record descriptors is assumed. -/
namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

def etaFields (name : Name) (count : Nat) (major : VExpr) : List VExpr :=
  (List.range count).map (fun index => .proj name index major)

private theorem levels_self (levels : List VLevel) : List.Forall₂ (· ≈ ·) levels levels :=
  Lean4Lean.List.Forall₂.rfl fun _ _ => rfl

private theorem familySeed
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {family : FamilyData (Profile n)} {levels : List VLevel} {params : List VExpr}
    (definitions : registry.definitions family.name = none)
    (natives : registry.natives family.name = none)
    (quotient : registry.quotient = false ∨ family.name ≠ ``Quot.lift)
    (packet : List.Forall₂ (· ≈ ·) family.levels levels)
    (typed : env.HasType U Γ (mkApps (.const family.name levels) params) (.sort level))
    (flag : Relevant level family.relevant)
    (arguments : Arguments env U (relations env U registry n) Γ family.arguments params params) :
    FamilyRelation env U registry (relations env U registry n) Γ
      (mkApps (.const family.name levels) params) (mkApps (.const family.name levels) params) family := by
  have seed := literalFamilyCodeOfInert henv hscoped ⟨definitions, natives, quotient⟩ typed flag arguments
  intro Δ ρ future
  obtain ⟨witness⟩ := seed Δ ρ future
  exact ⟨{ witness with
    leftUniverses := Lean4Lean.List.Forall₂.trans (fun _ _ _ h h' => h.trans h') packet witness.leftUniverses
    rightUniverses := Lean4Lean.List.Forall₂.trans (fun _ _ _ h h' => h.trans h') packet witness.rightUniverses }⟩

/-- Declaration lookup, raw eta typing, and exact lower-rank admissions.
The two parameter admissions are deliberately separate: satisfying a
constructor request does not imply satisfying its frozen family request.
The parameter vector may therefore retain the original literal source seed. -/
structure RecordConstructorPacket (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (left right type : VExpr) (demand : ConstructorData (Profile n)) where
  info : VProjectionInfo
  registered : env.projections demand.family.name info
  constructorName : demand.name = info.ctorName
  unindexed : info.nindices = 0
  levels : List VLevel
  constructorPacket : List.Forall₂ (· ≈ ·) demand.levels levels
  parameterRequests : List (DataRequest (Profile n))
  fieldRequests : List (DataRequest (Profile n))
  parameters : List VExpr
  parameterCount : parameters.length = info.nparams
  argumentShape : demand.arguments = parameterRequests ++ fieldRequests
  parameterAdmissions : Arguments env U (relations env U registry n) Γ
    parameterRequests parameters parameters
  fieldAdmissions : Arguments env U (relations env U registry n) Γ fieldRequests
    (etaFields demand.family.name info.numFields left)
    (etaFields demand.family.name info.numFields right)
  familyDefinitions : registry.definitions demand.family.name = none
  familyNatives : registry.natives demand.family.name = none
  familyQuotient : registry.quotient = false ∨ demand.family.name ≠ ``Quot.lift
  familyPacket : List.Forall₂ (· ≈ ·) demand.family.levels levels
  familyLevel : VLevel
  familyTyped : env.HasType U Γ (mkApps (.const demand.family.name levels) parameters)
    (.sort familyLevel)
  familyRelevant : Relevant familyLevel demand.family.relevant
  familyAdmissions : Arguments env U (relations env U registry n) Γ
    demand.family.arguments parameters parameters
  assignedFamily : TypeConversion env U Γ type (mkApps (.const demand.family.name levels) parameters)
  leftExpansionTyped : env.HasType U Γ
    (mkApps (.const demand.name levels)
      (parameters ++ etaFields demand.family.name info.numFields left))
    (mkApps (.const demand.family.name levels) parameters)
  rightExpansionTyped : env.HasType U Γ
    (mkApps (.const demand.name levels)
      (parameters ++ etaFields demand.family.name info.numFields right))
    (mkApps (.const demand.family.name levels) parameters)
  leftHeader : ConstructorResultHeader env demand.name demand.family.name levels
    (parameters ++ etaFields demand.family.name info.numFields left)
  rightHeader : ConstructorResultHeader env demand.name demand.family.name levels
    (parameters ++ etaFields demand.family.name info.numFields right)
  leftResult : leftHeader.result = mkApps (.const demand.family.name levels) parameters
  rightResult : rightHeader.result = mkApps (.const demand.family.name levels) parameters

theorem Arguments.append
    (first : Arguments env U lower Γ requests left right)
    (second : Arguments env U lower Γ requests' left' right') :
    Arguments env U lower Γ (requests ++ requests') (left ++ left') (right ++ right') := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head ih

/-- Assemble an actual constructor witness from a record's real private
world and a finite aligned packet in that world. The family's exact demand
is retained, even when field observations came from independent records. -/
theorem RecordWitness.toConstructor
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (laws : LowerEquality env U registry (relations env U registry n))
    {Γ : List VExpr} {left right type : VExpr}
    {record : RecordData (Profile n)} {demand : ConstructorData (Profile n)}
    (inert : CanonicalDataHead.HeadInert registry demand.name)
    (sameFamily : demand.family = record.family)
    (witness : RecordWitness env U registry (relations env U registry n) Γ left right type record)
    (packet : RecordConstructorPacket env U registry witness.context
      (left.lift' witness.map) (right.lift' witness.map) (type.lift' witness.map)
      (demand.rename witness.map)) :
    Nonempty (ConstructorWitness env U registry (relations env U registry n) Γ left right type demand) := by
  let localDemand := demand.rename witness.map
  have majorLeft := packet.assignedFamily.cast witness.leftType
  have majorRight := packet.assignedFamily.cast witness.rightType
  have leftExpansion := packet.leftExpansionTyped
  have rightExpansion := packet.rightExpansionTyped
  rw [packet.constructorName] at leftExpansion rightExpansion
  have leftOrigin : ConstructorOrigin env U registry witness.context
      (left.lift' witness.map)
      (mkApps (.const demand.name packet.levels)
        (packet.parameters ++ etaFields demand.family.name packet.info.numFields (left.lift' witness.map)))
      (type.lift' witness.map) := by
    rw [show demand.name = packet.info.ctorName from packet.constructorName]
    exact .convert packet.assignedFamily.symm
      (.eta packet.registered packet.parameterCount packet.unindexed majorLeft leftExpansion)
  have rightOrigin : ConstructorOrigin env U registry witness.context
      (right.lift' witness.map)
      (mkApps (.const demand.name packet.levels)
        (packet.parameters ++ etaFields demand.family.name packet.info.numFields (right.lift' witness.map)))
      (type.lift' witness.map) := by
    rw [show demand.name = packet.info.ctorName from packet.constructorName]
    exact .convert packet.assignedFamily.symm
      (.eta packet.registered packet.parameterCount packet.unindexed majorRight rightExpansion)
  have seed := familySeed henv hscoped packet.familyDefinitions packet.familyNatives packet.familyQuotient
    packet.familyPacket packet.familyTyped packet.familyRelevant packet.familyAdmissions
  have typeCode := witness.typeCode
  rw [← sameFamily] at typeCode
  have bridge := seed.joinPath henv laws packet.assignedFamily.symm typeCode
  refine ⟨{
    headInert := inert
    context := witness.context, map := witness.map
    leftLevels := packet.levels, rightLevels := packet.levels
    leftArguments := packet.parameters ++ etaFields demand.family.name packet.info.numFields (left.lift' witness.map)
    rightArguments := packet.parameters ++ etaFields demand.family.name packet.info.numFields (right.lift' witness.map)
    leftExposure := ⟨witness.baseWF, witness.insertion, leftOrigin, leftOrigin.sound henv⟩
    rightExposure := ⟨witness.baseWF, witness.insertion, rightOrigin, rightOrigin.sound henv⟩
    leftTerminal := inert.step _ _, rightTerminal := inert.step _ _
    leftUniverses := packet.constructorPacket, rightUniverses := packet.constructorPacket
    arguments := ?_
    leftHeader := packet.leftHeader, rightHeader := packet.rightHeader
    leftBridge := ?_, rightBridge := ?_ }⟩
  · have args := packet.parameterAdmissions.append packet.fieldAdmissions
    rw [← packet.argumentShape] at args
    exact args
  · rw [packet.leftResult]
    exact bridge
  · rw [packet.rightResult]
    exact bridge

end Lean4Lean.AnchoredSemantics.RankedData
