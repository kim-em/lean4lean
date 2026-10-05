import Lean4Lean.Theory.Typing.AnchoredTypeExposure
import Lean4Lean.Theory.Typing.AnchoredRelations
import Lean4Lean.Theory.Typing.AnchoredDataExposure
import Lean4Lean.Theory.Typing.AnchoredConstructorDisplay

/-! Successor-rank data clauses parameterized by the already constructed lower
rank. These definitions import neither `AnchoredSemantics` nor any theorem
about the completed relation. The family descriptor frozen by a constructor
or record is used literally, including all parameter and index requests. -/

namespace Lean4Lean.AnchoredProfiles
open VExpr

variable {n : Nat}

def DataRequest.rename (ρ : Lift) (request : DataRequest (Profile n)) : DataRequest (Profile n) :=
  request.map (·.lift' ρ) (Profile.rename ρ)

theorem DataRequest.rename_comp (request : DataRequest (Profile n)) (ρ τ : Lift) :
    (request.rename ρ).rename τ = request.rename (ρ.comp τ) := by
  unfold rename
  rw [DataRequest.map_map]
  congr 1
  · funext e; exact lift'_comp.symm
  · funext p; exact (Profile.rename_comp p ρ τ).symm

theorem DataRequest.rename_refl (request : DataRequest (Profile n)) : request.rename .refl = request := by
  unfold rename
  rw [show (fun e : VExpr => e.lift' .refl) = id from funext (fun _ => lift'_refl),
    show Profile.rename (n := n) .refl = id from funext Profile.rename_refl, DataRequest.map_id]

def FamilyData.rename (data : FamilyData (Profile n)) (ρ : Lift) : FamilyData (Profile n) :=
  data.map (·.lift' ρ) (Profile.rename ρ)

def ConstructorData.rename (data : ConstructorData (Profile n)) (ρ : Lift) : ConstructorData (Profile n) :=
  data.map (·.lift' ρ) (Profile.rename ρ)

def RecordData.rename (data : RecordData (Profile n)) (ρ : Lift) : RecordData (Profile n) :=
  data.map (·.lift' ρ) (Profile.rename ρ)

theorem FamilyData.rename_comp (data : FamilyData (Profile n)) (ρ τ : Lift) :
    (data.rename ρ).rename τ = data.rename (ρ.comp τ) := by
  unfold rename
  rw [FamilyData.map_map]
  congr 1
  · funext e; exact lift'_comp.symm
  · funext p; exact (Profile.rename_comp p ρ τ).symm

theorem ConstructorData.rename_comp (data : ConstructorData (Profile n)) (ρ τ : Lift) :
    (data.rename ρ).rename τ = data.rename (ρ.comp τ) := by
  unfold rename
  rw [ConstructorData.map_map]
  congr 1
  · funext e; exact lift'_comp.symm
  · funext p; exact (Profile.rename_comp p ρ τ).symm

theorem RecordData.rename_comp (data : RecordData (Profile n)) (ρ τ : Lift) :
    (data.rename ρ).rename τ = data.rename (ρ.comp τ) := by
  unfold rename
  rw [RecordData.map_map]
  congr 1
  · funext e; exact lift'_comp.symm
  · funext p; exact (Profile.rename_comp p ρ τ).symm

end Lean4Lean.AnchoredProfiles

namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv AnchoredProfiles

/-- Data demands freeze their complete lower-rank support along with the input.
No hidden support can contain private syntax absent from the descriptor. -/
def RequestAdmission (env : VEnv) (U : Nat) (lower : Relations n)
    (Γ : List VExpr) (request : DataRequest (Profile n)) (left right : VExpr) : Prop :=
  env.IsDefEq U Γ request.anchor left request.domain ∧
  env.IsDefEq U Γ left right request.domain ∧
  request.input.HasType request.support ∧ request.support.HasType (.sort true) ∧
  lower.code Γ request.domain request.domain request.support ∧
  lower.term Γ request.anchor left request.domain request.input request.support ∧
  lower.term Γ left right request.domain request.input request.support

theorem RequestAdmission.toAdmission
    (admitted : RequestAdmission env U lower Γ request left right) :
    Admission env U lower Γ request.toKeyData left right :=
  ⟨admitted.1, admitted.2.1, request.support, admitted.2.2⟩

/-- One lower-rank query per actual argument position. No argument is
reconstructed from raw equality or from a family head alone. -/
inductive Arguments (env : VEnv) (U : Nat) (lower : Relations n)
    (Γ : List VExpr) : List (DataRequest (Profile n)) → List VExpr → List VExpr → Prop where
  | nil : Arguments env U lower Γ [] [] []
  | cons : RequestAdmission env U lower Γ key left right →
      Arguments env U lower Γ keys lefts rights →
      Arguments env U lower Γ (key :: keys) (left :: lefts) (right :: rights)

/-- Actual typed family exposures share one private world. Raw formation and
conversion are retained there; no proof-world reflection is asserted. -/
structure FamilyWitness (env : VEnv) (U : Nat) (registry : CanonicalDataHead.Registry)
    (lower : Relations n) (Γ : List VExpr) (left right : VExpr)
    (demand : FamilyData (Profile n)) where
  /-- The fixed syntax table is scoped by its original declaration history.
  This supplies the trace-transport invariant needed when composing the
  lower-rank argument admissions. -/
  registryScoped : registry.Scoped
  headInert : CanonicalDataHead.HeadInert registry demand.name
  context : List VExpr
  map : Lift
  leftLevel : VLevel
  rightLevel : VLevel
  leftRelevance : Relevant leftLevel demand.relevant
  rightRelevance : Relevant rightLevel demand.relevant
  path : TypeConversion env U context (left.lift' map) (right.lift' map)
  leftLevels : List VLevel
  rightLevels : List VLevel
  leftArguments : List VExpr
  rightArguments : List VExpr
  /-- Relevance belongs to the displayed family heads. A raw conversion chain
  need not classify the source operands at these same universe levels. -/
  leftType : env.HasType U context (mkApps (.const demand.name leftLevels) leftArguments) (.sort leftLevel)
  rightType : env.HasType U context (mkApps (.const demand.name rightLevels) rightArguments) (.sort rightLevel)
  leftExposure : Exposure env U registry Γ left context map
    (mkApps (.const demand.name leftLevels) leftArguments)
  rightExposure : Exposure env U registry Γ right context map
    (mkApps (.const demand.name rightLevels) rightArguments)
  leftTerminal : CanonicalDataHead.step registry (mkApps (.const demand.name leftLevels) leftArguments) = none
  rightTerminal : CanonicalDataHead.step registry (mkApps (.const demand.name rightLevels) rightArguments) = none
  leftUniverses : List.Forall₂ (· ≈ ·) demand.levels leftLevels
  rightUniverses : List.Forall₂ (· ≈ ·) demand.levels rightLevels
  arguments : Arguments env U lower context
    (demand.arguments.map (fun request => request.rename map)) leftArguments rightArguments

/-- Future closure retains the same finite family descriptor. This is a
positive finite clause at the successor rank, using only `lower` admissions. -/
def FamilyRelation (env : VEnv) (U : Nat) (registry : CanonicalDataHead.Registry)
    (lower : Relations n) (Γ : List VExpr) (left right : VExpr)
    (demand : FamilyData (Profile n)) : Prop :=
  ∀ Δ ρ, FutureInsertion env U Γ Δ ρ →
    Nonempty (FamilyWitness env U registry lower Δ (left.lift' ρ) (right.lift' ρ)
      (demand.rename ρ))

/-- Constructor endpoints retain actual declaration-derived family results,
with separate bridges to the assigned type at the exact frozen descriptor. -/
structure ConstructorWitness (env : VEnv) (U : Nat) (registry : CanonicalDataHead.Registry)
    (lower : Relations n) (Γ : List VExpr) (left right type : VExpr)
    (demand : ConstructorData (Profile n)) where
  headInert : CanonicalDataHead.HeadInert registry demand.name
  context : List VExpr
  map : Lift
  leftLevels : List VLevel
  rightLevels : List VLevel
  leftArguments : List VExpr
  rightArguments : List VExpr
  leftExposure : ConstructorDisplay env U registry Γ left type context map
    (mkApps (.const demand.name leftLevels) leftArguments)
  rightExposure : ConstructorDisplay env U registry Γ right type context map
    (mkApps (.const demand.name rightLevels) rightArguments)
  leftTerminal : CanonicalDataHead.step registry (mkApps (.const demand.name leftLevels) leftArguments) = none
  rightTerminal : CanonicalDataHead.step registry (mkApps (.const demand.name rightLevels) rightArguments) = none
  leftUniverses : List.Forall₂ (· ≈ ·) demand.levels leftLevels
  rightUniverses : List.Forall₂ (· ≈ ·) demand.levels rightLevels
  arguments : Arguments env U lower context
    (demand.arguments.map (fun request => request.rename map)) leftArguments rightArguments
  leftHeader : ConstructorResultHeader env demand.name demand.family.name leftLevels leftArguments
  rightHeader : ConstructorResultHeader env demand.name demand.family.name rightLevels rightArguments
  leftBridge : FamilyRelation env U registry lower context leftHeader.result
    (type.lift' map) (demand.family.rename map)
  rightBridge : FamilyRelation env U registry lower context rightHeader.result
    (type.lift' map) (demand.family.rename map)

def ConstructorRelation (env : VEnv) (U : Nat) (registry : CanonicalDataHead.Registry)
    (lower : Relations n) (Γ : List VExpr) (left right type : VExpr)
    (demand : ConstructorData (Profile n)) : Prop :=
  ∀ Δ ρ, FutureInsertion env U Γ Δ ρ →
    Nonempty (ConstructorWitness env U registry lower Δ
      (left.lift' ρ) (right.lift' ρ) (type.lift' ρ) (demand.rename ρ))

/-- One actual primitive-projection typing derivation. The literal field
type and family may differ from the observation's assigned types; both typed
conversion paths are retained rather than inferred from type uniqueness. -/
structure ProjectionOrigin (env : VEnv) (U : Nat) (Γ : List VExpr)
    (info : VProjectionInfo) (name : Name) (index : Nat)
    (major assignedType domain : VExpr) where
  registered : env.projections name info
  levels : List VLevel
  levelsWF : ∀ level ∈ levels, level.WF U
  levelCount : levels.length = info.uvars
  params : List VExpr
  paramCount : params.length = info.nparams
  indexArgs : List VExpr
  indexCount : indexArgs.length = info.nindices
  sourceMajor : VExpr
  fieldType : VExpr
  fieldLevel : VLevel
  selected : info.fieldType name levels params index sourceMajor = some fieldType
  formation : env.HasType U Γ fieldType (.sort fieldLevel)
  familyPath : TypeConversion env U Γ assignedType (mkApps (.const name levels) (params ++ indexArgs))
  majorEq : env.IsDefEq U Γ sourceMajor major (mkApps (.const name levels) (params ++ indexArgs))
  ctorClosed : info.ctorType.Closed
  guard : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero
  fieldPath : TypeConversion env U Γ fieldType domain

/-- Projection observations retain a real private world and an exact family
bridge, while permitting neutral record endpoints. -/
structure RecordWitness (env : VEnv) (U : Nat) (registry : CanonicalDataHead.Registry)
    (lower : Relations n) (Γ : List VExpr) (left right type : VExpr)
    (demand : RecordData (Profile n)) where
  baseWF : OnCtx Γ (env.IsType U)
  context : List VExpr
  map : Lift
  insertion : MixedInsertion env U Γ context map
  info : VProjectionInfo
  lookup : registry.projections demand.family.name = some info
  ctorDefinition : registry.definitions info.ctorName = none
  ctorNative : registry.natives info.ctorName = none
  ctorQuotient : registry.quotient = false ∨ info.ctorName ≠ ``Quot.lift
  bounded : ∀ entry ∈ demand.fields, entry.1 < info.numFields
  typeCode : FamilyRelation env U registry lower context (type.lift' map) (type.lift' map)
    (demand.family.rename map)
  leftType : env.HasType U context (left.lift' map) (type.lift' map)
  rightType : env.HasType U context (right.lift' map) (type.lift' map)
  leftOrigins : ∀ entry ∈ demand.fields,
    Nonempty (ProjectionOrigin env U context info demand.family.name entry.1
      (left.lift' map) (type.lift' map) (entry.2.domain.lift' map))
  rightOrigins : ∀ entry ∈ demand.fields,
    Nonempty (ProjectionOrigin env U context info demand.family.name entry.1
      (right.lift' map) (type.lift' map) (entry.2.domain.lift' map))
  fields : Arguments env U lower context (demand.fields.map (fun entry => entry.2.rename map))
    (demand.fields.map (fun entry => .proj demand.family.name entry.1 (left.lift' map)))
    (demand.fields.map (fun entry => .proj demand.family.name entry.1 (right.lift' map)))

def RecordRelation (env : VEnv) (U : Nat) (registry : CanonicalDataHead.Registry)
    (lower : Relations n) (Γ : List VExpr) (left right type : VExpr)
    (demand : RecordData (Profile n)) : Prop :=
  ∀ Δ ρ, FutureInsertion env U Γ Δ ρ →
    Nonempty (RecordWitness env U registry lower Δ
      (left.lift' ρ) (right.lift' ρ) (type.lift' ρ) (demand.rename ρ))

theorem FamilyRelation.future (henv : env.Ordered)
    (related : FamilyRelation env U registry lower Γ left right demand)
    (route : FutureInsertion env U Γ Δ ρ) :
    FamilyRelation env U registry lower Δ (left.lift' ρ) (right.lift' ρ) (demand.rename ρ) := by
  intro Ω τ future
  simpa only [lift'_comp, FamilyData.rename_comp] using
    related Ω (ρ.comp τ) (route.comp future henv)

theorem ConstructorRelation.future (henv : env.Ordered)
    (related : ConstructorRelation env U registry lower Γ left right type demand)
    (route : FutureInsertion env U Γ Δ ρ) :
    ConstructorRelation env U registry lower Δ
      (left.lift' ρ) (right.lift' ρ) (type.lift' ρ) (demand.rename ρ) := by
  intro Ω τ future
  simpa only [lift'_comp, ConstructorData.rename_comp] using
    related Ω (ρ.comp τ) (route.comp future henv)

theorem RecordRelation.future (henv : env.Ordered)
    (related : RecordRelation env U registry lower Γ left right type demand)
    (route : FutureInsertion env U Γ Δ ρ) :
    RecordRelation env U registry lower Δ
      (left.lift' ρ) (right.lift' ρ) (type.lift' ρ) (demand.rename ρ) := by
  intro Ω τ future
  simpa only [lift'_comp, RecordData.rename_comp] using
    related Ω (ρ.comp τ) (route.comp future henv)

end Lean4Lean.AnchoredSemantics.RankedData
