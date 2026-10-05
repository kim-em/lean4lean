import Lean4Lean.Theory.VExpr

/-! Syntax shared by finite anchored profiles and their data descriptors.
All keys in a descriptor use the same parameter `P`; no semantic relation,
source observation, or type-support predicate occurs in these declarations. -/

namespace Lean4Lean.AnchoredProfiles

structure KeyData (P : Type) where
  domain : VExpr
  anchor : VExpr
  input : P

/-- A data argument or projection request freezes its finite type support
alongside its ordinary anchored key. No private witness chooses this syntax. -/
structure DataRequest (P : Type) extends KeyData P where
  support : P

instance : Coe (DataRequest P) (KeyData P) := ⟨DataRequest.toKeyData⟩

/-- Parameters and indices occupy their actual declaration positions. The
whole descriptor, including every argument request, is frozen by a value. -/
structure FamilyData (P : Type) where
  name : Name
  levels : List VLevel
  relevant : Bool
  arguments : List (DataRequest P)

/-- Relevant constructor observations retain both their constructor tag and
an exact family descriptor, even when every field request is empty. -/
structure ConstructorData (P : Type) where
  name : Name
  levels : List VLevel
  arguments : List (DataRequest P)
  family : FamilyData P
  relevant : family.relevant = true

/-- Structure observations use primitive projections, so neutral values can
be observed without inventing a constructor exposure. -/
structure RecordData (P : Type) where
  family : FamilyData P
  relevant : family.relevant = true
  fields : List (Nat × DataRequest P)

variable {P Q R : Type}

def KeyData.map (raw : VExpr → VExpr) (input : P → Q) (key : KeyData P) : KeyData Q :=
  ⟨raw key.domain, raw key.anchor, input key.input⟩

def DataRequest.map (raw : VExpr → VExpr) (profile : P → Q) (request : DataRequest P) : DataRequest Q :=
  ⟨request.toKeyData.map raw profile, profile request.support⟩

theorem DataRequest.map_map (raw raw' : VExpr → VExpr) (profile : P → Q) (profile' : Q → R)
    (request : DataRequest P) :
    (request.map raw profile).map raw' profile' = request.map (raw' ∘ raw) (profile' ∘ profile) := rfl

@[simp] theorem DataRequest.map_id (request : DataRequest P) : request.map id id = request := by
  cases request; rfl

def FamilyData.map (raw : VExpr → VExpr) (input : P → Q) (data : FamilyData P) : FamilyData Q :=
  { data with arguments := data.arguments.map (DataRequest.map raw input) }

def ConstructorData.map (raw : VExpr → VExpr) (input : P → Q)
    (data : ConstructorData P) : ConstructorData Q :=
  { data with
    arguments := data.arguments.map (DataRequest.map raw input)
    family := data.family.map raw input }

def RecordData.map (raw : VExpr → VExpr) (input : P → Q) (data : RecordData P) : RecordData Q :=
  { data with
    family := data.family.map raw input
    fields := data.fields.map (fun entry => (entry.1, entry.2.map raw input)) }

theorem KeyData.map_map (raw raw' : VExpr → VExpr) (input : P → Q) (input' : Q → R)
    (key : KeyData P) :
    (key.map raw input).map raw' input' = key.map (raw' ∘ raw) (input' ∘ input) := rfl

theorem FamilyData.map_map (raw raw' : VExpr → VExpr) (input : P → Q) (input' : Q → R)
    (data : FamilyData P) :
    (data.map raw input).map raw' input' = data.map (raw' ∘ raw) (input' ∘ input) := by
  cases data
  simp only [map, List.map_map, Function.comp_def, DataRequest.map_map]

theorem ConstructorData.map_map (raw raw' : VExpr → VExpr) (input : P → Q) (input' : Q → R)
    (data : ConstructorData P) :
    (data.map raw input).map raw' input' = data.map (raw' ∘ raw) (input' ∘ input) := by
  cases data
  simp only [map, FamilyData.map_map, List.map_map, Function.comp_def, DataRequest.map_map]

theorem RecordData.map_map (raw raw' : VExpr → VExpr) (input : P → Q) (input' : Q → R)
    (data : RecordData P) :
    (data.map raw input).map raw' input' = data.map (raw' ∘ raw) (input' ∘ input) := by
  cases data
  simp only [map, FamilyData.map_map, List.map_map, Function.comp_def, DataRequest.map_map]


@[simp] theorem KeyData.map_id (key : KeyData P) : key.map id id = key := by
  cases key; rfl

@[simp] theorem FamilyData.map_id (data : FamilyData P) : data.map id id = data := by
  cases data
  simp only [map, show DataRequest.map (P := P) id id = id from funext DataRequest.map_id, List.map_id]

@[simp] theorem ConstructorData.map_id (data : ConstructorData P) : data.map id id = data := by
  cases data
  simp only [map, FamilyData.map_id, show DataRequest.map (P := P) id id = id from funext DataRequest.map_id, List.map_id]

@[simp] theorem RecordData.map_id (data : RecordData P) : data.map id id = data := by
  cases data
  simp only [map, FamilyData.map_id, DataRequest.map_id, Prod.eta]
  rw [show (fun entry : Nat × DataRequest P => entry) = id from rfl, List.map_id]

theorem KeyData.map_injective {raw : VExpr → VExpr} {input : P → Q}
    (hr : Function.Injective raw) (hi : Function.Injective input) :
    Function.Injective (KeyData.map raw input) := by
  rintro ⟨d,a,p⟩ ⟨e,b,q⟩ equal
  obtain ⟨de, ab, pq⟩ := KeyData.mk.inj equal
  cases hr de; cases hr ab; cases hi pq; rfl

theorem DataRequest.map_injective {raw : VExpr → VExpr} {profile : P → Q}
    (hr : Function.Injective raw) (hp : Function.Injective profile) :
    Function.Injective (DataRequest.map raw profile) := by
  rintro ⟨key, support⟩ ⟨key', support'⟩ equal
  have keys := KeyData.map_injective hr hp (congrArg DataRequest.toKeyData equal)
  have supports := hp (congrArg DataRequest.support equal)
  cases keys; cases supports; rfl

theorem FamilyData.map_injective {raw : VExpr → VExpr} {input : P → Q}
    (hr : Function.Injective raw) (hi : Function.Injective input) :
    Function.Injective (FamilyData.map raw input) := by
  rintro ⟨name,levels,relevant,args⟩ ⟨name',levels',relevant',args'⟩ equal
  obtain ⟨names, packets, flags, arguments⟩ := FamilyData.mk.inj equal
  cases names; cases packets; cases flags
  have same := (List.map_inj_right (fun _ _ h => DataRequest.map_injective hr hi h)).mp arguments
  cases same; rfl

theorem ConstructorData.map_injective {raw : VExpr → VExpr} {input : P → Q}
    (hr : Function.Injective raw) (hi : Function.Injective input) :
    Function.Injective (ConstructorData.map raw input) := by
  intro first second equal
  have names := congrArg ConstructorData.name equal
  have packets := congrArg ConstructorData.levels equal
  have args := (List.map_inj_right (fun _ _ h => DataRequest.map_injective hr hi h)).mp
    (congrArg ConstructorData.arguments equal)
  have families := FamilyData.map_injective hr hi (congrArg ConstructorData.family equal)
  cases first; cases second
  cases names; cases packets; cases args; cases families; rfl

theorem RecordData.map_injective {raw : VExpr → VExpr} {input : P → Q}
    (hr : Function.Injective raw) (hi : Function.Injective input) :
    Function.Injective (RecordData.map raw input) := by
  intro first second equal
  have families := FamilyData.map_injective hr hi (congrArg RecordData.family equal)
  have fields := congrArg RecordData.fields equal
  have fields := (List.map_inj_right (fun a b h => by
    have parts := Prod.mk.inj h
    exact Prod.ext parts.1 (DataRequest.map_injective hr hi parts.2))).mp fields
  cases first; cases second; cases families; cases fields; rfl

end Lean4Lean.AnchoredProfiles
