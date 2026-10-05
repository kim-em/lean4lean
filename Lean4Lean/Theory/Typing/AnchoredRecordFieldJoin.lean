import Lean4Lean.Theory.Typing.AnchoredDataValueLaws
import Lean4Lean.Theory.Typing.AnchoredRecordProjection

/-! A record value observes a named finite projection tuple. Its assigned
family's full parameter code belongs to the surrounding type relation, not
to this value descriptor. This isolated candidate demonstrates that records
with different family-code requests can join their exact field requests. -/
namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

structure FieldRecordWitness (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (lower : Relations n) (Γ : List VExpr) (left right type : VExpr)
    (name : Name) (requests : List (Nat × DataRequest (Profile n))) where
  meaningful : ∃ entry ∈ requests, Profile.Nonempty entry.2.input
  baseWF : OnCtx Γ (env.IsType U)
  context : List VExpr
  map : Lift
  insertion : MixedInsertion env U Γ context map
  info : VProjectionInfo
  lookup : registry.projections name = some info
  ctorDefinition : registry.definitions info.ctorName = none
  ctorNative : registry.natives info.ctorName = none
  ctorQuotient : registry.quotient = false ∨ info.ctorName ≠ ``Quot.lift
  bounded : ∀ entry ∈ requests, entry.1 < info.numFields
  leftType : env.HasType U context (left.lift' map) (type.lift' map)
  rightType : env.HasType U context (right.lift' map) (type.lift' map)
  leftOrigins : ∀ entry ∈ requests, Nonempty (ProjectionOrigin env U context info name entry.1
    (left.lift' map) (type.lift' map) (entry.2.domain.lift' map))
  rightOrigins : ∀ entry ∈ requests, Nonempty (ProjectionOrigin env U context info name entry.1
    (right.lift' map) (type.lift' map) (entry.2.domain.lift' map))
  fields : Arguments env U lower context (requests.map (fun entry => entry.2.rename map))
    (requests.map (fun entry => .proj name entry.1 (left.lift' map)))
    (requests.map (fun entry => .proj name entry.1 (right.lift' map)))

/-- Forget only the value descriptor's redundant family-code demand.
All actual raw origins and frozen projection supports remain intact. -/
def RecordWitness.fieldView
    (witness : RecordWitness env U registry lower Γ left right type demand)
    (meaningful : ∃ entry ∈ demand.fields, Profile.Nonempty entry.2.input) :
    FieldRecordWitness env U registry lower Γ left right type demand.family.name demand.fields where
  meaningful := meaningful
  baseWF := witness.baseWF
  context := witness.context
  map := witness.map
  insertion := witness.insertion
  info := witness.info
  lookup := witness.lookup
  ctorDefinition := witness.ctorDefinition
  ctorNative := witness.ctorNative
  ctorQuotient := witness.ctorQuotient
  bounded := witness.bounded
  leftType := witness.leftType
  rightType := witness.rightType
  leftOrigins := witness.leftOrigins
  rightOrigins := witness.rightOrigins
  fields := witness.fields

theorem FieldRecordWitness.transportDisplay
    (henv : env.Ordered) (laws : LowerTransport env U lower)
    (witness : FieldRecordWitness env U registry lower Γ left right type name requests)
    (route : MixedInsertion env U witness.context Δ ρ) :
    ∃ shifted : FieldRecordWitness env U registry lower Γ left right type name requests,
      shifted.context = Δ ∧ shifted.map = witness.map.comp ρ := by
  refine ⟨{
    meaningful := witness.meaningful
    baseWF := witness.baseWF, context := Δ, map := witness.map.comp ρ
    insertion := witness.insertion.comp route
    info := witness.info, lookup := witness.lookup
    ctorDefinition := witness.ctorDefinition, ctorNative := witness.ctorNative
    ctorQuotient := witness.ctorQuotient, bounded := witness.bounded
    leftType := ?_, rightType := ?_, leftOrigins := ?_, rightOrigins := ?_, fields := ?_ }, rfl, rfl⟩
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

private theorem appendArguments
    (first : Arguments env U lower Γ requests left right)
    (second : Arguments env U lower Γ requests' left' right') :
    Arguments env U lower Γ (requests ++ requests') (left ++ left') (right ++ right') := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head ih

/-- Join observations of the same endpoints at the same actual assigned
type. The requests may retain unrelated frozen domains, anchors and supports;
each original admission is preserved at its own position. -/
theorem FieldRecordWitness.append
    (henv : env.Ordered) (laws : LowerTransport env U lower)
    (first : FieldRecordWitness env U registry lower Γ left right type name requests)
    (second : FieldRecordWitness env U registry lower Γ left right type name requests') :
    Nonempty (FieldRecordWitness env U registry lower Γ left right type name (requests ++ requests')) := by
  obtain ⟨Ω, i, j, firstLeg, secondLeg, maps⟩ :=
    first.insertion.amalgam henv first.baseWF second.insertion
  obtain ⟨before, context₁, map₁⟩ := first.transportDisplay henv laws firstLeg
  obtain ⟨after, context₂, map₂⟩ := second.transportDisplay henv laws secondLeg
  have contexts : before.context = after.context := context₁.trans context₂.symm
  have commonMap : before.map = after.map := map₁.trans (maps.trans map₂.symm)
  have commonInfo : before.info = after.info := Option.some.inj (before.lookup.symm.trans after.lookup)
  refine ⟨{
    before with
    meaningful := ?_
    bounded := ?_
    leftOrigins := ?_
    rightOrigins := ?_
    fields := ?_ }⟩
  · obtain ⟨entry, member, nonempty⟩ := before.meaningful
    exact ⟨entry, List.mem_append_left _ member, nonempty⟩
  · intro entry member
    rcases List.mem_append.mp member with member | member
    · exact before.bounded entry member
    · simpa only [commonInfo] using after.bounded entry member
  · intro entry member
    rcases List.mem_append.mp member with member | member
    · exact before.leftOrigins entry member
    · simpa only [contexts, commonMap, commonInfo] using after.leftOrigins entry member
  · intro entry member
    rcases List.mem_append.mp member with member | member
    · exact before.rightOrigins entry member
    · simpa only [contexts, commonMap, commonInfo] using after.rightOrigins entry member
  · have later := after.fields
    rw [← contexts, ← commonMap] at later
    simpa only [List.map_append] using appendArguments before.fields later

/-- Keep exactly the requested fields after joining independently observed
records. Selection preserves the literal request, including its support. -/
def FieldRecordWitness.select
    {lower : Relations n}
    (witness : FieldRecordWitness env U registry lower Γ left right type name requests)
    (selected : List (Nat × DataRequest (Profile n)))
    (included : List.Subset selected requests)
    (meaningful : ∃ entry ∈ selected, Profile.Nonempty entry.2.input) :
    FieldRecordWitness env U registry lower Γ left right type name selected := by
  refine {
    witness with
    meaningful := meaningful
    bounded := fun entry member => witness.bounded entry (included member)
    leftOrigins := fun entry member => witness.leftOrigins entry (included member)
    rightOrigins := fun entry member => witness.rightOrigins entry (included member)
    fields := ?_ }
  clear meaningful
  induction selected with
  | nil => exact .nil
  | cons entry selected ih =>
    exact .cons (witness.fields.map_member (included List.mem_cons_self))
      (ih (fun _ member => included (List.mem_cons_of_mem _ member)))

def FieldRecordRelation (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (lower : Relations n) (Γ : List VExpr) (left right type : VExpr)
    (name : Name) (requests : List (Nat × DataRequest (Profile n))) : Prop :=
  ∀ Δ ρ, FutureInsertion env U Γ Δ ρ →
    Nonempty (FieldRecordWitness env U registry lower Δ
      (left.lift' ρ) (right.lift' ρ) (type.lift' ρ) name
      (requests.map (fun entry => (entry.1, entry.2.rename ρ))))

theorem FieldRecordRelation.append
    (henv : env.Ordered) (laws : LowerTransport env U lower)
    (first : FieldRecordRelation env U registry lower Γ left right type name requests)
    (second : FieldRecordRelation env U registry lower Γ left right type name requests') :
    FieldRecordRelation env U registry lower Γ left right type name (requests ++ requests') := by
  intro Δ ρ future
  obtain ⟨before⟩ := first Δ ρ future
  obtain ⟨after⟩ := second Δ ρ future
  simpa only [List.map_append] using before.append henv laws after

/-- Reattach a chosen EXTERNAL family type code. The first source child's
natural type certificate can supply this code; the value witness never
chooses or hides a stronger family descriptor in its private world. -/
def FieldRecordWitness.attachType
    {lower : Relations n}
    (henv : env.Ordered)
    {family : FamilyData (Profile n)} (relevant : family.relevant = true)
    (witness : FieldRecordWitness env U registry lower Γ left right type name requests)
    (sameName : name = family.name)
    (code : FamilyRelation env U registry lower Γ type type family) :
    RecordWitness env U registry lower Γ left right type ⟨family, relevant, requests⟩ := by
  subst name
  exact {
    baseWF := witness.baseWF
    context := witness.context
    map := witness.map
    insertion := witness.insertion
    info := witness.info
    lookup := witness.lookup
    ctorDefinition := witness.ctorDefinition
    ctorNative := witness.ctorNative
    ctorQuotient := witness.ctorQuotient
    bounded := witness.bounded
    typeCode := code.mixed henv witness.insertion
    leftType := witness.leftType
    rightType := witness.rightType
    leftOrigins := witness.leftOrigins
    rightOrigins := witness.rightOrigins
    fields := witness.fields }

/-- Existing record witnesses with entirely different family descriptors
already suffice for the join once their family names agree. Their separate
family type codes remain available to the surrounding typed interpretation. -/
theorem RecordWitness.joinFields
    {lower : Relations n}
    (henv : env.Ordered) (laws : LowerTransport env U lower)
    {firstDemand secondDemand : RecordData (Profile n)}
    (first : RecordWitness env U registry lower Γ left right type firstDemand)
    (second : RecordWitness env U registry lower Γ left right type secondDemand)
    (sameName : firstDemand.family.name = secondDemand.family.name)
    (firstMeaningful : ∃ entry ∈ firstDemand.fields, Profile.Nonempty entry.2.input)
    (secondMeaningful : ∃ entry ∈ secondDemand.fields, Profile.Nonempty entry.2.input) :
    Nonempty (FieldRecordWitness env U registry lower Γ left right type firstDemand.family.name
      (firstDemand.fields ++ secondDemand.fields)) := by
  apply (first.fieldView firstMeaningful).append henv laws
  rw [sameName]
  exact second.fieldView secondMeaningful

end Lean4Lean.AnchoredSemantics.RankedData
