import Lean4Lean.Theory.Typing.AnchoredLiteralRecordFields
import Lean4Lean.Theory.Typing.AnchoredDataProjection
import Lean4Lean.Theory.Typing.AnchoredRecordProjection

/-! A constructor's actual selected fields introduce a record observation.
The rule consumes finite original projection origins, not an inverse for
arbitrary composite constructor provenance. -/
namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

def ProjectionOrigin.future
    (henv : env.Ordered) (route : FutureInsertion env U Γ Δ ρ)
    (origin : ProjectionOrigin env U Γ info name index major assignedType domain) :
    ProjectionOrigin env U Δ info name index (major.lift' ρ)
      (assignedType.lift' ρ) (domain.lift' ρ) := by
  simpa only [← lift'_subst, subst_id] using
    origin.substitute henv (route.targetWF henv) (route.typedRenaming henv)

theorem recordOfFields
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {Γ : List VExpr} {left right type : VExpr} {demand : RecordData (Profile n)}
    {info : VProjectionInfo} (lookup : registry.projections demand.family.name = some info)
    (inert : CanonicalDataHead.HeadInert registry info.ctorName)
    (bounded : ∀ entry ∈ demand.fields, entry.1 < info.numFields)
    (code : FamilyRelation env U registry (relations env U registry n) Γ type type demand.family)
    (leftTyped : env.HasType U Γ left type) (rightTyped : env.HasType U Γ right type)
    (leftOrigins : ∀ entry ∈ demand.fields,
      Nonempty (ProjectionOrigin env U Γ info demand.family.name entry.1 left type entry.2.domain))
    (rightOrigins : ∀ entry ∈ demand.fields,
      Nonempty (ProjectionOrigin env U Γ info demand.family.name entry.1 right type entry.2.domain))
    (fields : Arguments env U (relations env U registry n) Γ (demand.fields.map (·.2))
      (demand.fields.map (fun entry => .proj demand.family.name entry.1 left))
      (demand.fields.map (fun entry => .proj demand.family.name entry.1 right))) :
    RecordRelation env U registry (relations env U registry n) Γ left right type demand := by
  intro Δ ρ future
  have familyRefl (family : FamilyData (Profile n)) : family.rename .refl = family := by
    unfold FamilyData.rename
    rw [show (fun e : VExpr => e.lift' .refl) = id from funext (fun _ => lift'_refl),
      show Profile.rename (n := n) .refl = id from funext Profile.rename_refl,
      FamilyData.map_id]
  refine ⟨{
    baseWF := future.targetWF henv
    context := Δ
    map := .refl
    insertion := .proof (.refl (future.targetWF henv))
    info := info
    lookup := lookup
    ctorDefinition := inert.definition
    ctorNative := inert.native
    ctorQuotient := inert.quotient
    bounded := ?_
    typeCode := ?_
    leftType := by simpa only [lift'_refl] using leftTyped.weak' henv future.weakening
    rightType := by simpa only [lift'_refl] using rightTyped.weak' henv future.weakening
    leftOrigins := ?_
    rightOrigins := ?_
    fields := ?_ }⟩
  · intro entry member
    change entry ∈ demand.fields.map (fun entry => (entry.1, entry.2.rename ρ)) at member
    obtain ⟨original, originalMember, equal⟩ := List.mem_map.mp member
    cases equal
    exact bounded original originalMember
  · change FamilyRelation env U registry (relations env U registry n) Δ
      ((type.lift' ρ).lift' .refl) ((type.lift' ρ).lift' .refl)
      ((demand.family.rename ρ).rename .refl)
    rw [familyRefl, lift'_refl]
    exact code.future henv future
  · intro entry member
    change entry ∈ demand.fields.map (fun entry => (entry.1, entry.2.rename ρ)) at member
    obtain ⟨original, originalMember, equal⟩ := List.mem_map.mp member
    cases equal
    obtain ⟨origin⟩ := leftOrigins original originalMember
    exact ⟨by simpa only [RecordData.rename, RecordData.map, FamilyData.map,
      DataRequest.rename, DataRequest.map, KeyData.map, lift'_refl] using origin.future henv future⟩
  · intro entry member
    change entry ∈ demand.fields.map (fun entry => (entry.1, entry.2.rename ρ)) at member
    obtain ⟨original, originalMember, equal⟩ := List.mem_map.mp member
    cases equal
    obtain ⟨origin⟩ := rightOrigins original originalMember
    exact ⟨by simpa only [RecordData.rename, RecordData.map, FamilyData.map,
      DataRequest.rename, DataRequest.map, KeyData.map, lift'_refl] using origin.future henv future⟩
  · have args := fields.future henv future
    simpa only [RecordData.rename, RecordData.map, FamilyData.map, List.map_map,
      Function.comp_def, DataRequest.rename_refl, lift'_refl, lift', DataRequest.rename,
      show Profile.rename (n := n) .refl = id from funext Profile.rename_refl,
      show (fun x : VExpr => x) = id from rfl, DataRequest.map_id]
      using args

private theorem Arguments.fromMembers
    {entries : List α} {requests : α → DataRequest (Profile n)} {left right : α → VExpr}
    (fields : ∀ entry ∈ entries,
      RequestAdmission env U lower Γ (requests entry) (left entry) (right entry)) :
    Arguments env U lower Γ (entries.map requests) (entries.map left) (entries.map right) := by
  induction entries with
  | nil => exact .nil
  | cons entry entries ih =>
    exact .cons (fields entry List.mem_cons_self)
      (ih fun entry member => fields entry (List.mem_cons_of_mem _ member))

theorem literalRecord
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ : List VExpr} (formed : OnCtx Γ (env.IsType U))
    {type : VExpr} {demand : RecordData (Profile n)}
    {info : VProjectionInfo} (lookup : registry.projections demand.family.name = some info)
    (inert : CanonicalDataHead.HeadInert registry info.ctorName)
    {levels levels' : List VLevel} {args args' : List VExpr}
    (bounded : ∀ entry ∈ demand.fields, entry.1 < info.numFields)
    (code : FamilyRelation env U registry (relations env U registry n) Γ type type demand.family)
    (leftTyped : env.HasType U Γ (mkApps (.const info.ctorName levels) args) type)
    (rightTyped : env.HasType U Γ (mkApps (.const info.ctorName levels') args') type)
    (leftOrigins : ∀ entry ∈ demand.fields, Nonempty (ProjectionOrigin env U Γ info
      demand.family.name entry.1 (mkApps (.const info.ctorName levels) args) type entry.2.domain))
    (rightOrigins : ∀ entry ∈ demand.fields, Nonempty (ProjectionOrigin env U Γ info
      demand.family.name entry.1 (mkApps (.const info.ctorName levels') args') type entry.2.domain))
    (fields : ∀ entry ∈ demand.fields, ∃ field field',
      args[info.nparams + entry.1]? = some field ∧ args'[info.nparams + entry.1]? = some field' ∧
      RequestAdmission env U (relations env U registry n) Γ entry.2 field field') :
    RecordRelation env U registry (relations env U registry n) Γ
      (mkApps (.const info.ctorName levels) args) (mkApps (.const info.ctorName levels') args')
      type demand := by
  apply recordOfFields henv lookup inert bounded code leftTyped rightTyped leftOrigins rightOrigins
  apply Arguments.fromMembers
  intro entry member
  obtain ⟨field, field', selected, selected', admitted⟩ := fields entry member
  obtain ⟨leftOrigin⟩ := leftOrigins entry member
  obtain ⟨rightOrigin⟩ := rightOrigins entry member
  exact admitted.literalProjection henv hscoped formed lookup leftOrigin rightOrigin selected selected'

end Lean4Lean.AnchoredSemantics.RankedData
