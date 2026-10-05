import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionOrigin
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionAtomRows

/-! Empty field inputs still retain their raw origin and complete request
support. They can join a meaningful record query without inventing an atom
origin or changing the coupled policy for wholly empty records.
-/
namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

/-- An empty input has no term observations, but its raw anchor, domain and
support remain literal. The projected equality comes from the actual origin. -/
theorem RequestAdmission.emptyFieldPair
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {info : VProjectionInfo} {name : Name} {index : Nat} {left right type : VExpr}
    {request : DataRequest (Profile n)}
    (origin : ProjectionOrigin env U target info name index left type request.domain)
    (equal : env.IsDefEq U target left right type)
    (seed : RequestAdmission env U (relations env U registry n) target request
      (.proj name index left) (.proj name index left))
    (empty : request.input = .empty) :
    RequestAdmission env U (relations env U registry n) target request
      (.proj name index left) (.proj name index right) := by
  refine ⟨seed.1, origin.congr equal, seed.2.2.1, seed.2.2.2.1, seed.2.2.2.2.1,
    seed.2.2.2.2.2.1, ?_⟩
  change Related env U registry target (.proj name index left) (.proj name index right)
    request.domain request.input request.support
  rw [empty]
  cases n <;> intro atom member <;> cases member

private theorem appendArguments
    (first : Arguments env U lower Γ requests left right)
    (second : Arguments env U lower Γ requests' left' right') :
    Arguments env U lower Γ (requests ++ requests') (left ++ left') (right ++ right') := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head ih

/-- Add an empty-input field to a record whose meaningful field is already
present. Raw origins are constructed independently of atom selection, and
the new field's exact type support remains in its admission. -/
theorem FieldRecordWitness.appendEmpty
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {info : VProjectionInfo} {name : Name} {index : Nat} {left right type : VExpr}
    {requests : List (Nat × DataRequest (Profile n))} {request : DataRequest (Profile n)}
    (henv : env.Ordered)
    (witness : FieldRecordWitness env U registry (relations env U registry n)
      target left right type name requests)
    (origin : ProjectionOrigin env U target info name index left type request.domain)
    (bound : index < info.numFields)
    (equal : env.IsDefEq U target left right type)
    (seed : RequestAdmission env U (relations env U registry n) target request
      (.proj name index left) (.proj name index left))
    (empty : request.input = .empty) :
    Nonempty (FieldRecordWitness env U registry (relations env U registry n)
      target left right type name (requests ++ [(index, request)])) := by
  have admission := RequestAdmission.emptyFieldPair origin equal seed empty
  have moved := admission_transport henv
    (show LowerTransport env U (relations env U registry n) from
      ⟨fun route code => route.code henv code, fun route term => route.term henv term⟩)
    witness.insertion admission
  obtain ⟨existing, present, _⟩ := witness.meaningful
  obtain ⟨existingOrigin⟩ := witness.leftOrigins existing present
  have sameInfo : info = witness.info :=
    henv.projections_unique origin.registered existingOrigin.registered
  let leftOrigin := origin.transport henv witness.insertion
  let rightOrigin := (origin.replaceMajor equal).transport henv witness.insertion
  refine ⟨{ witness with
    meaningful := ?_, bounded := ?_, leftOrigins := ?_, rightOrigins := ?_, fields := ?_ }⟩
  · obtain ⟨entry, member, nonempty⟩ := witness.meaningful
    exact ⟨entry, List.mem_append_left _ member, nonempty⟩
  · intro entry member
    rcases List.mem_append.mp member with member | member
    · exact witness.bounded entry member
    · cases List.mem_singleton.mp member
      simpa only [sameInfo] using bound
  · intro entry member
    rcases List.mem_append.mp member with member | member
    · exact witness.leftOrigins entry member
    · cases List.mem_singleton.mp member
      exact ⟨sameInfo ▸ leftOrigin⟩
  · intro entry member
    rcases List.mem_append.mp member with member | member
    · exact witness.rightOrigins entry member
    · cases List.mem_singleton.mp member
      exact ⟨sameInfo ▸ rightOrigin⟩
  · simpa only [List.map_append, List.map_cons, List.map_nil, lift'] using
      appendArguments witness.fields (Arguments.cons moved Arguments.nil)

end Lean4Lean.AnchoredSemantics.RankedData
