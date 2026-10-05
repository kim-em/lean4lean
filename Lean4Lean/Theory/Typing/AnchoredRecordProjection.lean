import Lean4Lean.Theory.Typing.AnchoredDataAbsorption
import Lean4Lean.Theory.Typing.AnchoredMixedTransport

/-! A primitive projection consumes one actual finite record request. Its
domain, value demand and support all descend as literal lifts from the
record's private world; no equality of unrequested fields is needed. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

namespace RankedData

theorem Arguments.map_member
    {entries : List α} {requests : α → DataRequest (Profile n)}
    {left right : α → VExpr}
    (arguments : Arguments env U lower Γ (entries.map requests)
      (entries.map left) (entries.map right))
    (member : entry ∈ entries) :
    RequestAdmission env U lower Γ (requests entry) (left entry) (right entry) := by
  induction entries with
  | nil => cases member
  | cons head tail ih =>
    cases arguments with
    | cons admitted rest =>
      rcases List.mem_cons.mp member with rfl | member
      · exact admitted
      · exact ih rest member

theorem RecordWitness.project
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {Γ : List VExpr} {left right type : VExpr}
    {demand : RecordData (Profile n)} {index : Nat} {request : DataRequest (Profile n)}
    (witness : RecordWitness env U registry (relations env U registry n) Γ
      left right type demand)
    (member : (index, request) ∈ demand.fields) :
    Related env U registry Γ (.proj demand.family.name index left)
      (.proj demand.family.name index right) request.domain request.input request.support := by
  have admitted := witness.fields.map_member member
  apply witness.insertion.termBack henv
  exact admitted.2.2.2.2.2.2

theorem RecordRelation.project
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {Γ : List VExpr} (formed : OnCtx Γ (env.IsType U))
    {left right type : VExpr} {demand : RecordData (Profile n)}
    {index : Nat} {request : DataRequest (Profile n)}
    (related : RecordRelation env U registry (relations env U registry n) Γ
      left right type demand)
    (member : (index, request) ∈ demand.fields) :
    Related env U registry Γ (.proj demand.family.name index left)
      (.proj demand.family.name index right) request.domain request.input request.support := by
  obtain ⟨witness⟩ := related Γ .refl (.refl formed)
  have rename : demand.rename .refl = demand := by
    unfold RecordData.rename
    rw [show (fun e : VExpr => e.lift' .refl) = id from funext (fun _ => lift'_refl),
      show Profile.rename (n := n) .refl = id from funext Profile.rename_refl,
      RecordData.map_id]
  simp only [lift'_refl, rename] at witness
  exact witness.project henv member

end RankedData

theorem Related.projectRecord
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ : List VExpr} (formed : OnCtx Γ (env.IsType U))
    {left right type : VExpr} {demand : RecordData (Profile n)}
    {support : Profile (n + 1)} {index : Nat} {request : DataRequest (Profile n)}
    (related : Related env U registry Γ left right type
      (Profile.singleton (n := n + 1) (.record demand)) support)
    (member : (index, request) ∈ demand.fields) :
    Related env U registry Γ (.proj demand.family.name index left)
      (.proj demand.family.name index right) request.domain request.input request.support :=
  (related.recordRelation henv hscoped formed).project henv formed member

end Lean4Lean.AnchoredSemantics
