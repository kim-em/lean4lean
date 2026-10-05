import Lean4Lean.Theory.Typing.AnchoredDataProjection
import Lean4Lean.Theory.Typing.AnchoredProjectionOriginTransport
import Lean4Lean.Theory.Typing.AnchoredRecordProjection

/-! Primitive projection provenance retracts through the actual private
proof/context world. The retraction substitutes the stored inhabitants of
inserted proof binders; it does not strengthen a semantic relation. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

namespace RankedData

theorem ProjectionOrigin.pullbackMixed
    (henv : env.Ordered) (route : MixedInsertion env U Γ Δ ρ)
    (origin : ProjectionOrigin env U Δ info name index (major.lift' ρ)
      (assignedType.lift' ρ) (domain.lift' ρ)) :
    Nonempty (ProjectionOrigin env U Γ info name index major assignedType domain) := by
  induction route generalizing major assignedType domain with
  | proof insertion =>
    obtain ⟨embedding, map⟩ := insertion.toEmbedding henv
    have result := origin.substitute henv embedding.baseWF embedding.typed
    exact ⟨by simpa only [← map, embedding.leftInv] using result⟩
  | context chain =>
    have result := origin.transport henv (.context (chain.symm henv))
    exact ⟨by simpa only [lift'_refl] using result⟩
  | comp _ _ first second =>
    obtain ⟨middle⟩ := second (by simpa only [lift'_comp] using origin)
    exact first middle

/-- Both finite sets of primitive guards are available at the base world,
with exactly the requested domains and the witness's actual registration. -/
theorem RecordWitness.originsAtBase
    {lower : Relations n} {demand : RecordData (Profile n)}
    (henv : env.Ordered)
    (witness : RecordWitness env U registry lower Γ left right type demand)
    (entry : Nat × DataRequest (Profile n)) (member : entry ∈ demand.fields) :
    Nonempty (ProjectionOrigin env U Γ witness.info demand.family.name entry.1
      left type entry.2.domain) ∧
    Nonempty (ProjectionOrigin env U Γ witness.info demand.family.name entry.1
      right type entry.2.domain) := by
  obtain ⟨leftOrigin⟩ := witness.leftOrigins entry member
  obtain ⟨rightOrigin⟩ := witness.rightOrigins entry member
  exact ⟨leftOrigin.pullbackMixed henv witness.insertion,
    rightOrigin.pullbackMixed henv witness.insertion⟩

/-- The registry lookup identifies the private witness's descriptor with the
actual requested descriptor. Empty field sets require no primitive guard. -/
theorem RecordRelation.originsAtBase
    {lower : Relations n} {demand : RecordData (Profile n)}
    (henv : env.Ordered) (formed : OnCtx Γ (env.IsType U))
    (related : RecordRelation env U registry lower Γ left right type demand)
    (lookup : registry.projections demand.family.name = some info)
    (entry : Nat × DataRequest (Profile n)) (member : entry ∈ demand.fields) :
    Nonempty (ProjectionOrigin env U Γ info demand.family.name entry.1
      left type entry.2.domain) ∧
    Nonempty (ProjectionOrigin env U Γ info demand.family.name entry.1
      right type entry.2.domain) := by
  obtain ⟨witness⟩ := related Γ .refl (.refl formed)
  have rename : demand.rename .refl = demand := by
    unfold RecordData.rename
    rw [show (fun e : VExpr => e.lift' .refl) = id from funext (fun _ => lift'_refl),
      show Profile.rename (n := n) .refl = id from funext Profile.rename_refl,
      RecordData.map_id]
  simp only [lift'_refl, rename] at witness
  have same : witness.info = info := Option.some.inj (witness.lookup.symm.trans lookup)
  simpa only [same] using witness.originsAtBase henv entry member

end RankedData

/-- A record observation provides its original raw field guards even when
its semantic witness uses an inhabited private proof context. -/
theorem Related.recordOriginsAtBase
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx Γ (env.IsType U))
    (related : Related env U registry Γ left right type
      (Profile.singleton (n := n + 1) (.record demand)) support)
    (lookup : registry.projections demand.family.name = some info)
    (entry : Nat × DataRequest (Profile n)) (member : entry ∈ demand.fields) :
    Nonempty (RankedData.ProjectionOrigin env U Γ info demand.family.name entry.1
      left type entry.2.domain) ∧
    Nonempty (RankedData.ProjectionOrigin env U Γ info demand.family.name entry.1
      right type entry.2.domain) :=
  (related.recordRelation henv hscoped formed).originsAtBase henv formed lookup entry member

end Lean4Lean.AnchoredSemantics
