import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalConstOrigin
import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalConstSite
import Lean4Lean.Theory.Typing.AnchoredOriginalRichConstantRelocation
import Lean4Lean.Theory.Typing.AnchoredSortableScope

/-! Close an actual canonical constant occurrence using its retained closed
constDF premise. This is an explicit derivation in the same selected earlier
source, not a claim that the old occurrence had an empty source context.
Relocation preserves the exact finite query and every head policy. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
open OriginalEndpointFactor EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

mutual
theorem OriginalRecordSource.RichCert.constantScoped
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    (query : RichCert sourceEnv env U registry target node locals σ relevant profile footprint) :
    Footprint.Scoped 0 footprint := by
  match query with
  | .legacy child => exact child.scoped trivial
  | .observe child _ => exact child.constantScoped
  | .route _ child | .pad child | .down child | .map _ child | .support _ child | .select child _ =>
    exact child.constantScoped
  | .union left right => exact Footprint.Scoped.append left.constantScoped right.constantScoped
termination_by sizeOf query
decreasing_by all_goals simp_wf <;> omega

theorem OriginalRecordSource.RichObs.constantScoped
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    (query : RichObs sourceEnv env U registry target node locals σ profile footprint) :
    Footprint.Scoped 0 footprint := by
  match query with
  | .family .. | .constructor .. | .canonicalDelta .. => exact fun _ _ member => nomatch member
  | .legacy child => exact child.scoped trivial
  | .code child => exact child.constantScoped
  | .route _ child | .view child _ | .action child _ | .select child _ | .pad child | .unpad child =>
    exact child.constantScoped
  | .union left right => exact Footprint.Scoped.append left.constantScoped right.constantScoped
termination_by sizeOf query
decreasing_by all_goals simp_wf <;> omega
end

/-- The packet is computed from a primitive in the same selected canonical
source and the actual constant query, even when that query was under binders.
No source comparison or supplied semantic answer is used. -/
theorem canonicalConstSiteOfPrimitive
    (owner : CanonicalCodeOwner env registry strata ownerName)
    {node : EndpointState owner.selected.origin.source U source (.const name levels) assigned}
    (query : RichObs owner.selected.origin.source env U registry target node locals σ profile footprint)
    (reference : EndpointRef owner.selected.origin.source U primitiveSource (.const name levels) primitiveAssigned)
    (primitive : reference.Primitive) :
    ∃ packet : CanonicalConstSitePacket env U registry target strata name levels profile,
      packet.ownerName = ownerName ∧ HEq packet.owner owner ∧
      ∀ control, packet.chargeDepth control =
        headDepth owner.selected.ordinal
          (fun k => query.stratifiedDepth (strata.headOrdinal registry) k) control := by
  obtain ⟨closed⟩ := EndpointRef.closedPrimitiveConstant reference rfl primitive
  obtain ⟨moved, depth⟩ := query.relocateConstant (.ref closed.site) [] σ
  let packet : CanonicalConstSitePacket env U registry target strata name levels profile :=
    { ownerName := ownerName, owner := owner, info := closed.info, lookup := closed.lookup,
      assignedLevels := closed.assignedLevels, assignedWF := closed.assignedWF,
      levelsWF := closed.levelsWF, equivalent := closed.equivalent,
      typeClosed := owner.selected.origin.ordered.closedC closed.lookup,
      site := closed.site, realization := σ, footprint := footprint, query := moved,
      resources := by
        intro index need member
        have impossible := query.constantScoped index need member
        omega }
  refine ⟨packet, rfl, HEq.rfl, ?_⟩
  intro control
  change headDepth owner.selected.ordinal
    (fun k => moved.stratifiedDepth (strata.headOrdinal registry) k) control = _
  congr 1
  funext k
  exact depth _

/-- The primitive reference is selected from the actual input node. Even an
input node with conversion prefixes needs no supplied primitive or semantic
prefix interpretation: the finite query itself is relocated unchanged. -/
theorem canonicalConstSiteOfQuery
    (owner : CanonicalCodeOwner env registry strata ownerName)
    {node : EndpointState owner.selected.origin.source U source (.const name levels) assigned}
    (query : RichObs owner.selected.origin.source env U registry target node locals σ profile footprint) :
    ∃ packet : CanonicalConstSitePacket env U registry target strata name levels profile,
      packet.ownerName = ownerName ∧ HEq packet.owner owner ∧
      ∀ control, packet.chargeDepth control =
        headDepth owner.selected.ordinal
          (fun k => query.stratifiedDepth (strata.headOrdinal registry) k) control := by
  let head := constantPrefix node
  exact canonicalConstSiteOfPrimitive owner query head.reference head.primitive

end Lean4Lean.AnchoredSource.Adapted
