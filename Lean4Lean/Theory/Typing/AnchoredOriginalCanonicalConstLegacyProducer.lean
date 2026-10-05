import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalConstSharedReturn
import Lean4Lean.Theory.Typing.AnchoredSortableConstantRelocation
import Lean4Lean.Theory.Typing.AnchoredSortableScope
import Lean4Lean.Theory.Typing.AnchoredOriginalPrefixReplay

/-! Concrete closed constant input for the recipe application compiler.
Only the actual legacy function program is relocated. This does not assert
that arbitrary rich recipes at a constant have no local resource demands. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
open OriginalEndpointFactor EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- The original primitive and closed constDF premise are selected from the
actual retained function node, including its conversion prefix. -/
theorem canonicalConstSiteOfLegacy
    (owner : CanonicalCodeOwner env registry strata ownerName)
    (node : EndpointState owner.selected.origin.source U source (.const name levels) assigned)
    (query : SortableObs env U registry target locals σ (.const name levels) profile footprint) :
    ∃ packet : CanonicalConstSitePacket env U registry target strata name levels profile,
      packet.ownerName = ownerName ∧ HEq packet.owner owner ∧
      ∀ policy, packet.query.headDepth policy = query.headDepth policy := by
  let head := constantPrefix node
  obtain ⟨closed⟩ := EndpointRef.closedPrimitiveConstant head.reference rfl head.primitive
  obtain ⟨moved, depth⟩ := query.relocateConstant [] σ
  let origin : CanonicalConstOrigin env U registry strata name levels := {
    ownerName := ownerName
    owner := owner
    info := closed.info
    lookup := closed.lookup
    assignedLevels := closed.assignedLevels
    assignedWF := closed.assignedWF
    levelsWF := closed.levelsWF
    equivalent := closed.equivalent
    typeClosed := owner.selected.origin.ordered.closedC closed.lookup
    site := closed.site }
  let packet := CanonicalConstSitePacket.ofOrigin (target := target) origin σ (.legacy moved) (by
    intro index need member
    have impossible := query.scoped (show (VExpr.const name levels).Closed from trivial) index need member
    omega)
  refine ⟨packet, rfl, HEq.rfl, ?_⟩
  intro policy
  change (RichObs.legacy moved).headDepth policy = query.headDepth policy
  rw [RichObs.headDepth]
  exact depth policy

end Lean4Lean.AnchoredSource.Adapted
