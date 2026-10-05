import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalConstValuePruning
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceLevels

/-! A level-aligned constant body is compared by an actual closed original
universe equality, not by pretending its two displayed expressions coincide.
The equality is constructed inside the retained canonical owner's source. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
open OriginalEndpointFactor EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

namespace CanonicalConstSitePacket

structure LevelBridge
    (packet : CanonicalConstSitePacket env U registry target strata name levels (Profile.fn key output))
    (nextLevels : List VLevel) where
  original : Derivation packet.owner.selected.origin.source U [] (.const name levels)
    (.const name nextLevels) (packet.info.type.instL packet.assignedLevels)
  query : RichObs packet.owner.selected.origin.source env U registry target (.ref (.left original))
    [] packet.realization (Profile.fn key output) []
  depth : ∀ policy, query.headDepth policy ≤ packet.query.headDepth policy

/-- Ordered strengthening and reification are applied only to the actual
closed site and its level conversion. There is no arbitrary typing supplier
and no purported bound by the old site's natural-number proof size. -/
theorem levelBridge
    (packet : CanonicalConstSitePacket env U registry target strata name levels (Profile.fn key output))
    (equal : EqUpToLevels U (.const name levels) (.const name nextLevels)) :
    Nonempty (packet.LevelBridge nextLevels) := by
  have raw := (EndpointState.ref packet.site).sound.defeq
  have comparison := raw.eqUpToLevels packet.owner.selected.origin.ordered (by trivial) equal
  obtain ⟨original⟩ := Derivation.reify
    (comparison.strong packet.owner.selected.origin.ordered (by trivial))
  obtain ⟨query, depth⟩ := packet.query.pruneConstantFunction (.ref (.left original)) [] packet.realization
  exact ⟨⟨original, query, depth⟩⟩

/-- The exact right endpoint becomes the next closed canonical site. Its
owner and original assigned-level instance are unchanged. -/
def LevelBridge.origin
    {packet : CanonicalConstSitePacket env U registry target strata name levels (Profile.fn key output)}
    (bridge : packet.LevelBridge nextLevels)
    (equal : EqUpToLevels U (.const name levels) (.const name nextLevels)) :
    CanonicalConstOrigin env U registry strata name nextLevels where
  ownerName := packet.ownerName
  owner := packet.owner
  info := packet.info
  lookup := packet.lookup
  assignedLevels := packet.assignedLevels
  assignedWF := packet.assignedWF
  levelsWF := by cases equal with | const _ right _ => exact right
  equivalent := by
    cases equal with
    | const _ _ comparison =>
      exact Lean4Lean.List.Forall₂.trans (T := (· ≈ ·))
        (fun _ _ _ first second => first.trans second) packet.equivalent comparison
  typeClosed := packet.typeClosed
  site := .right bridge.original

/-- Assemble only from the actual selected right query of the equality
call. This definition carries no semantic comparison premise. -/
noncomputable def LevelBridge.packet
    {realization : Subst} {footprint : Footprint}
    {packet : CanonicalConstSitePacket env U registry target strata name levels (Profile.fn key output)}
    (bridge : packet.LevelBridge nextLevels)
    (equal : EqUpToLevels U (.const name levels) (.const name nextLevels))
    (query : RichObs packet.owner.selected.origin.source env U registry target (.ref (.right bridge.original))
      [] realization profile footprint)
    (resources : footprint.Available (fun _ => [])) :
    CanonicalConstSitePacket env U registry target strata name nextLevels profile :=
  CanonicalConstSitePacket.ofOrigin (bridge.origin equal) realization query resources

@[simp] theorem LevelBridge.packet_owner
    {realization : Subst} {footprint : Footprint}
    {packet : CanonicalConstSitePacket env U registry target strata name levels (Profile.fn key output)}
    (bridge : packet.LevelBridge nextLevels)
    (equal : EqUpToLevels U (.const name levels) (.const name nextLevels))
    (query : RichObs packet.owner.selected.origin.source env U registry target (.ref (.right bridge.original))
      [] realization profile footprint)
    (resources : footprint.Available (fun _ => [])) :
    (bridge.packet equal query resources).owner = packet.owner := rfl

end CanonicalConstSitePacket
end Lean4Lean.AnchoredSource.Adapted
