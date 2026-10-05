import Lean4Lean.Theory.Typing.EquationHeaderDerivation
import Lean4Lean.Theory.Typing.AnchoredOriginalRichNativeDepth

/-! A canonical delta payload, independent of the original constant endpoint
being queried. It retains actual pre-equation original type/body proofs
selected once from the target's finite equation stratification.
`WorldCanonicalDeltaReturn` constructs its shared `RichObs.canonicalDelta`
observer and returns the actual body answer's assigned certificate through
`RichCert.recipe`. Declaration-history delta sources remain distinct. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- All proof-bearing children belong to the one selected source. No caller
source inclusion, fabricated formation endpoint, or semantic callback occurs. -/
structure CanonicalDeltaPacket (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (strata : EquationStratification env)
    (name : Name) (levels : List VLevel) (profile : Profile n) where
  value : VDefVal
  lookup : registry.definitions name = some value
  nameEq : value.name = name
  registered : DefinitionRegistered env value
  seedLevels : List VLevel
  seedWF : ∀ level ∈ seedLevels, level.WF U
  seedLength : seedLevels.length = value.uvars
  levelsWF : ∀ level ∈ levels, level.WF U
  equivalent : List.Forall₂ (· ≈ ·) seedLevels levels
  bodyClosed : value.value.Closed
  typeClosed : value.type.Closed
  support : Profile n
  typeRealization : Subst
  bodyRealization : Subst
  certificate : RichCert (strata.select registered.2).origin.source env U registry target
    (EndpointState.ref (.left (EquationHeaderOrigin.instantiatedRhs
      (strata.select registered.2).origin seedWF))).typeFormation.node
    [] typeRealization true support []
  typed : profile.HasType support
  body : RichObs (strata.select registered.2).origin.source env U registry target
    (.ref (.left (EquationHeaderOrigin.instantiatedRhs (strata.select registered.2).origin seedWF)))
    [] bodyRealization profile []

namespace CanonicalDeltaPacket
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
  {strata : EquationStratification env} {name : Name} {levels : List VLevel}
  {profile : Profile n}

noncomputable def selected (packet : CanonicalDeltaPacket env U registry target strata name levels profile) :
    strata.Selected packet.value.toDefEq := strata.select packet.registered.2

theorem source_ordinal_lt
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (previous : strata.Selected rule)
    (present : packet.selected.origin.source.defeqs rule) :
    previous.ordinal < packet.selected.ordinal :=
  packet.selected.earlier_ordinal previous present

noncomputable def nativeDepth
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (current : Name → Bool) : Nat :=
  max (packet.body.nativeDepth current) (packet.certificate.nativeDepth current) +
    if current name then 1 else 0

/-- Removing this actual named query head gives a strict query-fuel step,
independently of the size or constants of its original checking source. -/
theorem children_lt
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (current : Name → Bool) (active : current name = true) :
    max (packet.body.nativeDepth current) (packet.certificate.nativeDepth current) <
      packet.nativeDepth current := by
  simp [nativeDepth, active]

end CanonicalDeltaPacket

/-- A caller-indexed packet view. Its original caller node is retained
verbatim; all borrowed original roots are in the canonical packet. -/
structure CanonicalDeltaAt (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (strata : EquationStratification env)
    (node : EndpointState sourceEnv U source (.const name levels) assigned)
    (locals : List Nat) (σ : Subst) (profile : Profile n) where
  packet : CanonicalDeltaPacket env U registry target strata name levels profile

/-- Same-head expression R can copy the identical payload to another actual
original endpoint. No header≤caller premise or type-proof relabeling is needed. -/
def CanonicalDeltaAt.reindex
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    (query : CanonicalDeltaAt sourceEnv env U registry target strata node locals σ profile)
    (destination : EndpointState destinationEnv U destinationSource (.const name levels) destinationAssigned)
    (destinationLocals : List Nat) (destinationSubst : Subst) :
    CanonicalDeltaAt destinationEnv env U registry target strata destination
      destinationLocals destinationSubst profile := ⟨query.packet⟩

@[simp] theorem CanonicalDeltaAt.reindex_packet
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    (query : CanonicalDeltaAt sourceEnv env U registry target strata node locals σ profile)
    (destination : EndpointState destinationEnv U destinationSource (.const name levels) destinationAssigned)
    (destinationLocals : List Nat) (destinationSubst : Subst) :
    (query.reindex destination destinationLocals destinationSubst).packet = query.packet := rfl

end Lean4Lean.AnchoredSource.Adapted
