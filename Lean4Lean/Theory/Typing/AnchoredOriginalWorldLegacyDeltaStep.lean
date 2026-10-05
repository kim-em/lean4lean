import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCanonicalDeltaStep
import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalDeltaPrimitive

/-! The actual legacy delta observer enters the canonical computational branch.
Its unindexed finite children attach to the selected RHS and that same RHS's
computed assigned formation. No declaration-history original is transported. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalRecordSource OriginalEndpointFactor EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

namespace CanonicalDeltaPacket
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
  {strata : EquationStratification env} {name : Name} {levels : List VLevel}

/-- Read the assigned universes from the actual primitive constant proof.
The caller supplies neither an assigned certificate nor a universe bridge. -/
theorem primitiveStepWorld
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (below : sourceEnv ≤ env)
    (reference : EndpointRef sourceEnv U source (.const name levels) assigned)
    (primitive : reference.Primitive)
    (locals : List Nat) (σ τ : Subst) (available : Valuation)
    (controls : OriginalWorldControls strata sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U environment)
    (frontier : List (World strata.rules.length))
    (callerPaid : Sponsored frontier [originalCallWorld controls .fundamental (.ref reference) baseline])
    (source : P packet.selected.origin.source)
    (bodyAnnotation : WorldObsProvenance strata packet.body)
    (bodyPaid : Sponsored frontier bodyAnnotation.worlds)
    (bound : WithinAbove controls.cutoff controls.fuel packet.stratifiedDepth)
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.ref reference) baseline])) :
    ∃ result : RichComputationalValue sourceEnv env U registry target (.ref reference)
        locals σ τ available profile,
      Nonempty (ControlledStoredQuery controls frontier (.certificate result.certificate)) ∧
      Nonempty (ControlledStoredQuery controls frontier (.observation result.rightQuery.observation)) := by
  obtain ⟨assignedLevels, assignedWF, seedAssigned, assignedEq⟩ :=
    packet.primitiveAssigned below reference rfl primitive
  cases assignedEq
  exact packet.stepWorld henv hscoped formed assignedWF seedAssigned (.ref reference)
    locals σ τ available controls baseline frontier callerPaid source bodyAnnotation bodyPaid bound bank

section Legacy
variable {value : VDefVal} {seedLevels : List VLevel} {atom : Atom n} {support : Profile n}
  {typeRealization bodyRealization : Subst}
  (lookup : registry.definitions name = some value) (nameEq : value.name = name)
  (registered : DefinitionRegistered env value)
  (seedWF : ∀ level ∈ seedLevels, level.WF U) (seedLength : seedLevels.length = value.uvars)
  (levelsWF : ∀ level ∈ levels, level.WF U)
  (equivalent : List.Forall₂ (· ≈ ·) seedLevels levels)
  (bodyClosed : value.value.Closed) (typeClosed : value.type.Closed)
  (certificate : CodeCert env U registry target [] typeRealization
    (value.type.instL seedLevels) support [])
  (typed : (Profile.singleton atom).HasType support)
  (body : Obs env U registry target [] bodyRealization
    (value.value.instL seedLevels) (.singleton atom) [])

/-- The original endpoints are computed from the actual registered equation.
The legacy certificate is placed at the RHS's assigned formation, not at an
independently chosen type original. -/
noncomputable def ofLegacyDelta :
    CanonicalDeltaPacket env U registry target strata name levels (.singleton atom) where
  value := value
  lookup := lookup
  nameEq := nameEq
  registered := registered
  seedLevels := seedLevels
  seedWF := seedWF
  seedLength := seedLength
  levelsWF := levelsWF
  equivalent := equivalent
  bodyClosed := bodyClosed
  typeClosed := typeClosed
  support := support
  typeRealization := typeRealization
  bodyRealization := bodyRealization
  certificate := .legacy (.ofCode certificate certificate.formed)
  typed := typed
  body := .legacy (.legacy body)

include lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed
  certificate typed body in
/-- The conversion preserves the actual masked input depth exactly. -/
theorem ofLegacyDelta_stratifiedDepth (locals : List Nat) (σ : Subst) :
    (ofLegacyDelta (strata := strata) lookup nameEq registered seedWF seedLength levelsWF
      equivalent bodyClosed typeClosed certificate typed body).stratifiedDepth =
    fun control => (Obs.delta (locals := locals) (σ := σ) lookup nameEq registered
      seedWF seedLength levelsWF equivalent bodyClosed typeClosed certificate typed body).headDepth
        (stratifiedHeadPolicy (strata.headOrdinal registry) control) := by
  funext control
  simp only [stratifiedDepth, stratifiedChildren, ofLegacyDelta, selected,
    RichObs.stratifiedDepth, RichCert.stratifiedDepth, RichObs.headDepth, RichCert.headDepth,
    SortableObs.headDepth, SortableCert.headDepth, Obs.headDepth,
    stratifiedHeadPolicy, strata.headOrdinal_definition lookup registered.2,
    EquationStratifiedFuel.headDepth]

include lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed
  certificate typed body in
/-- This is the legacy delta F branch at an actual primitive original. The
incoming annotation's arbitrary closed call sites are not used as canonical
sites: only its SAME finite body annotation survives. Canonical controls and
empty frames are computed by `stepWorld`. -/
theorem legacyPrimitiveStepWorld
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (below : sourceEnv ≤ env)
    (reference : EndpointRef sourceEnv U source (.const name levels) assigned)
    (primitive : reference.Primitive)
    (locals : List Nat) (σ τ : Subst) (available : Valuation)
    (controls : OriginalWorldControls strata sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U environment)
    (frontier : List (World strata.rules.length))
    (callerPaid : Sponsored frontier [originalCallWorld controls .fundamental (.ref reference) baseline])
    (source : P (strata.select registered.2).origin.source)
    (certificateAnnotation : WorldLegacyCertProvenance strata certificate)
    (bodyAnnotation : WorldLegacyObsProvenance strata body)
    (origin : EquationHeaderOrigin env value.toDefEq)
    (typeSite : WorldQuerySite (registry := registry) (target := target) strata
      (.ref (.left (EquationHeaderOrigin.instantiatedType origin seedWF))) [] typeRealization)
    (bodySite : WorldQuerySite (registry := registry) (target := target) strata
      (.ref (.left (EquationHeaderOrigin.instantiatedRhs origin seedWF))) [] bodyRealization)
    (paid : Sponsored frontier
      (WorldLegacyObsProvenance.delta (locals := locals) (σ := σ)
        lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed
        certificate typed body certificateAnnotation bodyAnnotation origin typeSite bodySite).worlds)
    (bound : WithinAbove controls.cutoff controls.fuel
      (fun control => (Obs.delta (locals := locals) (σ := σ) lookup nameEq registered
        seedWF seedLength levelsWF equivalent bodyClosed typeClosed certificate typed body).headDepth
          (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.ref reference) baseline])) :
    ∃ result : RichComputationalValue sourceEnv env U registry target (.ref reference)
        locals σ τ available (.singleton atom),
      Nonempty (ControlledStoredQuery controls frontier (.certificate result.certificate)) ∧
      Nonempty (ControlledStoredQuery controls frontier (.observation result.rightQuery.observation)) := by
  let packet := ofLegacyDelta (strata := strata) lookup nameEq registered seedWF seedLength
    levelsWF equivalent bodyClosed typeClosed certificate typed body
  let bodyReady : WorldObsProvenance strata packet.body :=
    .legacy _ (.legacy _ bodyAnnotation)
  have bodyPaid : Sponsored frontier bodyReady.worlds := by
    intro world member
    apply paid world
    change world ∈ typeSite.worlds ++ bodySite.worlds ++ certificateAnnotation.worlds ++ bodyAnnotation.worlds
    exact List.mem_append_right _ member
  have packetBound : WithinAbove controls.cutoff controls.fuel packet.stratifiedDepth := by
    simpa only [packet, ofLegacyDelta_stratifiedDepth lookup nameEq registered seedWF seedLength
      levelsWF equivalent bodyClosed typeClosed certificate typed body locals σ] using bound
  exact packet.primitiveStepWorld henv hscoped formed below reference primitive locals σ τ available
    controls baseline frontier callerPaid source bodyReady bodyPaid packetBound bank

end Legacy
end CanonicalDeltaPacket
end Lean4Lean.AnchoredSource.Adapted
